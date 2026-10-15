use std::collections::HashMap;

use rayon::prelude::*;

use crate::{
    Context, Edge, GraphCsr, PartitionTask, SolverResult, TaskExecResult, add_edge_to_graph,
    build_phase1_graph, checked_edge_weight, compact_log_line, csr_from_graph, csr_graphs_equal,
    favut, get_weight_in_csr, graph_from_csr, res_num, runtime_println,
    save_block_relaxed_checkpoint, should_update_progress, shutdown_requested,
};

#[derive(Debug)]
struct EvalScratch {
    global_tag: i32,
    weight_cache: Vec<i32>,
    cache_tags: Vec<i32>,
    phase2_candidates: Vec<i32>,
}

impl EvalScratch {
    fn new(num_vertices: usize) -> Self {
        Self {
            global_tag: 0,
            weight_cache: vec![0; num_vertices],
            cache_tags: vec![0; num_vertices],
            phase2_candidates: vec![0; num_vertices],
        }
    }

    #[inline(always)]
    fn bump_global_tag(&mut self) {
        self.global_tag += 1;
        if self.global_tag == i32::MAX {
            self.cache_tags.fill(0);
            self.global_tag = 1;
        }
    }
}

#[derive(Debug, Default)]
struct BlockOverlay {
    by_vertex: HashMap<usize, Vec<Edge>>,
}

impl BlockOverlay {
    fn add_edge(&mut self, u: usize, v: usize, weight: i32) {
        self.by_vertex.entry(u).or_default().push(Edge {
            target: v as i32,
            weight,
        });
        self.by_vertex.entry(v).or_default().push(Edge {
            target: u as i32,
            weight,
        });
    }

    fn get_weight(&self, u: usize, v: usize) -> i32 {
        let Some(edges) = self.by_vertex.get(&u) else {
            return 0;
        };
        edges
            .binary_search_by_key(&(v as i32), |edge| edge.target)
            .ok()
            .map_or(0, |idx| edges[idx].weight)
    }

    fn for_each_neighbor(&self, u: usize, mut visitor: impl FnMut(usize, i32)) {
        if let Some(edges) = self.by_vertex.get(&u) {
            for edge in edges {
                visitor(edge.target as usize, edge.weight);
            }
        }
    }
}

trait GraphRead {
    fn get_weight(&self, u: usize, v: usize) -> i32;

    fn for_each_neighbor(&self, u: usize, visitor: impl FnMut(usize, i32));
}

impl GraphRead for GraphCsr {
    fn get_weight(&self, u: usize, v: usize) -> i32 {
        get_weight_in_csr(self, u, v)
    }

    fn for_each_neighbor(&self, u: usize, mut visitor: impl FnMut(usize, i32)) {
        for edge in &self.edges[self.offsets[u]..self.offsets[u + 1]] {
            visitor(edge.target as usize, edge.weight);
        }
    }
}

struct BlockGraph<'a> {
    phase1: &'a GraphCsr,
    snapshot: &'a GraphCsr,
    overlay: &'a BlockOverlay,
    block_start: usize,
    block_end: usize,
}

impl BlockGraph<'_> {
    fn target_in_block(&self, u: usize, v: usize) -> bool {
        let target = u.max(v);
        target >= self.block_start && target < self.block_end
    }
}

impl GraphRead for BlockGraph<'_> {
    fn get_weight(&self, u: usize, v: usize) -> i32 {
        if self.target_in_block(u, v) {
            let overlay_weight = self.overlay.get_weight(u, v);
            if overlay_weight != 0 {
                return overlay_weight;
            }
            return self.phase1.get_weight(u, v);
        }
        self.snapshot.get_weight(u, v)
    }

    fn for_each_neighbor(&self, u: usize, mut visitor: impl FnMut(usize, i32)) {
        self.snapshot.for_each_neighbor(u, |v, weight| {
            if !self.target_in_block(u, v) {
                visitor(v, weight);
            }
        });
        self.phase1.for_each_neighbor(u, |v, weight| {
            if self.target_in_block(u, v) {
                visitor(v, weight);
            }
        });
        self.overlay
            .for_each_neighbor(u, |v, weight| visitor(v, weight));
    }
}

#[derive(Debug)]
struct BlockResult {
    edges: Vec<(usize, usize, i32)>,
    total_edges: i64,
    special_edges: i64,
}

fn collect_phase2_candidates(ctx: &Context, scratch: &mut EvalScratch, t: usize) -> usize {
    let mut candidate_count = 0usize;
    let des_t = ctx.descents[t];
    if ctx.mask_offsets.is_empty() {
        for u in 0..t {
            let des_u = ctx.descents[u];
            if ctx.length_parity[u] != ctx.length_parity[t]
                && (des_t & des_u) == des_t
                && des_t != des_u
            {
                scratch.phase2_candidates[candidate_count] = u as i32;
                candidate_count += 1;
            }
        }
        return candidate_count;
    }

    let mask_count = ctx.full_desc_mask as usize + 1;
    let parity_base = (usize::from(ctx.length_parity[t] ^ 1)) * mask_count;
    let complement = ctx.full_desc_mask ^ des_t;
    let mut extra = complement;

    while extra != 0 {
        let super_mask = des_t | extra;
        let bucket = parity_base + super_mask as usize;
        let start = ctx.mask_offsets[bucket] as usize;
        let end = ctx.mask_offsets[bucket + 1] as usize;
        for &u in &ctx.mask_vertices[start..end] {
            if u as usize >= t {
                break;
            }
            scratch.phase2_candidates[candidate_count] = u;
            candidate_count += 1;
        }

        extra = (extra - 1) & complement;
    }

    if candidate_count > 1 {
        scratch.phase2_candidates[..candidate_count].sort_unstable();
    }

    candidate_count
}

fn evaluate_phase2_candidate<G: GraphRead>(
    ctx: &Context,
    scratch: &mut EvalScratch,
    graph: &G,
    u: usize,
    t: usize,
    j: usize,
) -> i32 {
    if ctx.length_parity[u] == ctx.length_parity[t] {
        return 0;
    }

    let des_t = ctx.descents[t];
    let des_u = ctx.descents[u];
    if (des_t & des_u) != des_t || des_t == des_u {
        return 0;
    }

    let i = res_num(ctx, u, t);
    if i == 0 || i >= j {
        return 0;
    }

    let i_bit = i - 1;
    let j_bit = j - 1;
    let i_mask = 1u32 << i_bit;
    let j_mask = 1u32 << j_bit;
    let in_diff = (des_u & i_mask) != 0 && (des_t & i_mask) == 0;

    let mut fu = u;
    let mut ft = t;
    if !in_diff {
        if let Some((new_fu, new_ft)) = favut(ctx, u, t, i) {
            fu = new_fu;
            ft = new_ft;
        }
    }

    let des_fu = ctx.descents[fu];
    let des_ft = ctx.descents[ft];
    let in_diff_f = (des_fu & i_mask) != 0 && (des_ft & i_mask) == 0;
    if !in_diff_f {
        return 0;
    }

    let mut weight = 0i64;
    if ft < t {
        weight = i64::from(graph.get_weight(ft, fu));
    } else {
        scratch.bump_global_tag();

        graph.for_each_neighbor(fu, |target, edge_weight| {
            scratch.weight_cache[target] = edge_weight;
            scratch.cache_tags[target] = scratch.global_tag;
        });
        scratch.weight_cache[fu] = 1;
        scratch.cache_tags[fu] = scratch.global_tag;

        let val_v = ctx.table[ctx.table_index(ft, j_bit)];
        let v = val_v.abs() - 1;
        if v >= 0 {
            let v = v as usize;
            let des_v = ctx.descents[v];
            let i_in_des_v = (des_v & i_mask) != 0;

            if !i_in_des_v {
                let mut sumji = 0i64;
                let mut sumij = 0i64;
                graph.for_each_neighbor(v, |x, w_vx| {
                    let w_vx = i64::from(w_vx);
                    let w_xfu = if scratch.cache_tags[x] == scratch.global_tag {
                        i64::from(scratch.weight_cache[x])
                    } else {
                        0
                    };
                    if w_xfu != 0 {
                        let des_x = ctx.descents[x];
                        if x != ft && (des_x & j_mask) != 0 && (des_x & i_mask) == 0 {
                            sumji += w_vx * w_xfu;
                        }
                        if (des_x & i_mask) != 0 && (des_x & j_mask) == 0 {
                            sumij += w_vx * w_xfu;
                        }
                    }
                });
                weight = sumij - sumji;
            } else if i == j - 1 {
                let val_w = ctx.table[ctx.table_index(v, i_bit)];
                if val_w > 0 {
                    let w_idx = (val_w - 1) as usize;
                    let mut sumji = 0i64;
                    graph.for_each_neighbor(w_idx, |x, w_wx| {
                        let w_wx = i64::from(w_wx);
                        let des_x = ctx.descents[x];
                        let i_idx = (des_x & i_mask) != 0;
                        let j_idx = (des_x & j_mask) != 0;
                        let mut y = None;

                        if x != v && i_idx && !j_idx {
                            let t_jx = ctx.table[ctx.table_index(x, j_bit)];
                            if t_jx.abs() - 1 > x as i32 {
                                let tx = (t_jx.abs() - 1) as usize;
                                if (ctx.descents[tx] & i_mask) == 0 {
                                    y = Some(tx);
                                }
                            } else {
                                let t_ix = ctx.table[ctx.table_index(x, i_bit)];
                                if t_ix.abs() - 1 < x as i32 && t_ix > 0 {
                                    let tix = (t_ix.abs() - 1) as usize;
                                    if (ctx.descents[tix] & j_mask) != 0 {
                                        y = Some(tix);
                                    }
                                }
                            }
                        }

                        if j_idx && !i_idx {
                            let t_ix = ctx.table[ctx.table_index(x, i_bit)];
                            if t_ix.abs() - 1 > x as i32 {
                                let tix = (t_ix.abs() - 1) as usize;
                                if (ctx.descents[tix] & j_mask) == 0 {
                                    y = Some(tix);
                                }
                            } else {
                                let t_jx = ctx.table[ctx.table_index(x, j_bit)];
                                if t_jx.abs() - 1 < x as i32 && t_jx > 0 {
                                    let tjx = (t_jx.abs() - 1) as usize;
                                    if (ctx.descents[tjx] & i_mask) != 0 {
                                        y = Some(tjx);
                                    }
                                }
                            }
                        }

                        if let Some(y_idx) = y {
                            let w_yfu = if scratch.cache_tags[y_idx] == scratch.global_tag {
                                i64::from(scratch.weight_cache[y_idx])
                            } else {
                                0
                            };
                            if w_yfu != 0 {
                                sumji += w_wx * w_yfu;
                            }
                        }
                    });
                    weight = sumji;
                }
            }
        }
    }

    checked_edge_weight(weight)
}

fn solve_block(
    ctx: &Context,
    phase1: &GraphCsr,
    snapshot: &GraphCsr,
    block_start: usize,
    block_end: usize,
) -> BlockResult {
    let mut scratch = EvalScratch::new(ctx.num_tableaux);
    let mut overlay = BlockOverlay::default();
    let mut edges = Vec::new();
    let mut total_edges = 0i64;
    let mut special_edges = 0i64;

    for t in block_start..block_end {
        let j = ctx.max_positive_descent.get(t).copied().unwrap_or(0) as usize;
        if j == 0 {
            continue;
        }
        let candidate_count = collect_phase2_candidates(ctx, &mut scratch, t);

        for idx in 0..candidate_count {
            let u = scratch.phase2_candidates[idx] as usize;
            let weight = {
                let graph = BlockGraph {
                    phase1,
                    snapshot,
                    overlay: &overlay,
                    block_start,
                    block_end,
                };
                evaluate_phase2_candidate(ctx, &mut scratch, &graph, u, t, j)
            };
            if weight > 0 {
                overlay.add_edge(u, t, weight);
                edges.push((u, t, weight));
                total_edges += 1;
                if weight != 1 {
                    special_edges += 1;
                }
            }
        }
    }

    BlockResult {
        edges,
        total_edges,
        special_edges,
    }
}

fn compute_block_ranges(num_tableaux: usize, block_size: usize) -> Vec<(usize, usize)> {
    if num_tableaux <= 1 {
        return Vec::new();
    }

    let mut ranges = Vec::new();
    let mut start = 1usize;
    while start < num_tableaux {
        let end = (start + block_size).min(num_tableaux);
        ranges.push((start, end));
        start = end;
    }
    ranges
}

fn block_worker_count(ctx: &Context) -> usize {
    if !ctx.runtime.config.async_mode || ctx.runtime.config.force_single_partition {
        ctx.runtime.config.threads_to_use.max(1)
    } else {
        1
    }
}

fn block_size(ctx: &Context) -> usize {
    if ctx.runtime.config.phase2_block_size > 0 {
        return ctx
            .runtime
            .config
            .phase2_block_size
            .min(ctx.num_tableaux.max(1));
    }

    let workers = block_worker_count(ctx).max(1);
    ctx.num_tableaux.saturating_sub(1).div_ceil(workers).max(1)
}

pub(crate) fn compute_weighted_graph_block_relaxed(
    ctx: &mut Context,
    task: &PartitionTask,
    result: &mut SolverResult,
    resume: Option<(usize, u64, GraphCsr)>,
) -> TaskExecResult {
    let mut phase1_builder = ctx.flat_graph.take().unwrap_or_default();
    let phase1_edges = build_phase1_graph(ctx, &mut phase1_builder);
    let phase1 = csr_from_graph(&phase1_builder);

    let (mut current_snapshot, start_round, elapsed_millis) =
        if let Some((round, saved_elapsed_millis, current_snapshot)) = resume {
            (current_snapshot, round, saved_elapsed_millis)
        } else {
            result.total_edges = phase1_edges;
            result.special_edges = 0;
            result.epochs = 0;
            (phase1.clone(), 1, 0)
        };

    let block_ranges = compute_block_ranges(ctx.num_tableaux, block_size(ctx));
    let workers = block_worker_count(ctx);
    let pool = (workers > 1).then(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(workers.min(block_ranges.len().max(1)))
            .build()
            .expect("failed to build rayon thread pool")
    });

    for round in start_round..=ctx.runtime.config.fixed_point_max_epochs as usize {
        if shutdown_requested(&ctx.runtime) {
            return match save_block_relaxed_checkpoint(ctx, task, round, &current_snapshot) {
                Ok(()) => TaskExecResult::Interrupted,
                Err(err) => {
                    runtime_println(
                        &ctx.runtime,
                        compact_log_line(
                            "warn",
                            format_args!("checkpoint-save part={} err={err}", task.part_str),
                        ),
                    );
                    TaskExecResult::Failed
                }
            };
        }

        if let Some(progress) = &ctx.progress {
            progress.set_stage(
                &format!("block r{round}"),
                block_ranges.len() as u64,
                0,
                elapsed_millis,
            );
        }

        let block_results = if let Some(pool) = &pool {
            pool.install(|| {
                block_ranges
                    .par_iter()
                    .map(|&(start, end)| solve_block(ctx, &phase1, &current_snapshot, start, end))
                    .collect::<Vec<_>>()
            })
        } else {
            let mut results = Vec::with_capacity(block_ranges.len());
            for (block_idx, &(start, end)) in block_ranges.iter().enumerate() {
                if should_update_progress(block_idx) {
                    if let Some(progress) = &ctx.progress {
                        progress.update_position(block_idx as u64);
                    }
                }
                results.push(solve_block(ctx, &phase1, &current_snapshot, start, end));
            }
            results
        };

        let mut next_builder = graph_from_csr(&phase1, ctx.num_tableaux);
        let mut round_result = SolverResult {
            total_edges: phase1_edges,
            special_edges: 0,
            epochs: round as i32,
        };

        for block in block_results {
            round_result.total_edges += block.total_edges;
            round_result.special_edges += block.special_edges;
            for (u, v, weight) in block.edges {
                add_edge_to_graph(&mut next_builder, u, v, weight);
            }
        }

        let next_snapshot = csr_from_graph(&next_builder);
        if csr_graphs_equal(&current_snapshot, &next_snapshot) {
            ctx.flat_graph = Some(next_builder);
            *result = round_result;
            if let Some(progress) = &ctx.progress {
                progress.update_position(block_ranges.len() as u64);
            }
            return TaskExecResult::Success;
        }

        current_snapshot = next_snapshot;
        *result = round_result;

        if shutdown_requested(&ctx.runtime) {
            return match save_block_relaxed_checkpoint(ctx, task, round + 1, &current_snapshot) {
                Ok(()) => TaskExecResult::Interrupted,
                Err(err) => {
                    runtime_println(
                        &ctx.runtime,
                        compact_log_line(
                            "warn",
                            format_args!("checkpoint-save part={} err={err}", task.part_str),
                        ),
                    );
                    TaskExecResult::Failed
                }
            };
        }
    }

    ctx.flat_graph = Some(graph_from_csr(&current_snapshot, ctx.num_tableaux));
    result.epochs = ctx.runtime.config.fixed_point_max_epochs;
    TaskExecResult::Failed
}
