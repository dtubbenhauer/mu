mod newalg;

use std::collections::HashMap;
use std::env;
#[cfg(target_os = "macos")]
use std::ffi::CString;
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::marker::PhantomData;
use std::mem::{size_of, size_of_val};
use std::path::{Path, PathBuf};
use std::ptr;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressState, ProgressStyle};
use serde::{Deserialize, Serialize};

const DEFAULT_THREAD_COUNT: usize = 1;
const MIN_N: i32 = 1;
const MAX_N: i32 = 8;
const MAX_SUPPORTED_N: i32 = 32;

const DEBUG_MODE: bool = false;

const DEFAULT_MEMORY_FRACTION: f64 = 0.70;
const DEFAULT_MEMORY_RESERVE_MB: usize = 4096;
const DEFAULT_MEMORY_WAIT_SECONDS: i32 = 300;
const MEMORY_POLL_MILLISECONDS: u64 = 1000;

const MEMORY_ESTIMATE_HEADROOM: f64 = 1.35;
const MAX_CAPACITY: usize = i32::MAX as usize - 1;

const GRAPH_MAGIC: u32 = 0x5547_4C31;
const GRAPH_VERSION_U8_WEIGHTS: u32 = 2;
const GRAPH_VERSION: u32 = 3;
const CHECKPOINT_MAGIC: u32 = 0x5747_4350;
const CHECKPOINT_VERSION: u32 = 5;
const COMPLETE_METADATA_VERSION: u32 = 1;
const GRAPH_HASH_SEED: u64 = 0xcbf2_9ce4_8422_2325;
const GRAPH_HASH_PRIME: u64 = 0x0000_0001_0000_01b3;
const PROGRESS_UPDATE_STRIDE: usize = 256;
const PROGRESS_TICK_MILLIS: u64 = 120;
const SHUTDOWN_PROGRESS_MESSAGE: &str = "control-c received, saving and exiting...";

const COMPLETED_LOG_FILENAME: &str = "completed_partitions.log";
const STARTED_LOG_FILENAME: &str = "started_partitions.log";
const DEFERRED_LOG_FILENAME: &str = "deferred_partitions.log";
const FAILED_LOG_FILENAME: &str = "failed_partitions.log";

#[repr(C)]
#[derive(Clone, Copy)]
struct GraphFileHeader {
    magic: u32,
    version: u32,
    n: u32,
    partition_len: u32,
    num_vertices: u32,
    num_edges: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
struct Edge {
    target: i32,
    weight: i32,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
struct VertexFlat {
    edges: Vec<Edge>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
struct GraphCsr {
    offsets: Vec<usize>,
    edges: Vec<Edge>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
enum Phase2SolverMode {
    #[default]
    InPlace,
    FixedPoint,
    BlockRelaxed,
    Compare,
}

#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize)]
struct SolverResult {
    total_edges: i64,
    special_edges: i64,
    epochs: i32,
}

#[derive(Clone, Debug, Default)]
struct Phase2Stats {
    targets_with_j: u64,
    targets_without_j: u64,
    collection_calls: u64,
    collection_micros: u128,
    candidate_loop_micros: u128,
    bucket_visits: u64,
    nonempty_bucket_visits: u64,
    collected_candidates: u64,
    sort_calls: u64,
    sort_items: u64,
    restriction_component_skips: u64,
    restriction_seed_skips: u64,
    symmetry_skips: u64,
    evaluated_candidates: u64,
    reject_same_parity: u64,
    reject_descents: u64,
    reject_resnum: u64,
    favut_calls: u64,
    favut_successes: u64,
    favut_identity_successes: u64,
    favut_transform_successes: u64,
    favut_failures: u64,
    reject_after_favut: u64,
    direct_lookups: u64,
    direct_lookup_hits: u64,
    direct_lookup_scanned_edges: u64,
    recurrence_cases: u64,
    recurrence_cache_edges: u64,
    recurrence_cache_reuses: u64,
    recurrence_missing_v: u64,
    simple_cases: u64,
    simple_scanned_edges: u64,
    adjacent_cases: u64,
    adjacent_scanned_edges: u64,
    positive_weights: u64,
    zero_weights: u64,
}

#[derive(Clone, Copy, Debug, Default)]
struct BranchingDiagCounts {
    total: u64,
    positive: u64,
    zero: u64,
    special: u64,
}

#[derive(Clone, Debug, Default)]
struct BranchingDiagnostics {
    skipped_same_component: u64,
    seeded_same_component: u64,
    evaluated_same_component: u64,
    by_key: HashMap<u64, BranchingDiagCounts>,
}

impl BranchingDiagnostics {
    fn record(&mut self, key: u64, weight: i32) {
        self.evaluated_same_component += 1;
        let entry = self.by_key.entry(key).or_default();
        entry.total += 1;
        if weight > 0 {
            entry.positive += 1;
            if weight != 1 {
                entry.special += 1;
            }
        } else {
            entry.zero += 1;
        }
    }
}

fn print_branching_diagnostics(
    runtime: &Runtime,
    task: &PartitionTask,
    diag: &BranchingDiagnostics,
) {
    let positive_total = diag
        .by_key
        .values()
        .map(|counts| counts.positive)
        .sum::<u64>();
    let zero_total = diag.by_key.values().map(|counts| counts.zero).sum::<u64>();
    let special_total = diag
        .by_key
        .values()
        .map(|counts| counts.special)
        .sum::<u64>();
    runtime_println(
        runtime,
        compact_log_line(
            "branch",
            format_args!(
                "part={} same-eval={} pos={} zero={} special={} same-skip={} same-seed={} groups={}",
                task.part_str,
                diag.evaluated_same_component,
                positive_total,
                zero_total,
                special_total,
                diag.skipped_same_component,
                diag.seeded_same_component,
                diag.by_key.len()
            ),
        ),
    );

    let mut groups = diag
        .by_key
        .iter()
        .map(|(&key, &counts)| (key, counts))
        .collect::<Vec<_>>();
    groups.sort_unstable_by(|a, b| {
        b.1.positive
            .cmp(&a.1.positive)
            .then(b.1.total.cmp(&a.1.total))
            .then(a.0.cmp(&b.0))
    });

    for (rank, (key, counts)) in groups
        .iter()
        .copied()
        .filter(|(_, counts)| counts.positive > 0)
        .take(24)
        .enumerate()
    {
        let (i, j, du, dt, flags) = decode_branching_diag_key(key);
        runtime_println(
            runtime,
            compact_log_line(
                "branch",
                format_args!(
                    "part={} rank={} i={} j={} du={} dt={} flags={} total={} pos={} zero={} special={}",
                    task.part_str,
                    rank + 1,
                    i,
                    j,
                    du,
                    dt,
                    branch_flags_to_string(flags),
                    counts.total,
                    counts.positive,
                    counts.zero,
                    counts.special
                ),
            ),
        );
    }
}

fn print_phase2_stats(runtime: &Runtime, task: &PartitionTask, stats: &Phase2Stats) {
    runtime_println(
        runtime,
        compact_log_line(
            "stats",
            format_args!(
                "part={} targets-j={} targets-no-j={} candidates={} eval={} pos={} zero={}",
                task.part_str,
                stats.targets_with_j,
                stats.targets_without_j,
                stats.collected_candidates,
                stats.evaluated_candidates,
                stats.positive_weights,
                stats.zero_weights
            ),
        ),
    );
    runtime_println(
        runtime,
        compact_log_line(
            "stats",
            format_args!(
                "part={} collect={}us loop={}us buckets={} nonempty={} sort-calls={} sort-items={}",
                task.part_str,
                stats.collection_micros,
                stats.candidate_loop_micros,
                stats.bucket_visits,
                stats.nonempty_bucket_visits,
                stats.sort_calls,
                stats.sort_items
            ),
        ),
    );
    runtime_println(
        runtime,
        compact_log_line(
            "stats",
            format_args!(
                "part={} reject parity={} desc={} resnum={} favut-calls={} favut-ok={} favut-id={} favut-xform={} favut-fail={} after-favut={}",
                task.part_str,
                stats.reject_same_parity,
                stats.reject_descents,
                stats.reject_resnum,
                stats.favut_calls,
                stats.favut_successes,
                stats.favut_identity_successes,
                stats.favut_transform_successes,
                stats.favut_failures,
                stats.reject_after_favut
            ),
        ),
    );
    runtime_println(
        runtime,
        compact_log_line(
            "stats",
            format_args!(
                "part={} direct={} direct-hits={} direct-scan={} recur={} cache-edges={} cache-reuse={} missing-v={}",
                task.part_str,
                stats.direct_lookups,
                stats.direct_lookup_hits,
                stats.direct_lookup_scanned_edges,
                stats.recurrence_cases,
                stats.recurrence_cache_edges,
                stats.recurrence_cache_reuses,
                stats.recurrence_missing_v
            ),
        ),
    );
    runtime_println(
        runtime,
        compact_log_line(
            "stats",
            format_args!(
                "part={} simple={} simple-scan={} adjacent={} adjacent-scan={} restr-comp-skip={} restr-seed-skip={} sym-skip={}",
                task.part_str,
                stats.simple_cases,
                stats.simple_scanned_edges,
                stats.adjacent_cases,
                stats.adjacent_scanned_edges,
                stats.restriction_component_skips,
                stats.restriction_seed_skips,
                stats.symmetry_skips
            ),
        ),
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TaskState {
    Skip,
    Pending,
    Running,
    Done,
    Deferred,
    Failed,
}

#[derive(Clone, Debug)]
struct PartitionTask {
    n: usize,
    partition: [i32; 64],
    len: usize,
    part_str: String,
    dim_approx: f64,
    est_bytes: usize,
    initial_capacity: usize,
    attempts: usize,
    state: TaskState,
}

#[derive(Clone, Debug)]
struct Settings {
    async_mode: bool,
    force_single_partition: bool,
    range_min_n: i32,
    range_max_n: i32,
    threads_to_use: usize,
    output_dir: PathBuf,
    phase2_solver_mode: Phase2SolverMode,
    phase2_block_size: usize,
    fixed_point_max_epochs: i32,
    seed_restriction: bool,
    seed_restriction_load_only: bool,
    longest_word_symmetry: bool,
    phase2_stats: bool,
    branching_diagnostics: bool,
    memory_fraction: f64,
    memory_reserve_bytes: usize,
    memory_wait_seconds: i32,
}

impl Default for Settings {
    fn default() -> Self {
        Self {
            async_mode: false,
            force_single_partition: false,
            range_min_n: MIN_N,
            range_max_n: MAX_N,
            threads_to_use: DEFAULT_THREAD_COUNT,
            output_dir: PathBuf::from("data"),
            phase2_solver_mode: Phase2SolverMode::InPlace,
            phase2_block_size: 0,
            fixed_point_max_epochs: 256,
            seed_restriction: false,
            seed_restriction_load_only: false,
            longest_word_symmetry: false,
            phase2_stats: false,
            branching_diagnostics: false,
            memory_fraction: DEFAULT_MEMORY_FRACTION,
            memory_reserve_bytes: DEFAULT_MEMORY_RESERVE_MB * 1024 * 1024,
            memory_wait_seconds: DEFAULT_MEMORY_WAIT_SECONDS,
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct SchedulerCounts {
    pending: usize,
    running: usize,
    done: usize,
    deferred: usize,
    failed: usize,
}

#[derive(Debug)]
struct SchedulerState {
    tasks: Vec<PartitionTask>,
    global_reserved_bytes: usize,
    task_pending_count: usize,
    task_running_count: usize,
    task_done_count: usize,
    task_deferred_count: usize,
    task_failed_count: usize,
    last_progress_time: Instant,
}

#[derive(Clone, Debug)]
struct RuntimePaths {
    root: PathBuf,
    state_dir: PathBuf,
}

impl RuntimePaths {
    fn new(root: PathBuf) -> io::Result<Self> {
        fs::create_dir_all(&root)?;
        let state_dir = root.join("state");
        fs::create_dir_all(&state_dir)?;
        Ok(Self { root, state_dir })
    }

    fn log_path(&self, filename: &str) -> PathBuf {
        self.root.join(filename)
    }

    fn graph_dir(&self, n: usize) -> PathBuf {
        self.root.join(format!("S_{n}"))
    }

    fn graph_path(&self, task: &PartitionTask) -> PathBuf {
        self.graph_dir(task.n)
            .join(format!("{}.bin", task.part_str))
    }

    fn state_partition_dir(&self, n: usize) -> PathBuf {
        self.state_dir.join(format!("S_{n}"))
    }

    fn checkpoint_path(&self, task: &PartitionTask) -> PathBuf {
        self.state_partition_dir(task.n)
            .join(format!("{}.ckpt", task.part_str))
    }

    fn complete_path(&self, task: &PartitionTask) -> PathBuf {
        self.state_partition_dir(task.n)
            .join(format!("{}.done", task.part_str))
    }
}

#[derive(Debug)]
struct Runtime {
    config: Settings,
    paths: RuntimePaths,
    state: Mutex<SchedulerState>,
    log_lock: Mutex<()>,
    print_lock: Mutex<()>,
    multi_progress: MultiProgress,
    shutdown_bar: Mutex<Option<ProgressBar>>,
    shutdown_requested: AtomicBool,
    signal_count: AtomicUsize,
}

impl Runtime {
    fn new(
        config: Settings,
        paths: RuntimePaths,
        tasks: Vec<PartitionTask>,
        counts: SchedulerCounts,
    ) -> Self {
        let multi_progress =
            MultiProgress::with_draw_target(ProgressDrawTarget::stdout_with_hz(20));
        multi_progress.set_move_cursor(false);
        Self {
            config,
            paths,
            state: Mutex::new(SchedulerState {
                tasks,
                global_reserved_bytes: 0,
                task_pending_count: counts.pending,
                task_running_count: counts.running,
                task_done_count: counts.done,
                task_deferred_count: counts.deferred,
                task_failed_count: counts.failed,
                last_progress_time: Instant::now(),
            }),
            log_lock: Mutex::new(()),
            print_lock: Mutex::new(()),
            multi_progress,
            shutdown_bar: Mutex::new(None),
            shutdown_requested: AtomicBool::new(false),
            signal_count: AtomicUsize::new(0),
        }
    }
}

#[derive(Clone, Debug)]
struct TaskProgress {
    bar: ProgressBar,
}

impl TaskProgress {
    fn new(runtime: &Runtime, task: &PartitionTask) -> Self {
        let bar = runtime.multi_progress.add(ProgressBar::new(1));
        bar.set_style(progress_style());
        bar.set_prefix(task.part_str.clone());
        bar.set_message("queued");
        bar.enable_steady_tick(Duration::from_millis(PROGRESS_TICK_MILLIS));
        Self { bar }
    }

    fn set_stage(&self, stage: &str, len: u64, pos: u64, elapsed_millis: u64) {
        self.bar.set_length(len.max(1));
        self.bar.set_position(pos.min(len.max(1)));
        self.bar.set_elapsed(Duration::from_millis(elapsed_millis));
        self.bar.set_message(stage.to_string());
    }

    fn update_position(&self, pos: u64) {
        self.bar
            .set_position(pos.min(self.bar.length().unwrap_or(pos.max(1))));
    }

    fn elapsed_millis(&self) -> u64 {
        self.bar.elapsed().as_millis().min(u128::from(u64::MAX)) as u64
    }

    fn finish(&self) {
        self.bar.finish_and_clear();
    }
}

#[derive(Debug)]
struct Context {
    runtime: Arc<Runtime>,
    n: usize,
    table_width: usize,
    partition: [i32; 64],
    partition_len: usize,
    num_tableaux: usize,
    current_capacity: usize,
    global_tag: i32,
    reserved_bytes: usize,
    col_inds: Vec<u8>,
    row_inds: Vec<u8>,
    descents: Vec<u32>,
    table: Vec<i32>,
    flat_graph: Option<Vec<VertexFlat>>,
    weight_cache: Vec<i32>,
    cache_tags: Vec<i32>,
    cached_weight_vertex: usize,
    cached_weight_edge_len: usize,
    hash_keys: Vec<i32>,
    hash_size: usize,
    hash_mask: usize,
    full_desc_mask: u32,
    mask_offsets: Vec<u32>,
    mask_vertices: Vec<i32>,
    phase2_candidates: Vec<i32>,
    length_parity: Vec<u8>,
    max_positive_descent: Vec<u8>,
    progress: Option<TaskProgress>,
}

impl Context {
    fn new(task: &PartitionTask, runtime: Arc<Runtime>) -> Self {
        Self::with_capacity(task, runtime, task.initial_capacity.max(1))
    }

    fn with_capacity(task: &PartitionTask, runtime: Arc<Runtime>, current_capacity: usize) -> Self {
        let hash_size = next_hash_size_for_capacity(current_capacity);
        let n = task.n;
        let table_width = n.saturating_sub(1);
        let full_desc_mask = if n > MAX_SUPPORTED_N as usize {
            u32::MAX
        } else if n <= 1 {
            0
        } else {
            (1u32 << table_width) - 1
        };

        Self {
            runtime,
            n,
            table_width,
            partition: task.partition,
            partition_len: task.len,
            num_tableaux: 0,
            current_capacity,
            global_tag: 0,
            reserved_bytes: task.est_bytes,
            col_inds: vec![0; current_capacity * n],
            row_inds: vec![0; current_capacity * n],
            descents: vec![0; current_capacity],
            table: vec![0; current_capacity * table_width],
            flat_graph: None,
            weight_cache: vec![0; current_capacity],
            cache_tags: vec![0; current_capacity],
            cached_weight_vertex: usize::MAX,
            cached_weight_edge_len: 0,
            hash_keys: vec![-1; hash_size],
            hash_size,
            hash_mask: hash_size - 1,
            full_desc_mask,
            mask_offsets: Vec::new(),
            mask_vertices: Vec::new(),
            phase2_candidates: Vec::new(),
            length_parity: vec![0; current_capacity],
            max_positive_descent: Vec::new(),
            progress: None,
        }
    }

    #[inline(always)]
    fn seq_offset(&self, idx: usize) -> usize {
        idx * self.n
    }

    #[inline(always)]
    fn table_offset(&self, idx: usize) -> usize {
        idx * self.table_width
    }

    #[inline(always)]
    fn col_seq(&self, idx: usize) -> &[u8] {
        let start = self.seq_offset(idx);
        &self.col_inds[start..start + self.n]
    }

    #[inline(always)]
    fn table_index(&self, t: usize, s: usize) -> usize {
        self.table_offset(t) + s
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PersistedContext {
    n: usize,
    partition: Vec<i32>,
    partition_len: usize,
    num_tableaux: usize,
    current_capacity: usize,
    col_inds: Vec<u8>,
    row_inds: Vec<u8>,
    descents: Vec<u32>,
    table: Vec<i32>,
}

impl PersistedContext {
    fn from_context(ctx: &Context) -> Self {
        let used_seq = ctx.num_tableaux.saturating_mul(ctx.n);
        let used_table = ctx.num_tableaux.saturating_mul(ctx.table_width);
        Self {
            n: ctx.n,
            partition: ctx.partition[..ctx.partition_len].to_vec(),
            partition_len: ctx.partition_len,
            num_tableaux: ctx.num_tableaux,
            current_capacity: ctx.current_capacity,
            col_inds: ctx.col_inds[..used_seq].to_vec(),
            row_inds: ctx.row_inds[..used_seq].to_vec(),
            descents: ctx.descents[..ctx.num_tableaux].to_vec(),
            table: ctx.table[..used_table].to_vec(),
        }
    }

    fn restore(&self, task: &PartitionTask, runtime: Arc<Runtime>) -> Context {
        let mut ctx = Context::with_capacity(task, runtime, self.current_capacity.max(1));
        ctx.partition[..self.partition.len()].copy_from_slice(&self.partition);
        ctx.partition[self.partition.len()..].fill(0);
        ctx.partition_len = self.partition_len;
        ctx.num_tableaux = self.num_tableaux;
        ctx.col_inds[..self.col_inds.len()].copy_from_slice(&self.col_inds);
        ctx.row_inds[..self.row_inds.len()].copy_from_slice(&self.row_inds);
        ctx.descents[..self.descents.len()].copy_from_slice(&self.descents);
        ctx.table[..self.table.len()].copy_from_slice(&self.table);

        for idx in 0..ctx.num_tableaux {
            hash_insert(&mut ctx, idx);
        }

        ctx
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TableauxResume {
    next_m: usize,
    elapsed_millis: u64,
}

impl TableauxResume {
    fn into_tuple(self) -> (usize, u64) {
        (self.next_m, self.elapsed_millis)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct InPlaceResume {
    next_t: usize,
    elapsed_millis: u64,
    result: SolverResult,
    graph: Vec<VertexFlat>,
}

impl InPlaceResume {
    fn into_solver_resume(self) -> (usize, u64, SolverResult, Vec<VertexFlat>) {
        (self.next_t, self.elapsed_millis, self.result, self.graph)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct FixedPointResume {
    epoch: usize,
    next_t: usize,
    elapsed_millis: u64,
    epoch_result: SolverResult,
    current_snapshot: GraphCsr,
    next_builder: Vec<VertexFlat>,
}

impl FixedPointResume {
    fn into_solver_resume(self) -> (usize, usize, u64, SolverResult, GraphCsr, Vec<VertexFlat>) {
        (
            self.epoch,
            self.next_t,
            self.elapsed_millis,
            self.epoch_result,
            self.current_snapshot,
            self.next_builder,
        )
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct BlockRelaxedResume {
    round: usize,
    elapsed_millis: u64,
    current_snapshot: GraphCsr,
}

impl BlockRelaxedResume {
    fn into_solver_resume(self) -> (usize, u64, GraphCsr) {
        (self.round, self.elapsed_millis, self.current_snapshot)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CompareFixedPointResume {
    legacy_result: SolverResult,
    legacy_graph: Vec<VertexFlat>,
    fixed_point: FixedPointResume,
}

impl CompareFixedPointResume {
    fn into_parts(self) -> (SolverResult, Vec<VertexFlat>, FixedPointResume) {
        (self.legacy_result, self.legacy_graph, self.fixed_point)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Phase2Resume {
    InPlace(InPlaceResume),
    FixedPoint(FixedPointResume),
    BlockRelaxed(BlockRelaxedResume),
    CompareInPlace(InPlaceResume),
    CompareFixedPoint(CompareFixedPointResume),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum CheckpointResume {
    Tableaux(TableauxResume),
    Phase2(Phase2Resume),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
enum CheckpointResumeKind {
    Tableaux,
    InPlace,
    FixedPoint,
    BlockRelaxed,
    CompareInPlace,
    CompareFixedPoint,
}

impl CheckpointResume {
    fn kind(&self) -> CheckpointResumeKind {
        match self {
            Self::Tableaux(_) => CheckpointResumeKind::Tableaux,
            Self::Phase2(Phase2Resume::InPlace(_)) => CheckpointResumeKind::InPlace,
            Self::Phase2(Phase2Resume::FixedPoint(_)) => CheckpointResumeKind::FixedPoint,
            Self::Phase2(Phase2Resume::BlockRelaxed(_)) => CheckpointResumeKind::BlockRelaxed,
            Self::Phase2(Phase2Resume::CompareInPlace(_)) => CheckpointResumeKind::CompareInPlace,
            Self::Phase2(Phase2Resume::CompareFixedPoint(_)) => {
                CheckpointResumeKind::CompareFixedPoint
            }
        }
    }

    fn is_tableaux(&self) -> bool {
        matches!(self, Self::Tableaux(_))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CheckpointPayload {
    solver_mode: Phase2SolverMode,
    persisted: PersistedContext,
    resume: CheckpointResume,
}

impl CheckpointPayload {
    fn is_solver_compatible(&self, mode: Phase2SolverMode) -> bool {
        self.solver_mode == mode || self.resume.is_tableaux()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct CheckpointHeader {
    magic: u32,
    version: u32,
    solver_mode: Phase2SolverMode,
    resume_kind: CheckpointResumeKind,
    n: u32,
    partition_len: u32,
    current_capacity: u64,
    num_tableaux: u64,
}

#[derive(Debug, Clone)]
struct CheckpointSummary {
    solver_mode: Phase2SolverMode,
    resume_kind: CheckpointResumeKind,
    current_capacity: usize,
}

#[derive(Debug, Clone)]
struct CompleteRecord {
    total_edges: i64,
    special_edges: i64,
    epochs: i32,
    fingerprint: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TaskExecResult {
    Success,
    Interrupted,
    Failed,
}

#[derive(Debug)]
struct TaskProcessOutcome {
    result: TaskExecResult,
    reserved_bytes: usize,
    fail_reason: String,
}

fn main() {
    std::process::exit(run());
}

fn run() -> i32 {
    let start = Instant::now();
    let mut settings = Settings::default();
    let mut tasks = Vec::with_capacity(1000);
    let mut single_partition_str: Option<String> = None;
    let run_scope;

    let args: Vec<String> = env::args().collect();
    let prog = args.first().map_or("wgraphgen", String::as_str);

    if args.len() == 1
        || args
            .iter()
            .skip(1)
            .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        print_usage(prog);
        return 0;
    }

    let mut i = 1usize;
    while i < args.len() {
        match args[i].as_str() {
            "--async" => {
                settings.async_mode = true;
                i += 1;
            }
            "--partition" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                single_partition_str = Some(args[i + 1].clone());
                i += 2;
            }
            "--min-n" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                settings.range_min_n = parse_i32_arg(&args[i + 1]);
                i += 2;
            }
            "--max-n" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                settings.range_max_n = parse_i32_arg(&args[i + 1]);
                i += 2;
            }
            "--threads" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                let threads = parse_i64_arg(&args[i + 1]);
                if threads <= 0 {
                    eprintln!("Invalid thread count.");
                    return 1;
                }
                settings.threads_to_use = threads as usize;
                i += 2;
            }
            "--dir" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                settings.output_dir = PathBuf::from(&args[i + 1]);
                i += 2;
            }
            "--phase2-solver" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                settings.phase2_solver_mode = match args[i + 1].as_str() {
                    "inplace" => Phase2SolverMode::InPlace,
                    "fixed-point" => Phase2SolverMode::FixedPoint,
                    "block-relaxed" => Phase2SolverMode::BlockRelaxed,
                    "compare" => Phase2SolverMode::Compare,
                    mode => {
                        eprintln!("Invalid phase2 solver mode: {mode}");
                        return 1;
                    }
                };
                i += 2;
            }
            "--phase2-block-size" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                let block_size = parse_i64_arg(&args[i + 1]);
                if block_size <= 0 {
                    eprintln!("Invalid phase2 block size.");
                    return 1;
                }
                settings.phase2_block_size = block_size as usize;
                i += 2;
            }
            "--fixed-point-max-epochs" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                settings.fixed_point_max_epochs = parse_i32_arg(&args[i + 1]);
                if settings.fixed_point_max_epochs <= 0 {
                    eprintln!("Invalid fixed-point max epochs.");
                    return 1;
                }
                i += 2;
            }
            "--seed-restriction" => {
                settings.seed_restriction = true;
                i += 1;
            }
            "--longest-word-symmetry" => {
                settings.longest_word_symmetry = true;
                i += 1;
            }
            "--phase2-stats" => {
                settings.phase2_stats = true;
                i += 1;
            }
            "--branching-diagnostics" => {
                settings.branching_diagnostics = true;
                i += 1;
            }
            "--memory-fraction" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                settings.memory_fraction = parse_f64_arg(&args[i + 1]);
                if !(settings.memory_fraction > 0.0 && settings.memory_fraction <= 1.0) {
                    eprintln!("Invalid memory fraction.");
                    return 1;
                }
                i += 2;
            }
            "--memory-reserve-mb" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                let mb = parse_i64_arg(&args[i + 1]);
                if mb < 0 {
                    eprintln!("Invalid memory reserve.");
                    return 1;
                }
                settings.memory_reserve_bytes = (mb as usize).saturating_mul(1024 * 1024);
                i += 2;
            }
            "--memory-wait-seconds" => {
                if i + 1 >= args.len() {
                    print_usage(prog);
                    return 1;
                }
                settings.memory_wait_seconds = parse_i32_arg(&args[i + 1]);
                if settings.memory_wait_seconds < 0 {
                    eprintln!("Invalid wait seconds.");
                    return 1;
                }
                i += 2;
            }
            _ => {
                print_usage(prog);
                return 1;
            }
        }
    }

    if let Err(err) = validate_range(settings.range_min_n, settings.range_max_n) {
        eprintln!("{err}");
        return 1;
    }
    let single_partition = if let Some(single) = single_partition_str {
        let mut part = [0i32; 64];
        let Some((mut len, n)) = parse_partition_string(&single, &mut part) else {
            eprintln!(
                "Invalid partition: {single}; expected positive nonincreasing parts with n in 1..={MAX_SUPPORTED_N}"
            );
            return 1;
        };
        canonicalize_partition_lexmax(&mut part, &mut len);
        settings.force_single_partition = true;
        Some((part, len, n))
    } else {
        None
    };

    let paths = match RuntimePaths::new(settings.output_dir.clone()) {
        Ok(paths) => paths,
        Err(err) => {
            eprintln!(
                "Failed to initialize data dir {}: {err}",
                settings.output_dir.display()
            );
            return 1;
        }
    };

    let completed_count = load_completed_log(&paths).len();

    if let Some((part, len, n)) = single_partition {
        collect_task(n as usize, &part, len, &mut tasks);
        let canon = partition_to_string(&part, len);
        run_scope = format!("mode=single part={canon} n={n}");
    } else {
        run_scope = format!(
            "mode=range n={}..{} canonical=yes",
            settings.range_min_n, settings.range_max_n
        );
        let mut buffer = [0i32; 64];
        for n in settings.range_min_n..=settings.range_max_n {
            generate_partitions_recursive(n, n, &mut buffer, 0, n, &mut tasks);
        }
    }

    if let Err(err) = validate_execution_mode(&settings, tasks.len()) {
        eprintln!("{err}");
        return 1;
    }

    let counts = prepare_tasks_for_run(&mut tasks, &settings, &paths);
    let runtime = Arc::new(Runtime::new(settings, paths, tasks, counts));
    install_ctrlc_handler(&runtime);

    let task_count = runtime.state.lock().unwrap().tasks.len();
    println!(
        "{}",
        compact_log_line(
            "run",
            format_args!(
                "exec={} {run_scope} solver={} threads={} dir={}",
                execution_mode_name(runtime.config.async_mode),
                phase2_solver_name(runtime.config.phase2_solver_mode),
                runtime.config.threads_to_use,
                runtime.paths.root.display()
            )
        )
    );
    if runtime.config.async_mode {
        let available_now_mb = mb(get_available_memory_bytes());
        let budget_now_mb = mb(get_current_usable_budget_bytes(&runtime));
        let reserve_mb = mb(runtime.config.memory_reserve_bytes);
        println!(
            "{}",
            compact_log_line(
                "mem",
                format_args!(
                    "avail={}mb budget={}mb fraction={:.2} reserve={}mb wait={}s",
                    available_now_mb,
                    budget_now_mb,
                    runtime.config.memory_fraction,
                    reserve_mb,
                    runtime.config.memory_wait_seconds
                )
            )
        );
    }
    println!(
        "{}",
        compact_log_line(
            "tasks",
            format_args!(
                "total={} runnable={} skipped={} legacy-log={}",
                task_count,
                counts.pending,
                task_count.saturating_sub(counts.pending),
                completed_count
            )
        )
    );

    if runtime.config.async_mode {
        run_scheduler(&runtime);
    } else {
        run_synchronously(&runtime);
    }

    let shutdown_requested = runtime.shutdown_requested.load(Ordering::SeqCst);
    if shutdown_requested {
        finish_shutdown_progress(&runtime);
    }

    let (task_done_count, task_deferred_count, task_failed_count, task_pending_count) = {
        let state = runtime.state.lock().unwrap();
        (
            state.task_done_count,
            state.task_deferred_count,
            state.task_failed_count,
            state.task_pending_count,
        )
    };
    runtime_println(
        &runtime,
        compact_log_line(
            "time",
            format_args!("total={:.2}s", start.elapsed().as_secs_f64()),
        ),
    );
    runtime_println(
        &runtime,
        compact_log_line(
            "sum",
            format_args!(
                "done={} deferred={} failed={} pending={}",
                task_done_count, task_deferred_count, task_failed_count, task_pending_count
            ),
        ),
    );

    if shutdown_requested {
        runtime_println(
            &runtime,
            compact_log_line(
                "stop",
                format_args!("checkpoint-dir={}", runtime.paths.state_dir.display()),
            ),
        );
        130
    } else if task_failed_count > 0 || task_deferred_count > 0 {
        1
    } else {
        0
    }
}

fn parse_i32_arg(s: &str) -> i32 {
    s.parse::<i32>().unwrap_or(0)
}

fn parse_i64_arg(s: &str) -> i64 {
    s.parse::<i64>().unwrap_or(0)
}

fn parse_f64_arg(s: &str) -> f64 {
    s.parse::<f64>().unwrap_or(0.0)
}

fn print_usage(prog: &str) {
    eprintln!(
        "Usage:\n  {prog} --partition 5_5_3_3\n  \
         {prog} --async --min-n 1 --max-n 10 --threads 8\n  \
         {prog} --partition 6_6_3_3 --threads 1 --phase2-solver compare\n\n\
         Options:\n  \
         --help, -h                 Print usage and exit\n  \
         --async                    Enable async multi-partition scheduling with memory budgeting\n  \
         --partition <p>            Run exactly one partition (canonicalized up to conjugate)\n  \
         --min-n <a>                Range mode lower bound (default compile-time MIN_N)\n  \
         --max-n <b>                Range mode upper bound (default compile-time MAX_N)\n  \
         Supported n: 1..={MAX_SUPPORTED_N} (32-bit descent masks)\n  \
         --threads <t>              Async scheduler workers; also used by block-relaxed single runs\n  \
         --dir <path>               Root dir for graphs, logs, cache, and checkpoints (default data)\n  \
         --phase2-solver <mode>     inplace | fixed-point | block-relaxed | compare (default {})\n  \
         --phase2-block-size <n>    Block size for block-relaxed phase 2 (default auto)\n  \
         --fixed-point-max-epochs <n>\n                            \
         Max rounds for fixed-point/block-relaxed solvers (default 256)\n  \
         --seed-restriction         Experimental: seed inplace phase 2 from cached S_(n-1) graphs\n  \
         --longest-word-symmetry    Experimental: skip mirrored inplace phase-2 candidates via evacuation\n  \
         --phase2-stats             Print detailed inplace phase-2 profiling counters\n  \
         --branching-diagnostics    Print same-restriction-block candidate diagnostics\n  \
         --memory-fraction <x>      Async only: fraction of usable RAM to target (default {:.2})\n  \
         --memory-reserve-mb <m>    Async only: fixed RAM reserve in MB (default {DEFAULT_MEMORY_RESERVE_MB})\n  \
         --memory-wait-seconds <s>  Async only: wait before deferring pending tasks (default {DEFAULT_MEMORY_WAIT_SECONDS})",
        phase2_solver_name(Phase2SolverMode::InPlace),
        DEFAULT_MEMORY_FRACTION,
    );
}

fn execution_mode_name(async_mode: bool) -> &'static str {
    if async_mode { "async" } else { "sync" }
}

fn validate_range(min_n: i32, max_n: i32) -> Result<(), String> {
    if !(1..=MAX_SUPPORTED_N).contains(&min_n) || !(1..=MAX_SUPPORTED_N).contains(&max_n) {
        return Err(format!("Invalid range: n must be in 1..={MAX_SUPPORTED_N}"));
    }
    if min_n > max_n {
        return Err("Invalid range: min-n > max-n".to_string());
    }
    Ok(())
}

fn validate_execution_mode(settings: &Settings, task_count: usize) -> Result<(), String> {
    if settings.longest_word_symmetry && settings.phase2_solver_mode != Phase2SolverMode::InPlace {
        return Err(
            "--longest-word-symmetry is currently implemented only for --phase2-solver inplace"
                .to_string(),
        );
    }
    if settings.phase2_stats && settings.phase2_solver_mode != Phase2SolverMode::InPlace {
        return Err(
            "--phase2-stats is currently implemented only for --phase2-solver inplace".to_string(),
        );
    }
    if settings.branching_diagnostics && settings.phase2_solver_mode != Phase2SolverMode::InPlace {
        return Err(
            "--branching-diagnostics is currently implemented only for --phase2-solver inplace"
                .to_string(),
        );
    }
    if settings.branching_diagnostics && !settings.seed_restriction {
        return Err("--branching-diagnostics requires --seed-restriction".to_string());
    }
    if settings.async_mode || task_count <= 1 {
        return Ok(());
    }
    Err(format!(
        "Synchronous mode accepts one partition per invocation; this invocation produced {task_count}. Pass --async to enable multi-partition scheduling."
    ))
}

fn partition_to_string(part: &[i32; 64], len: usize) -> String {
    let mut out = String::new();
    for (idx, value) in part[..len].iter().enumerate() {
        if idx > 0 {
            out.push('_');
        }
        out.push_str(&value.to_string());
    }
    out
}

fn parse_partition_string(s: &str, out: &mut [i32; 64]) -> Option<(usize, i32)> {
    if s.is_empty() || s.len() >= 256 {
        return None;
    }

    let mut len = 0usize;
    let mut sum = 0i32;

    for token in s.split(|ch| matches!(ch, '_' | ' ' | ',')) {
        if token.is_empty() {
            continue;
        }
        if len >= 64 {
            return None;
        }
        let value = token.parse::<i32>().ok()?;
        if value <= 0 {
            return None;
        }
        if len > 0 && value > out[len - 1] {
            return None;
        }
        out[len] = value;
        len += 1;
        sum = sum.checked_add(value)?;
    }

    (len > 0 && (1..=MAX_SUPPORTED_N).contains(&sum)).then_some((len, sum))
}

fn compare_partitions_lex(a: &[i32], b: &[i32]) -> i32 {
    let min_len = a.len().min(b.len());
    for idx in 0..min_len {
        if a[idx] < b[idx] {
            return -1;
        }
        if a[idx] > b[idx] {
            return 1;
        }
    }
    match a.len().cmp(&b.len()) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

fn compute_conjugate_partition(part: &[i32; 64], len: usize, conj: &mut [i32; 64]) -> usize {
    conj.fill(0);
    let max_col = part[0] as usize;
    for col in 0..max_col {
        let mut count = 0i32;
        for &entry in &part[..len] {
            if entry > col as i32 {
                count += 1;
            }
        }
        conj[col] = count;
    }

    let mut conj_len = max_col;
    while conj_len > 0 && conj[conj_len - 1] == 0 {
        conj_len -= 1;
    }
    conj_len
}

fn canonicalize_partition_lexmax(part: &mut [i32; 64], len: &mut usize) {
    let mut conj = [0i32; 64];
    let conj_len = compute_conjugate_partition(part, *len, &mut conj);

    if compare_partitions_lex(&part[..*len], &conj[..conj_len]) < 0 {
        part[..conj_len].copy_from_slice(&conj[..conj_len]);
        *len = conj_len;
    }
}

fn is_partition_canonical_lexmax(part: &[i32], len: usize) -> bool {
    let mut part_array = [0i32; 64];
    part_array[..len].copy_from_slice(&part[..len]);
    let mut conj = [0i32; 64];
    let conj_len = compute_conjugate_partition(&part_array, len, &mut conj);
    compare_partitions_lex(&part[..len], &conj[..conj_len]) >= 0
}

fn load_completed_log(paths: &RuntimePaths) -> Vec<String> {
    let Ok(file) = File::open(paths.log_path(COMPLETED_LOG_FILENAME)) else {
        return Vec::new();
    };

    let mut completed = Vec::new();
    for line in BufReader::new(file).lines().map_while(Result::ok) {
        if line.is_empty() {
            continue;
        }
        let name = line.split_once('|').map_or(line.as_str(), |(left, _)| left);
        if name.is_empty() {
            continue;
        }

        let mut part = [0i32; 64];
        if let Some((mut len, _)) = parse_partition_string(name, &mut part) {
            canonicalize_partition_lexmax(&mut part, &mut len);
            completed.push(partition_to_string(&part, len));
        } else {
            completed.push(name.to_string());
        }
    }

    completed.sort_unstable();
    completed
}

fn append_completed_log(
    paths: &RuntimePaths,
    task: &PartitionTask,
    tableaux: usize,
    edges: i64,
    specials: i64,
) {
    let Ok(mut file) = OpenOptions::new()
        .append(true)
        .create(true)
        .open(paths.log_path(COMPLETED_LOG_FILENAME))
    else {
        eprintln!(
            "{}",
            compact_log_line(
                "warn",
                format_args!("log={} append=failed", COMPLETED_LOG_FILENAME)
            )
        );
        return;
    };

    let now = now_unix_seconds();
    let _ = writeln!(
        file,
        "{}|N={}|tableaux={}|edges={}|specials={}|est_mb={}|time={}",
        task.part_str,
        task.n,
        tableaux,
        edges,
        specials,
        mb(task.est_bytes),
        now
    );
    let _ = file.flush();
}

fn append_started_log(paths: &RuntimePaths, task: &PartitionTask, budget_bytes: usize) {
    let Ok(mut file) = OpenOptions::new()
        .append(true)
        .create(true)
        .open(paths.log_path(STARTED_LOG_FILENAME))
    else {
        return;
    };

    let now = now_unix_seconds();
    let _ = writeln!(
        file,
        "{}|N={}|est_mb={}|budget_mb={}|attempt={}|time={}",
        task.part_str,
        task.n,
        mb(task.est_bytes),
        mb(budget_bytes),
        task.attempts,
        now
    );
    let _ = file.flush();
}

fn append_deferred_log(
    paths: &RuntimePaths,
    task: &PartitionTask,
    reason: &str,
    budget_bytes: usize,
) {
    let Ok(mut file) = OpenOptions::new()
        .append(true)
        .create(true)
        .open(paths.log_path(DEFERRED_LOG_FILENAME))
    else {
        return;
    };

    let now = now_unix_seconds();
    let _ = writeln!(
        file,
        "{}|N={}|reason={}|est_mb={}|budget_mb={}|attempt={}|time={}",
        task.part_str,
        task.n,
        reason,
        mb(task.est_bytes),
        mb(budget_bytes),
        task.attempts,
        now
    );
    let _ = file.flush();
}

fn append_failed_log(paths: &RuntimePaths, task: &PartitionTask, reason: &str) {
    let Ok(mut file) = OpenOptions::new()
        .append(true)
        .create(true)
        .open(paths.log_path(FAILED_LOG_FILENAME))
    else {
        return;
    };

    let now = now_unix_seconds();
    let _ = writeln!(
        file,
        "{}|N={}|reason={}|attempt={}|time={}",
        task.part_str, task.n, reason, task.attempts, now
    );
    let _ = file.flush();
}

fn progress_style() -> ProgressStyle {
    ProgressStyle::with_template(
        "{spinner:.cyan} {prefix:>16} {msg:>10} {wide_bar:.cyan/blue} {pos:>7}/{len:7} \
         {percent:>3}% eta {eta_true} [{time_true}]",
    )
    .expect("valid progress template")
    .with_key(
        "eta_true",
        |state: &ProgressState, w: &mut dyn fmt::Write| {
            let _ = w.write_str(&format_progress_eta(state));
        },
    )
    .with_key(
        "time_true",
        |state: &ProgressState, w: &mut dyn fmt::Write| {
            let _ = w.write_str(&format_progress_duration(state.elapsed()));
        },
    )
    .progress_chars("█▉▊▋▌▍▎▏ ")
    .tick_strings(&["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏", "⠋"])
}

fn format_progress_eta(state: &ProgressState) -> String {
    let Some(len) = state.len() else {
        return "--:--:--".to_string();
    };

    let pos = state.pos();
    if pos == 0 {
        return "--:--:--".to_string();
    }
    if pos >= len {
        return "00:00:00".to_string();
    }

    let elapsed_millis = state.elapsed().as_millis();
    if elapsed_millis == 0 {
        return "--:--:--".to_string();
    }

    format_progress_duration(Duration::from_millis(estimate_sqrt_progress_eta_millis(
        elapsed_millis,
        pos,
        len,
    )))
}

fn estimate_sqrt_progress_eta_millis(elapsed_millis: u128, pos: u64, len: u64) -> u64 {
    if elapsed_millis == 0 || pos == 0 || pos >= len {
        return 0;
    }

    let len = u128::from(len);
    let pos = u128::from(pos);
    let len_squared = len * len;
    let pos_squared = pos * pos;
    let eta_millis = elapsed_millis.saturating_mul(len_squared - pos_squared) / pos_squared;
    eta_millis.min(u128::from(u64::MAX)) as u64
}

fn format_progress_duration(duration: Duration) -> String {
    let total_secs = duration.as_secs();
    let hours = total_secs / 3600;
    let minutes = (total_secs / 60) % 60;
    let seconds = total_secs % 60;
    format!("{hours:02}:{minutes:02}:{seconds:02}")
}

fn shutdown_progress_style() -> ProgressStyle {
    ProgressStyle::with_template("{spinner:.cyan} {msg}")
        .expect("valid shutdown progress template")
        .tick_strings(&["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏", "⠋"])
}

fn compact_log_line(tag: &str, args: fmt::Arguments<'_>) -> String {
    format!("{tag:<5} {args}")
}

fn show_shutdown_progress(runtime: &Runtime) {
    if runtime.multi_progress.is_hidden() {
        runtime_println(runtime, SHUTDOWN_PROGRESS_MESSAGE);
        return;
    }

    let mut shutdown_bar = runtime.shutdown_bar.lock().unwrap();
    if shutdown_bar.is_some() {
        return;
    }

    let bar = runtime.multi_progress.add(ProgressBar::new_spinner());
    bar.set_style(shutdown_progress_style());
    bar.set_message(SHUTDOWN_PROGRESS_MESSAGE.to_string());
    bar.enable_steady_tick(Duration::from_millis(PROGRESS_TICK_MILLIS));
    *shutdown_bar = Some(bar);
}

fn finish_shutdown_progress(runtime: &Runtime) {
    let shutdown_bar = runtime.shutdown_bar.lock().unwrap();
    if let Some(bar) = shutdown_bar.as_ref() {
        bar.finish_with_message(SHUTDOWN_PROGRESS_MESSAGE.to_string());
    }
}

fn runtime_println(runtime: &Runtime, line: impl AsRef<str>) {
    let line = line.as_ref();
    let _guard = runtime.print_lock.lock().unwrap();
    if runtime.multi_progress.is_hidden() {
        println!("{line}");
    } else {
        let _ = runtime.multi_progress.println(line);
    }
}

fn install_ctrlc_handler(runtime: &Arc<Runtime>) {
    let runtime = Arc::clone(runtime);
    let _ = ctrlc::set_handler(move || {
        let previous = runtime.signal_count.fetch_add(1, Ordering::SeqCst);
        runtime.shutdown_requested.store(true, Ordering::SeqCst);
        if previous == 0 {
            show_shutdown_progress(&runtime);
        }
    });
}

fn ensure_parent_dir(path: &Path) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    Ok(())
}

fn write_atomic(path: &Path, bytes: &[u8]) -> io::Result<()> {
    ensure_parent_dir(path)?;
    let tmp_path = path.with_extension(format!(
        "{}.tmp",
        path.extension()
            .and_then(|ext| ext.to_str())
            .unwrap_or_default()
    ));
    {
        let mut writer = BufWriter::new(File::create(&tmp_path)?);
        writer.write_all(bytes)?;
        writer.flush()?;
    }
    fs::rename(tmp_path, path)?;
    Ok(())
}

fn write_text_atomic(path: &Path, text: &str) -> io::Result<()> {
    write_atomic(path, text.as_bytes())
}

fn checkpoint_summary(
    paths: &RuntimePaths,
    task: &PartitionTask,
) -> io::Result<Option<CheckpointSummary>> {
    let path = paths.checkpoint_path(task);
    let Ok(file) = File::open(path) else {
        return Ok(None);
    };
    let mut reader = BufReader::new(file);

    let header: CheckpointHeader =
        bincode::serde::decode_from_std_read(&mut reader, bincode::config::standard())
            .map_err(|err| io::Error::other(err.to_string()))?;
    if header.magic != CHECKPOINT_MAGIC || header.version != CHECKPOINT_VERSION {
        return Ok(None);
    }
    if header.n as usize != task.n || header.partition_len as usize != task.len {
        return Ok(None);
    }

    Ok(Some(CheckpointSummary {
        solver_mode: header.solver_mode,
        resume_kind: header.resume_kind,
        current_capacity: header.current_capacity as usize,
    }))
}

fn save_checkpoint(
    paths: &RuntimePaths,
    task: &PartitionTask,
    solver_mode: Phase2SolverMode,
    persisted: PersistedContext,
    resume: CheckpointResume,
) -> io::Result<()> {
    let path = paths.checkpoint_path(task);
    ensure_parent_dir(&path)?;

    let header = CheckpointHeader {
        magic: CHECKPOINT_MAGIC,
        version: CHECKPOINT_VERSION,
        solver_mode,
        resume_kind: resume.kind(),
        n: task.n as u32,
        partition_len: task.len as u32,
        current_capacity: persisted.current_capacity as u64,
        num_tableaux: persisted.num_tableaux as u64,
    };

    let payload = CheckpointPayload {
        solver_mode,
        persisted,
        resume,
    };

    let tmp_path = path.with_extension("ckpt.tmp");
    {
        let mut writer = BufWriter::new(File::create(&tmp_path)?);
        bincode::serde::encode_into_std_write(&header, &mut writer, bincode::config::standard())
            .map_err(|err| io::Error::other(err.to_string()))?;
        bincode::serde::encode_into_std_write(&payload, &mut writer, bincode::config::standard())
            .map_err(|err| io::Error::other(err.to_string()))?;
        writer.flush()?;
    }
    fs::rename(tmp_path, path)?;
    Ok(())
}

fn load_checkpoint(
    paths: &RuntimePaths,
    task: &PartitionTask,
) -> io::Result<Option<CheckpointPayload>> {
    let path = paths.checkpoint_path(task);
    let Ok(file) = File::open(path) else {
        return Ok(None);
    };
    let mut reader = BufReader::new(file);

    let header: CheckpointHeader =
        bincode::serde::decode_from_std_read(&mut reader, bincode::config::standard())
            .map_err(|err| io::Error::other(err.to_string()))?;
    if header.magic != CHECKPOINT_MAGIC || header.version != CHECKPOINT_VERSION {
        return Ok(None);
    }
    if header.n as usize != task.n || header.partition_len as usize != task.len {
        return Ok(None);
    }

    let payload: CheckpointPayload =
        bincode::serde::decode_from_std_read(&mut reader, bincode::config::standard())
            .map_err(|err| io::Error::other(err.to_string()))?;
    Ok(Some(payload))
}

fn delete_checkpoint(paths: &RuntimePaths, task: &PartitionTask) {
    let _ = fs::remove_file(paths.checkpoint_path(task));
}

fn load_complete_record(
    paths: &RuntimePaths,
    task: &PartitionTask,
) -> io::Result<Option<CompleteRecord>> {
    let path = paths.complete_path(task);
    let Ok(text) = fs::read_to_string(&path) else {
        return Ok(None);
    };

    let mut version = None;
    let mut n = None;
    let mut part = None;
    let mut tableaux = None;
    let mut edges = None;
    let mut specials = None;
    let mut epochs = None;
    let mut fingerprint = None;
    let mut graph_rel_path = None;
    let mut completed_at = None;

    for line in text.lines() {
        let Some((key, value)) = line.split_once('=') else {
            continue;
        };
        match key {
            "version" => version = value.parse::<u32>().ok(),
            "n" => n = value.parse::<usize>().ok(),
            "part" => part = Some(value.to_string()),
            "tableaux" => tableaux = value.parse::<usize>().ok(),
            "edges" => edges = value.parse::<i64>().ok(),
            "specials" => specials = value.parse::<i64>().ok(),
            "epochs" => epochs = value.parse::<i32>().ok(),
            "fingerprint" => fingerprint = Some(value.to_ascii_lowercase()),
            "graph" => graph_rel_path = Some(value.to_string()),
            "completed_at" => completed_at = value.parse::<i64>().ok(),
            _ => {}
        }
    }

    if version != Some(COMPLETE_METADATA_VERSION)
        || n != Some(task.n)
        || part.as_deref() != Some(task.part_str.as_str())
    {
        return Ok(None);
    }

    let Some(graph_rel_path) = graph_rel_path else {
        return Ok(None);
    };
    let graph_path = paths.root.join(&graph_rel_path);
    if !graph_path.is_file() {
        return Ok(None);
    }

    let _ = tableaux;
    let _ = completed_at;
    Ok(Some(CompleteRecord {
        total_edges: edges.unwrap_or(0),
        special_edges: specials.unwrap_or(0),
        epochs: epochs.unwrap_or(0),
        fingerprint: fingerprint.unwrap_or_else(|| "00000000".to_string()),
    }))
}

fn save_complete_record(
    paths: &RuntimePaths,
    task: &PartitionTask,
    num_tableaux: usize,
    result: SolverResult,
    fingerprint: &str,
) -> io::Result<()> {
    let graph_rel_path = paths
        .graph_path(task)
        .strip_prefix(&paths.root)
        .unwrap_or_else(|_| Path::new(""))
        .to_string_lossy()
        .to_string();
    let content = format!(
        "version={COMPLETE_METADATA_VERSION}\n\
         n={}\n\
         part={}\n\
         tableaux={}\n\
         edges={}\n\
         specials={}\n\
         epochs={}\n\
         fingerprint={}\n\
         graph={}\n\
         completed_at={}\n",
        task.n,
        task.part_str,
        num_tableaux,
        result.total_edges,
        result.special_edges,
        result.epochs,
        fingerprint,
        graph_rel_path,
        now_unix_seconds()
    );
    write_text_atomic(&paths.complete_path(task), &content)
}

fn cached_summary_line(task: &PartitionTask, record: &CompleteRecord) -> String {
    if record.special_edges > 0 {
        compact_log_line(
            "alert",
            format_args!(
                "part={} specials={} total={} epochs={} fp={} cache=yes",
                task.part_str,
                record.special_edges,
                record.total_edges,
                record.epochs,
                record.fingerprint
            ),
        )
    } else {
        compact_log_line(
            "cache",
            format_args!(
                "part={} n={} fp={}",
                task.part_str, task.n, record.fingerprint
            ),
        )
    }
}

fn next_hash_size_for_capacity(cap: usize) -> usize {
    let need = if cap < 1024 { 1024 } else { cap * 2 };
    let mut hash_size = 1usize;
    while hash_size < need {
        if hash_size > usize::MAX / 2 {
            panic!("hash size overflow");
        }
        hash_size <<= 1;
    }
    hash_size
}

fn exact_specht_dimension_capped(n: usize, part: &[i32], len: usize, cap: u64) -> u64 {
    let mut primes = [0usize; 64];
    let mut prime_count = 0usize;
    let mut is_composite = [false; 256];

    for p in 2..=n {
        if !is_composite[p] {
            primes[prime_count] = p;
            prime_count += 1;
            if p * p <= n {
                let mut q = p * p;
                while q <= n {
                    is_composite[q] = true;
                    q += p;
                }
            }
        }
    }

    let mut exponents = [0i32; 64];
    for idx in 0..prime_count {
        let p = primes[idx];
        let mut m = n;
        while m > 0 {
            m /= p;
            exponents[idx] += m as i32;
        }
    }

    let mut conjugate = [0i32; 64];
    for col in 0..part[0] as usize {
        for &row in &part[..len] {
            if row > col as i32 {
                conjugate[col] += 1;
            }
        }
    }

    for row in 0..len {
        for col in 0..part[row] as usize {
            let mut hook = (part[row] - col as i32) + (conjugate[col] - row as i32) - 1;
            for idx in 0..prime_count {
                let p = primes[idx] as i32;
                while hook % p == 0 {
                    exponents[idx] -= 1;
                    hook /= p;
                }
                if hook == 1 {
                    break;
                }
            }
            assert!(hook == 1, "failed to factor hook length {hook}");
        }
    }

    let mut result = 1u128;
    for idx in 0..prime_count {
        for _ in 0..exponents[idx] {
            result *= primes[idx] as u128;
            if result > cap as u128 {
                return cap;
            }
        }
    }
    result as u64
}

fn checked_specht_dimension(n: usize, part: &[i32], len: usize) -> Result<usize, String> {
    let dimension = exact_specht_dimension_capped(n, part, len, MAX_CAPACITY as u64 + 1);
    if dimension > MAX_CAPACITY as u64 {
        return Err(format!(
            "tableau dimension exceeds vertex limit {MAX_CAPACITY}"
        ));
    }
    Ok(dimension as usize)
}

fn vertex_graph_storage_budget_for_capacity(n: usize, cap: usize) -> usize {
    cap.saturating_mul(size_of::<VertexFlat>())
        + 4usize
            .saturating_mul(cap)
            .saturating_mul(n.saturating_sub(1))
            .saturating_mul(size_of::<Edge>())
}

fn csr_graph_storage_budget_for_capacity(n: usize, cap: usize) -> usize {
    cap.saturating_add(1).saturating_mul(size_of::<usize>())
        + 4usize
            .saturating_mul(cap)
            .saturating_mul(n.saturating_sub(1))
            .saturating_mul(size_of::<Edge>())
}

fn estimate_context_bytes_for_capacity(n: usize, cap: usize, mode: Phase2SolverMode) -> usize {
    let mask_bucket_count = if (2..32).contains(&n) {
        2usize.saturating_mul(1usize << (n - 1))
    } else {
        0
    };

    let mut total = 0usize;
    total = total.saturating_add(next_hash_size_for_capacity(cap).saturating_mul(size_of::<i32>()));
    total = total.saturating_add(cap.saturating_mul(n).saturating_mul(size_of::<u8>()));
    total = total.saturating_add(cap.saturating_mul(n).saturating_mul(size_of::<u8>()));
    total = total.saturating_add(cap.saturating_mul(size_of::<i32>()));
    total = total.saturating_add(cap.saturating_mul(size_of::<i32>()));
    total = total.saturating_add(
        cap.saturating_mul(n.saturating_sub(1))
            .saturating_mul(size_of::<i32>()),
    );
    total = total.saturating_add(cap.saturating_mul(size_of::<u32>()));
    total = total.saturating_add(cap.saturating_mul(size_of::<i32>()));
    total = total.saturating_add(cap.saturating_mul(size_of::<i32>()));
    total = total.saturating_add(cap.saturating_mul(size_of::<u8>()));
    total = total.saturating_add(cap.saturating_mul(size_of::<u8>()));
    total = total.saturating_add(
        mask_bucket_count
            .saturating_add(1)
            .saturating_mul(size_of::<u32>()),
    );

    match mode {
        Phase2SolverMode::FixedPoint => {
            total = total.saturating_add(vertex_graph_storage_budget_for_capacity(n, cap));
            total = total.saturating_add(
                2usize.saturating_mul(csr_graph_storage_budget_for_capacity(n, cap)),
            );
        }
        Phase2SolverMode::BlockRelaxed => {
            total = total.saturating_add(vertex_graph_storage_budget_for_capacity(n, cap));
            total = total.saturating_add(
                2usize.saturating_mul(csr_graph_storage_budget_for_capacity(n, cap)),
            );
            total = total.saturating_add(csr_graph_storage_budget_for_capacity(n, cap));
        }
        Phase2SolverMode::Compare => {
            total = total.saturating_add(
                2usize.saturating_mul(vertex_graph_storage_budget_for_capacity(n, cap)),
            );
            total = total.saturating_add(
                2usize.saturating_mul(csr_graph_storage_budget_for_capacity(n, cap)),
            );
        }
        Phase2SolverMode::InPlace => {
            total = total.saturating_add(vertex_graph_storage_budget_for_capacity(n, cap));
        }
    }

    total
}

fn get_total_physical_memory_bytes() -> usize {
    #[cfg(target_os = "macos")]
    {
        let name = CString::new("hw.memsize").expect("static string");
        let mut mem: i64 = 0;
        let mut len = size_of::<i64>();
        // SAFETY: sysctlbyname writes at most `len` bytes into `mem`.
        let rc = unsafe {
            libc::sysctlbyname(
                name.as_ptr(),
                (&mut mem as *mut i64).cast(),
                &mut len,
                ptr::null_mut(),
                0,
            )
        };
        if rc == 0 && mem > 0 {
            return mem as usize;
        }
    }

    // SAFETY: sysconf is thread-safe and has no aliasing requirements.
    let pages = unsafe { libc::sysconf(libc::_SC_PHYS_PAGES) };
    // SAFETY: sysconf is thread-safe and has no aliasing requirements.
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if pages > 0 && page_size > 0 {
        return (pages as usize).saturating_mul(page_size as usize);
    }

    0
}

fn get_available_memory_bytes() -> usize {
    #[cfg(target_os = "linux")]
    {
        // 1. Try /proc/meminfo for high precision on Linux
        if let Ok(file) = File::open("/proc/meminfo") {
            for line in BufReader::new(file).lines().map_while(Result::ok) {
                if let Some(rest) = line.strip_prefix("MemAvailable:") {
                    if let Some(kb) = rest
                        .split_whitespace()
                        .next()
                        .and_then(|v| v.parse::<u64>().ok())
                    {
                        return (kb as usize).saturating_mul(1024);
                    }
                }
            }
        }

        // 2. Fallback to sysconf (Linux only)
        // SAFETY: sysconf is thread-safe and has no aliasing requirements.
        let pages = unsafe { libc::sysconf(libc::_SC_AVPHYS_PAGES) };
        let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        if pages > 0 && page_size > 0 {
            return (pages as usize).saturating_mul(page_size as usize);
        }
    }

    // 3. Fallback for macOS (and others):
    // Since macOS doesn't have _SC_AVPHYS_PAGES, we use the total memory
    // as the baseline for our budget calculation.
    get_total_physical_memory_bytes()
}

fn compute_usable_budget_bytes_unlocked(reserved_snapshot: usize, config: &Settings) -> usize {
    let avail = get_available_memory_bytes();
    let base = avail as f64 + reserved_snapshot as f64;
    let usable = config.memory_fraction * base - config.memory_reserve_bytes as f64;

    if usable <= 0.0 {
        return 0;
    }
    if usable >= usize::MAX as f64 {
        return usize::MAX;
    }
    usable as usize
}

fn get_current_usable_budget_bytes(runtime: &Runtime) -> usize {
    let reserved_snapshot = runtime.state.lock().unwrap().global_reserved_bytes;
    compute_usable_budget_bytes_unlocked(reserved_snapshot, &runtime.config)
}

fn wait_for_additional_reservation(ctx: &mut Context, new_required_bytes: usize) -> bool {
    if new_required_bytes <= ctx.reserved_bytes {
        return true;
    }

    if !ctx.runtime.config.async_mode {
        ctx.reserved_bytes = new_required_bytes;
        return true;
    }

    let delta = new_required_bytes - ctx.reserved_bytes;
    let start = Instant::now();

    loop {
        if ctx.runtime.shutdown_requested.load(Ordering::SeqCst) {
            return false;
        }

        {
            let mut state = ctx.runtime.state.lock().unwrap();
            let budget = compute_usable_budget_bytes_unlocked(
                state.global_reserved_bytes,
                &ctx.runtime.config,
            );
            if state.global_reserved_bytes <= budget
                && delta <= budget.saturating_sub(state.global_reserved_bytes)
            {
                state.global_reserved_bytes += delta;
                state.last_progress_time = Instant::now();
                ctx.reserved_bytes = new_required_bytes;
                return true;
            }
        }

        if ctx.runtime.config.memory_wait_seconds >= 0
            && start.elapsed() >= Duration::from_secs(ctx.runtime.config.memory_wait_seconds as u64)
        {
            return false;
        }

        sleep_millis(MEMORY_POLL_MILLISECONDS);
    }
}

fn release_reserved_bytes_after_task(runtime: &Runtime, bytes_released: usize) {
    let mut state = runtime.state.lock().unwrap();
    state.global_reserved_bytes = state.global_reserved_bytes.saturating_sub(bytes_released);
    state.last_progress_time = Instant::now();
}

fn ensure_capacity(ctx: &mut Context) -> bool {
    if ctx.num_tableaux < ctx.current_capacity {
        return true;
    }
    if ctx.current_capacity >= MAX_CAPACITY {
        return false;
    }

    let new_cap = (ctx.current_capacity * 2).min(MAX_CAPACITY);
    let base_required =
        estimate_context_bytes_for_capacity(ctx.n, new_cap, ctx.runtime.config.phase2_solver_mode);
    let mut new_required_bytes = (base_required as f64 * MEMORY_ESTIMATE_HEADROOM) as usize;
    if new_required_bytes < base_required {
        new_required_bytes = base_required;
    }

    if !wait_for_additional_reservation(ctx, new_required_bytes) {
        return false;
    }

    ctx.col_inds.resize(new_cap * ctx.n, 0);
    ctx.row_inds.resize(new_cap * ctx.n, 0);
    ctx.descents.resize(new_cap, 0);
    ctx.table.resize(new_cap * ctx.table_width, 0);
    ctx.weight_cache.resize(new_cap, 0);
    ctx.cache_tags.resize(new_cap, 0);
    ctx.length_parity.resize(new_cap, 0);

    let new_hash_size = next_hash_size_for_capacity(new_cap);
    if new_hash_size != ctx.hash_size {
        ctx.hash_keys = vec![-1; new_hash_size];
        ctx.hash_size = new_hash_size;
        ctx.hash_mask = new_hash_size - 1;
        for idx in 0..ctx.num_tableaux {
            hash_insert(ctx, idx);
        }
    }

    ctx.current_capacity = new_cap;
    true
}

fn alloc_graph(num_vertices: usize) -> Vec<VertexFlat> {
    vec![VertexFlat::default(); num_vertices]
}

fn clone_graph(src: &[VertexFlat]) -> Vec<VertexFlat> {
    src.to_vec()
}

fn graphs_equal(a: &[VertexFlat], b: &[VertexFlat]) -> bool {
    a == b
}

#[inline(always)]
fn push_edge(vertex: &mut VertexFlat, target: i32, weight: i32) {
    vertex.edges.push(Edge { target, weight });
}

#[inline(always)]
fn add_edge_to_graph(graph: &mut [VertexFlat], u: usize, v: usize, w: i32) {
    if u == v {
        push_edge(&mut graph[u], v as i32, w);
        return;
    }

    if u < v {
        let (left, right) = graph.split_at_mut(v);
        let vu = &mut left[u];
        let vv = &mut right[0];
        push_edge(vu, v as i32, w);
        push_edge(vv, u as i32, w);
    } else {
        let (left, right) = graph.split_at_mut(u);
        let vv = &mut left[v];
        let vu = &mut right[0];
        push_edge(vu, v as i32, w);
        push_edge(vv, u as i32, w);
    }
}

#[inline(always)]
fn get_weight_in_graph_min_scan(graph: &[VertexFlat], u: usize, v: usize) -> i32 {
    let (scan, target) = if graph[u].edges.len() <= graph[v].edges.len() {
        (&graph[u].edges, v as i32)
    } else {
        (&graph[v].edges, u as i32)
    };
    scan.iter()
        .find_map(|edge| (edge.target == target).then_some(edge.weight))
        .unwrap_or(0)
}

#[inline(always)]
fn get_weight_in_graph_min_scan_profiled(graph: &[VertexFlat], u: usize, v: usize) -> (i32, u64) {
    let (scan, target) = if graph[u].edges.len() <= graph[v].edges.len() {
        (&graph[u].edges, v as i32)
    } else {
        (&graph[v].edges, u as i32)
    };
    let mut scanned = 0u64;
    for edge in scan {
        scanned += 1;
        if edge.target == target {
            return (edge.weight, scanned);
        }
    }
    (0, scanned)
}

#[inline(always)]
pub(crate) fn checked_edge_weight(weight: i64) -> i32 {
    let weight = weight.max(0);
    i32::try_from(weight).expect("edge weight exceeds i32 range")
}

#[inline(always)]
fn phase1_edge_exists(ctx: &Context, u: usize, v: usize) -> bool {
    let source = u.min(v);
    let target = u.max(v);
    if ctx.length_parity[source] == ctx.length_parity[target] {
        return false;
    }

    let mut desc = ctx.descents[target];
    while desc != 0 {
        let s = desc.trailing_zeros() as usize;
        if s < ctx.table_width && ctx.table[ctx.table_index(target, s)] == source as i32 + 1 {
            return true;
        }
        desc &= desc - 1;
    }
    false
}

fn sort_vertex_graph(graph: &mut [VertexFlat]) {
    for vertex in graph {
        if vertex.edges.len() > 1 {
            vertex
                .edges
                .sort_unstable_by(|a, b| a.target.cmp(&b.target).then(a.weight.cmp(&b.weight)));
        }
    }
}

fn csr_from_graph(graph: &[VertexFlat]) -> GraphCsr {
    let num_vertices = graph.len();
    let mut offsets = Vec::with_capacity(num_vertices + 1);
    offsets.push(0);
    for vertex in graph {
        offsets.push(offsets.last().copied().unwrap_or(0) + vertex.edges.len());
    }

    let mut edges = Vec::with_capacity(*offsets.last().unwrap_or(&0));
    for vertex in graph {
        let begin = edges.len();
        edges.extend_from_slice(&vertex.edges);
        let end = edges.len();
        if end - begin > 1 {
            edges[begin..end]
                .sort_unstable_by(|a, b| a.target.cmp(&b.target).then(a.weight.cmp(&b.weight)));
        }
    }

    GraphCsr { offsets, edges }
}

fn graph_from_csr(csr: &GraphCsr, num_vertices: usize) -> Vec<VertexFlat> {
    let mut graph = alloc_graph(num_vertices);
    for (u, vertex) in graph.iter_mut().enumerate() {
        let begin = csr.offsets[u];
        let end = csr.offsets[u + 1];
        vertex.edges.reserve_exact(end - begin);
        vertex.edges.extend_from_slice(&csr.edges[begin..end]);
    }
    graph
}

fn csr_graphs_equal(a: &GraphCsr, b: &GraphCsr) -> bool {
    a == b
}

#[inline(always)]
fn get_weight_in_csr(graph: &GraphCsr, u: usize, v: usize) -> i32 {
    let mut lo = graph.offsets[u];
    let mut hi = graph.offsets[u + 1];

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let target = graph.edges[mid].target;
        if target < v as i32 {
            lo = mid + 1;
        } else if target > v as i32 {
            hi = mid;
        } else {
            return graph.edges[mid].weight;
        }
    }

    0
}

fn lower_partition_from_corner(
    part: &[i32; 64],
    len: usize,
    row: usize,
) -> Option<([i32; 64], usize)> {
    if row >= len || part[row] <= 0 {
        return None;
    }

    let mut lower = [0i32; 64];
    let mut lower_len = 0usize;
    for idx in 0..len {
        let mut value = part[idx];
        if idx == row {
            value -= 1;
        }
        if value > 0 {
            lower[lower_len] = value;
            lower_len += 1;
        }
    }

    Some((lower, lower_len))
}

fn read_u32_at(bytes: &[u8], offset: usize) -> io::Result<u32> {
    let slice = bytes
        .get(offset..offset + 4)
        .ok_or_else(|| io::Error::new(io::ErrorKind::UnexpectedEof, "truncated u32"))?;
    Ok(u32::from_ne_bytes(slice.try_into().unwrap()))
}

fn read_u64_at(bytes: &[u8], offset: usize) -> io::Result<u64> {
    let slice = bytes
        .get(offset..offset + 8)
        .ok_or_else(|| io::Error::new(io::ErrorKind::UnexpectedEof, "truncated u64"))?;
    Ok(u64::from_ne_bytes(slice.try_into().unwrap()))
}

#[inline(always)]
fn read_u32_unchecked(bytes: &[u8], offset: usize) -> u32 {
    debug_assert!(offset + size_of::<u32>() <= bytes.len());
    // SAFETY: callers use this only after validating the graph payload length.
    unsafe { ptr::read_unaligned(bytes.as_ptr().add(offset).cast::<u32>()) }
}

#[inline(always)]
fn read_i32_unchecked(bytes: &[u8], offset: usize) -> i32 {
    debug_assert!(offset + size_of::<i32>() <= bytes.len());
    // SAFETY: callers use this only after validating the graph payload length.
    unsafe { ptr::read_unaligned(bytes.as_ptr().add(offset).cast::<i32>()) }
}

#[inline(always)]
fn read_u64_unchecked(bytes: &[u8], offset: usize) -> u64 {
    debug_assert!(offset + size_of::<u64>() <= bytes.len());
    // SAFETY: callers use this only after validating the graph payload length.
    unsafe { ptr::read_unaligned(bytes.as_ptr().add(offset).cast::<u64>()) }
}

fn seed_restriction_edges_from_file(
    ctx: &Context,
    path: &Path,
    lower_to_full: &[usize],
    graph: &mut [VertexFlat],
    seeded_edges: &mut [Vec<Edge>],
    apply_edges: bool,
) -> io::Result<(i64, i64)> {
    let bytes = fs::read(path)?;
    if bytes.len() < size_of::<GraphFileHeader>() {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "truncated graph header",
        ));
    }

    let magic = read_u32_at(&bytes, 0)?;
    let version = read_u32_at(&bytes, 4)?;
    let partition_len = read_u32_at(&bytes, 12)? as usize;
    let num_vertices = read_u32_at(&bytes, 16)? as usize;
    let num_edges = read_u64_at(&bytes, 24)? as usize;

    if magic != GRAPH_MAGIC || !matches!(version, GRAPH_VERSION_U8_WEIGHTS | GRAPH_VERSION) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "unsupported graph file",
        ));
    }
    if num_vertices != lower_to_full.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "graph vertex count does not match lower tableau count",
        ));
    }

    let offsets_start = size_of::<GraphFileHeader>() + partition_len * size_of::<u32>();
    let targets_start = offsets_start + (num_vertices + 1) * size_of::<u64>();
    let weights_start = targets_start + num_edges * size_of::<u32>();
    let weight_size = if version == GRAPH_VERSION_U8_WEIGHTS {
        size_of::<u8>()
    } else {
        size_of::<i32>()
    };
    let weights_end = weights_start
        .checked_add(num_edges.checked_mul(weight_size).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "graph weight payload is too large",
            )
        })?)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "graph payload is too large"))?;
    if bytes.len() < weights_end {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "truncated graph payload",
        ));
    }

    let mut seeded_reserve = vec![0usize; seeded_edges.len()];
    let mut graph_reserve = if apply_edges {
        vec![0usize; graph.len()]
    } else {
        Vec::new()
    };
    for lower_u in 0..num_vertices {
        let start = read_u64_unchecked(&bytes, offsets_start + lower_u * size_of::<u64>()) as usize;
        let end =
            read_u64_unchecked(&bytes, offsets_start + (lower_u + 1) * size_of::<u64>()) as usize;
        if start > end || end > num_edges {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "graph edge offsets are out of range",
            ));
        }
        let full_u = lower_to_full[lower_u];
        for pos in start..end {
            let lower_v =
                read_u32_unchecked(&bytes, targets_start + pos * size_of::<u32>()) as usize;
            let full_v = lower_to_full[lower_v];
            seeded_reserve[full_u.max(full_v)] += 1;
            if apply_edges {
                graph_reserve[full_u] += 1;
                graph_reserve[full_v] += 1;
            }
        }
    }
    for (edges, &additional) in seeded_edges.iter_mut().zip(&seeded_reserve) {
        if additional > 0 {
            edges.reserve(additional);
        }
    }
    for (vertex, &additional) in graph.iter_mut().zip(&graph_reserve) {
        if additional > 0 {
            vertex.edges.reserve(additional);
        }
    }

    let mut added = 0i64;
    let mut added_specials = 0i64;
    for lower_u in 0..num_vertices {
        let start = read_u64_unchecked(&bytes, offsets_start + lower_u * size_of::<u64>()) as usize;
        let end =
            read_u64_unchecked(&bytes, offsets_start + (lower_u + 1) * size_of::<u64>()) as usize;
        if start > end || end > num_edges {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "graph edge offsets are out of range",
            ));
        }
        for pos in start..end {
            let lower_v =
                read_u32_unchecked(&bytes, targets_start + pos * size_of::<u32>()) as usize;
            let weight = if version == GRAPH_VERSION_U8_WEIGHTS {
                bytes[weights_start + pos] as i32
            } else {
                read_i32_unchecked(&bytes, weights_start + pos * size_of::<i32>())
            };
            let full_u = lower_to_full[lower_u];
            let full_v = lower_to_full[lower_v];
            let source = full_u.min(full_v);
            let target = full_u.max(full_v);
            seeded_edges[target].push(Edge {
                target: source as i32,
                weight,
            });

            if phase1_edge_exists(ctx, full_u, full_v) {
                if weight != 1 {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "seed edge conflicts with phase-1 graph edge",
                    ));
                }
            } else if apply_edges {
                add_edge_to_graph(graph, full_u, full_v, weight);
                added += 1;
                if weight != 1 {
                    added_specials += 1;
                }
            } else if get_weight_in_graph_min_scan(graph, full_u, full_v) != weight {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "seed edge conflicts with resumed graph edge",
                ));
            }
        }
    }

    Ok((added, added_specials))
}

fn compute_seed_component_graph(runtime: &Arc<Runtime>, task: &PartitionTask) -> io::Result<()> {
    let graph_path = runtime.paths.graph_path(task);
    if graph_path.exists() {
        return Ok(());
    }

    let mut config = runtime.config.clone();
    config.async_mode = false;
    config.force_single_partition = true;
    config.seed_restriction_load_only = true;
    config.branching_diagnostics = false;
    let child_runtime = Arc::new(Runtime::new(
        config,
        runtime.paths.clone(),
        Vec::new(),
        SchedulerCounts::default(),
    ));

    let mut ctx = Context::new(task, Arc::clone(&child_runtime));
    match generate_tableaux(&mut ctx, task, None) {
        TaskExecResult::Success => {}
        TaskExecResult::Interrupted => {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "lower tableau generation interrupted",
            ));
        }
        TaskExecResult::Failed => {
            return Err(io::Error::other("lower tableau generation failed"));
        }
    }

    let mut result = SolverResult::default();
    match compute_weighted_graph_inplace::<MainInPlace>(&mut ctx, task, &mut result, None) {
        TaskExecResult::Success => {}
        TaskExecResult::Interrupted => {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "lower graph computation interrupted",
            ));
        }
        TaskExecResult::Failed => {
            return Err(io::Error::other("lower graph computation failed"));
        }
    }

    if let Some(graph) = ctx.flat_graph.as_mut() {
        sort_vertex_graph(graph);
    }
    let fingerprint = export_csr_upper(&ctx, &graph_path)?;
    save_complete_record(&runtime.paths, task, ctx.num_tableaux, result, &fingerprint)?;
    Ok(())
}

fn compute_missing_seed_components(
    runtime: &Arc<Runtime>,
    missing_tasks: Vec<PartitionTask>,
) -> io::Result<()> {
    if missing_tasks.is_empty() {
        return Ok(());
    }

    if missing_tasks.len() == 1 || runtime.config.threads_to_use <= 1 {
        for task in missing_tasks {
            compute_seed_component_graph(runtime, &task)?;
        }
        return Ok(());
    }

    let mut results = Vec::with_capacity(missing_tasks.len());
    thread::scope(|scope| {
        let mut handles = Vec::with_capacity(missing_tasks.len());
        for task in missing_tasks {
            let runtime = Arc::clone(runtime);
            handles.push(scope.spawn(move || {
                let name = task.part_str.clone();
                (name, compute_seed_component_graph(&runtime, &task))
            }));
        }

        for handle in handles {
            results.push(handle.join().unwrap_or_else(|_| {
                (
                    "unknown".to_string(),
                    Err(io::Error::other("lower graph worker panicked")),
                )
            }));
        }
    });

    for (name, result) in results {
        if let Err(err) = result {
            return Err(io::Error::other(format!(
                "failed to compute lower graph {name}: {err}"
            )));
        }
    }

    Ok(())
}

fn seed_restriction_edges(
    ctx: &Context,
    task: &PartitionTask,
    graph: &mut [VertexFlat],
    apply_edges: bool,
) -> io::Result<(Vec<Vec<Edge>>, Vec<u16>, i64, i64)> {
    let mut seeded_edges = vec![Vec::new(); ctx.num_tableaux];
    let mut component_ids = vec![u16::MAX; ctx.num_tableaux];
    let mut seeded_count = 0i64;
    let mut seeded_specials = 0i64;
    let lower_n = task.n - 1;
    let mut components = Vec::new();

    if task.n <= 2 {
        return Ok((seeded_edges, component_ids, seeded_count, seeded_specials));
    }

    for row in 0..ctx.partition_len {
        let next = ctx.partition.get(row + 1).copied().unwrap_or(0);
        if ctx.partition[row] == next {
            continue;
        }

        let Some((lower_part, lower_len)) =
            lower_partition_from_corner(&ctx.partition, ctx.partition_len, row)
        else {
            continue;
        };
        if !is_partition_canonical_lexmax(&lower_part[..lower_len], lower_len) {
            runtime_println(
                &ctx.runtime,
                compact_log_line(
                    "seed",
                    format_args!(
                        "part={} lower={} skipped=noncanonical",
                        task.part_str,
                        partition_to_string(&lower_part, lower_len)
                    ),
                ),
            );
            continue;
        }

        let lower_dim = checked_specht_dimension(lower_n, &lower_part[..lower_len], lower_len)
            .map_err(io::Error::other)?;
        let base_required =
            estimate_context_bytes_for_capacity(lower_n, lower_dim, Phase2SolverMode::InPlace);
        let est_bytes = (base_required as f64 * MEMORY_ESTIMATE_HEADROOM) as usize;
        let lower_task = PartitionTask {
            n: lower_n,
            partition: lower_part,
            len: lower_len,
            part_str: partition_to_string(&lower_part, lower_len),
            dim_approx: lower_dim as f64,
            est_bytes: est_bytes.max(base_required),
            initial_capacity: lower_dim.max(1),
            attempts: 0,
            state: TaskState::Pending,
        };
        let graph_path = ctx.runtime.paths.graph_path(&lower_task);
        let corner_row = (row + 1) as u8;
        let corner_col = ctx.partition[row] as u8;
        let component_id = u16::try_from(components.len()).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "too many restriction components for u16 ids",
            )
        })?;
        components.push((component_id, corner_row, corner_col, lower_task, graph_path));
    }

    let missing_tasks = components
        .iter()
        .filter(|(_, _, _, _, graph_path)| !graph_path.exists())
        .map(|(_, _, _, lower_task, _)| lower_task.clone())
        .collect::<Vec<_>>();
    if !missing_tasks.is_empty() && !ctx.runtime.config.seed_restriction_load_only {
        runtime_println(
            &ctx.runtime,
            compact_log_line(
                "seed",
                format_args!(
                    "part={} compute-missing={} parallel={}",
                    task.part_str,
                    missing_tasks.len(),
                    missing_tasks.len() > 1 && ctx.runtime.config.threads_to_use > 1
                ),
            ),
        );
        compute_missing_seed_components(&ctx.runtime, missing_tasks)?;
    } else if !missing_tasks.is_empty() {
        runtime_println(
            &ctx.runtime,
            compact_log_line(
                "seed",
                format_args!(
                    "part={} cached-missing={} skipped=load-only",
                    task.part_str,
                    missing_tasks.len()
                ),
            ),
        );
    }

    for (component_id, corner_row, corner_col, lower_task, graph_path) in components {
        if !graph_path.exists() {
            if ctx.runtime.config.seed_restriction_load_only {
                continue;
            }
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("missing lower graph {}", graph_path.display()),
            ));
        }

        let mut lower_ctx = Context::with_capacity(
            &lower_task,
            Arc::clone(&ctx.runtime),
            lower_task.initial_capacity,
        );
        if generate_tableaux(&mut lower_ctx, &lower_task, None) != TaskExecResult::Success {
            return Err(io::Error::other("failed to generate lower tableaux"));
        }

        let mut lower_to_full = Vec::with_capacity(lower_ctx.num_tableaux);
        let mut full_cols = [0u8; 64];
        full_cols[lower_n] = corner_col;
        for lower_idx in 0..lower_ctx.num_tableaux {
            full_cols[..lower_n].copy_from_slice(lower_ctx.col_seq(lower_idx));
            let full_idx = hash_find(ctx, &full_cols[..task.n]);
            if full_idx < 0 {
                return Err(io::Error::other("lower tableau missing in full block"));
            }
            let full_idx = full_idx as usize;
            let seq_start = ctx.seq_offset(full_idx);
            if ctx.row_inds[seq_start + task.n - 1] != corner_row
                || ctx.col_inds[seq_start + task.n - 1] != corner_col
            {
                return Err(io::Error::other("lower tableau mapped to wrong full block"));
            }
            lower_to_full.push(full_idx);
        }

        let (added, specials) = seed_restriction_edges_from_file(
            ctx,
            &graph_path,
            &lower_to_full,
            graph,
            &mut seeded_edges,
            apply_edges,
        )?;
        for &full_idx in &lower_to_full {
            component_ids[full_idx] = component_id;
        }
        seeded_count += added;
        seeded_specials += specials;
        runtime_println(
            &ctx.runtime,
            compact_log_line(
                "seed",
                format_args!(
                    "part={} lower={} added={} path={}",
                    task.part_str,
                    lower_task.part_str,
                    added,
                    graph_path.display()
                ),
            ),
        );
    }

    for edges in &mut seeded_edges {
        if edges.len() > 1 {
            edges.sort_unstable_by_key(|edge| edge.target);
        }
    }

    Ok((seeded_edges, component_ids, seeded_count, seeded_specials))
}

#[derive(Clone, Copy, Debug)]
struct SymmetryPending {
    source: usize,
    weight: i32,
}

struct LongestWordSymmetry {
    tableau_map: Vec<usize>,
    pending: Vec<Vec<SymmetryPending>>,
    stored: u64,
    skipped: u64,
}

impl LongestWordSymmetry {
    fn mapped_candidate(&self, ctx: &Context, u: usize, t: usize) -> Option<(usize, usize)> {
        let su = self.tableau_map[u];
        let st = self.tableau_map[t];
        let (source, target) = if su < st { (su, st) } else { (st, su) };
        if source == target || ctx.max_positive_descent.get(target).copied().unwrap_or(0) == 0 {
            return None;
        }

        let des_source = ctx.descents[source];
        let des_target = ctx.descents[target];
        if ctx.length_parity[source] == ctx.length_parity[target]
            || (des_source & des_target) != des_target
            || des_source == des_target
        {
            return None;
        }

        Some((source, target))
    }

    fn store_pending(&mut self, source: usize, target: usize, weight: i32) {
        self.pending[target].push(SymmetryPending { source, weight });
        self.stored += 1;
    }
}

#[inline(always)]
fn phase2_order_before(source_a: usize, target_a: usize, source_b: usize, target_b: usize) -> bool {
    target_a < target_b || (target_a == target_b && source_a < source_b)
}

fn reverse_desc_mask(mask: u32, width: usize) -> u32 {
    let mut reversed = 0u32;
    for bit in 0..width {
        if (mask & (1u32 << bit)) != 0 {
            reversed |= 1u32 << (width - 1 - bit);
        }
    }
    reversed
}

fn build_longest_word_symmetry(ctx: &Context) -> Result<LongestWordSymmetry, String> {
    if ctx.n > MAX_SUPPORTED_N as usize || ctx.partition_len > 64 || ctx.partition[0] > 64 {
        return Err(format!(
            "longest-word symmetry supports n up to {MAX_SUPPORTED_N} with 32-bit descent masks"
        ));
    }

    let mut cell_by_pos = [[usize::MAX; 64]; 64];
    let mut cell_rows = [0u8; 64];
    let mut cell_cols = [0u8; 64];
    let mut cell_count = 0usize;

    for row in 0..ctx.partition_len {
        let row_len = ctx.partition[row] as usize;
        for col in 0..row_len {
            cell_by_pos[row][col] = cell_count;
            cell_rows[cell_count] = row as u8;
            cell_cols[cell_count] = col as u8;
            cell_count += 1;
        }
    }
    if cell_count != ctx.n {
        return Err("partition cell count does not match n".to_string());
    }

    let mut tableau_map = vec![0usize; ctx.num_tableaux];
    for t in 0..ctx.num_tableaux {
        let mut p_values = [0u8; 64];
        let mut q_values = [0u8; 64];
        let start = ctx.seq_offset(t);

        for entry in 0..ctx.n {
            let row = ctx.row_inds[start + entry] as usize - 1;
            let col = ctx.col_inds[start + entry] as usize - 1;
            let cell = cell_by_pos[row][col];
            if cell == usize::MAX {
                return Err(format!("tableau {} has entry outside partition", t + 1));
            }
            p_values[cell] = (entry + 1) as u8;
        }

        for label in (1..=ctx.n).rev() {
            let mut hole = usize::MAX;
            for (cell, &value) in p_values[..cell_count].iter().enumerate() {
                if value == 1 {
                    hole = cell;
                    break;
                }
            }
            if hole == usize::MAX {
                return Err(format!(
                    "evacuation failed to find entry 1 for tableau {}",
                    t + 1
                ));
            }
            p_values[hole] = 0;

            loop {
                let row = cell_rows[hole] as usize;
                let col = cell_cols[hole] as usize;
                let right = if col + 1 < 64 {
                    cell_by_pos[row][col + 1]
                } else {
                    usize::MAX
                };
                let down = if row + 1 < 64 {
                    cell_by_pos[row + 1][col]
                } else {
                    usize::MAX
                };
                let right_value = if right == usize::MAX {
                    0
                } else {
                    p_values[right]
                };
                let down_value = if down == usize::MAX {
                    0
                } else {
                    p_values[down]
                };

                let next = match (right_value != 0, down_value != 0) {
                    (true, true) => {
                        if right_value < down_value {
                            right
                        } else {
                            down
                        }
                    }
                    (true, false) => right,
                    (false, true) => down,
                    (false, false) => break,
                };

                p_values[hole] = p_values[next];
                p_values[next] = 0;
                hole = next;
            }

            q_values[hole] = label as u8;
            for value in &mut p_values[..cell_count] {
                if *value != 0 {
                    *value -= 1;
                }
            }
        }

        let mut evac_cols = [0u8; 64];
        for cell in 0..cell_count {
            let value = q_values[cell] as usize;
            if value == 0 {
                return Err(format!(
                    "evacuation left an empty output cell for tableau {}",
                    t + 1
                ));
            }
            evac_cols[value - 1] = cell_cols[cell] + 1;
        }

        let mapped = hash_find(ctx, &evac_cols[..ctx.n]);
        if mapped < 0 {
            return Err(format!("evacuated tableau {} was not found", t + 1));
        }
        let mapped = mapped as usize;
        let expected_desc = reverse_desc_mask(ctx.descents[t], ctx.table_width);
        if ctx.descents[mapped] != expected_desc {
            return Err(format!(
                "evacuation descent mismatch at tableau {} mapped={} got={:#x} expected={:#x}",
                t + 1,
                mapped + 1,
                ctx.descents[mapped],
                expected_desc
            ));
        }
        tableau_map[t] = mapped;
    }

    for t in 0..ctx.num_tableaux {
        let mapped = tableau_map[t];
        if tableau_map[mapped] != t {
            return Err(format!(
                "evacuation is not an involution at tableau {} mapped={}",
                t + 1,
                mapped + 1
            ));
        }
    }

    Ok(LongestWordSymmetry {
        tableau_map,
        pending: vec![Vec::new(); ctx.num_tableaux],
        stored: 0,
        skipped: 0,
    })
}

fn record_phase2_edge(
    ctx: &Context,
    graph: &mut [VertexFlat],
    result: &mut SolverResult,
    u: usize,
    t: usize,
    weight: i32,
) {
    add_edge_to_graph(graph, u, t, weight);
    result.total_edges += 1;
    if weight != 1 {
        result.special_edges += 1;
        if DEBUG_MODE {
            let _guard = ctx.runtime.print_lock.lock().unwrap();
            println!(
                "{}",
                compact_log_line(
                    "edge",
                    format_args!("kind=special src={} dst={} weight={weight}", u + 1, t + 1)
                )
            );
        }
    }
}

#[inline(always)]
fn restriction_last_descent_mask(ctx: &Context) -> Option<u32> {
    (ctx.runtime.config.seed_restriction && (2..=32).contains(&ctx.n)).then(|| 1u32 << (ctx.n - 2))
}

fn build_desc_mask_buckets(ctx: &mut Context) {
    ctx.length_parity.resize(ctx.current_capacity, 0);
    ctx.phase2_candidates = vec![0i32; ctx.num_tableaux];
    ctx.max_positive_descent = vec![0u8; ctx.num_tableaux];

    for t in 0..ctx.num_tableaux {
        let start = ctx.seq_offset(t);
        let cols = &ctx.col_inds[start..start + ctx.n];
        let rows = &ctx.row_inds[start..start + ctx.n];
        let mut parity = 0u8;

        for a in 0..ctx.n {
            let col_a = cols[a];
            let row_a = rows[a];
            for b in a + 1..ctx.n {
                parity ^= u8::from(col_a > cols[b] || (col_a == cols[b] && row_a > rows[b]));
            }
        }

        ctx.length_parity[t] = parity;
        let des_t = ctx.descents[t];
        for s in (0..ctx.table_width).rev() {
            if descent_has(des_t, s) && ctx.table[ctx.table_index(t, s)] > 0 {
                ctx.max_positive_descent[t] = (s + 1) as u8;
                break;
            }
        }
    }

    if ctx.n <= 1 || ctx.n >= 32 {
        return;
    }

    let mask_count = 1usize << ctx.table_width;
    let bucket_count = 2usize * mask_count;
    let mut counts = vec![0u32; bucket_count];
    ctx.mask_offsets = vec![0u32; bucket_count + 1];
    ctx.mask_vertices = vec![0i32; ctx.num_tableaux];

    for t in 0..ctx.num_tableaux {
        let bucket = ctx.length_parity[t] as usize * mask_count + ctx.descents[t] as usize;
        counts[bucket] += 1;
    }

    for bucket in 0..bucket_count {
        ctx.mask_offsets[bucket + 1] = ctx.mask_offsets[bucket] + counts[bucket];
    }

    let mut cursor = ctx.mask_offsets[..bucket_count].to_vec();
    for t in 0..ctx.num_tableaux {
        let bucket = ctx.length_parity[t] as usize * mask_count + ctx.descents[t] as usize;
        let pos = cursor[bucket] as usize;
        ctx.mask_vertices[pos] = t as i32;
        cursor[bucket] += 1;
    }
}

fn hash_seq(data: &[u8]) -> u32 {
    let mut hash = 2_166_136_261u32;
    for &byte in data {
        hash ^= byte as u32;
        hash = hash.wrapping_mul(16_777_619);
    }
    hash
}

fn hash_insert(ctx: &mut Context, val: usize) {
    let key_data = ctx.col_seq(val);
    let mut h = hash_seq(key_data) as usize & ctx.hash_mask;
    while ctx.hash_keys[h] != -1 {
        h = (h + 1) & ctx.hash_mask;
    }
    ctx.hash_keys[h] = val as i32;
}

fn hash_find(ctx: &Context, target_seq: &[u8]) -> i32 {
    let mut h = hash_seq(target_seq) as usize & ctx.hash_mask;
    while ctx.hash_keys[h] != -1 {
        let idx = ctx.hash_keys[h] as usize;
        if ctx.col_seq(idx) == target_seq {
            return idx as i32;
        }
        h = (h + 1) & ctx.hash_mask;
    }
    -1
}

fn should_update_progress(index: usize) -> bool {
    index == 0 || index % PROGRESS_UPDATE_STRIDE == 0
}

fn shutdown_requested(runtime: &Runtime) -> bool {
    runtime.shutdown_requested.load(Ordering::SeqCst)
}

fn current_progress_elapsed_millis(ctx: &Context) -> u64 {
    ctx.progress
        .as_ref()
        .map_or(0, TaskProgress::elapsed_millis)
}

fn save_tableaux_checkpoint(ctx: &Context, task: &PartitionTask, next_m: usize) -> io::Result<()> {
    save_checkpoint(
        &ctx.runtime.paths,
        task,
        ctx.runtime.config.phase2_solver_mode,
        PersistedContext::from_context(ctx),
        CheckpointResume::Tableaux(TableauxResume {
            next_m,
            elapsed_millis: current_progress_elapsed_millis(ctx),
        }),
    )
}

trait InPlaceFlavor {
    fn checkpoint_resume(resume: InPlaceResume) -> CheckpointResume;
}

struct MainInPlace;

impl InPlaceFlavor for MainInPlace {
    fn checkpoint_resume(resume: InPlaceResume) -> CheckpointResume {
        CheckpointResume::Phase2(Phase2Resume::InPlace(resume))
    }
}

struct CompareInPlace;

impl InPlaceFlavor for CompareInPlace {
    fn checkpoint_resume(resume: InPlaceResume) -> CheckpointResume {
        CheckpointResume::Phase2(Phase2Resume::CompareInPlace(resume))
    }
}

fn save_inplace_checkpoint<F: InPlaceFlavor>(
    ctx: &Context,
    task: &PartitionTask,
    next_t: usize,
    result: SolverResult,
    graph: &[VertexFlat],
) -> io::Result<()> {
    let resume = F::checkpoint_resume(InPlaceResume {
        next_t,
        elapsed_millis: current_progress_elapsed_millis(ctx),
        result,
        graph: graph.to_vec(),
    });
    save_checkpoint(
        &ctx.runtime.paths,
        task,
        ctx.runtime.config.phase2_solver_mode,
        PersistedContext::from_context(ctx),
        resume,
    )
}

fn save_fixed_point_checkpoint(
    ctx: &Context,
    task: &PartitionTask,
    epoch: usize,
    next_t: usize,
    epoch_result: SolverResult,
    current_snapshot: &GraphCsr,
    next_builder: &[VertexFlat],
    compare_state: Option<(&SolverResult, &[VertexFlat])>,
) -> io::Result<()> {
    let fixed_point = FixedPointResume {
        epoch,
        next_t,
        elapsed_millis: current_progress_elapsed_millis(ctx),
        epoch_result,
        current_snapshot: current_snapshot.clone(),
        next_builder: next_builder.to_vec(),
    };
    let resume = if let Some((legacy_result, legacy_graph)) = compare_state {
        CheckpointResume::Phase2(Phase2Resume::CompareFixedPoint(CompareFixedPointResume {
            legacy_result: *legacy_result,
            legacy_graph: legacy_graph.to_vec(),
            fixed_point,
        }))
    } else {
        CheckpointResume::Phase2(Phase2Resume::FixedPoint(fixed_point))
    };
    save_checkpoint(
        &ctx.runtime.paths,
        task,
        ctx.runtime.config.phase2_solver_mode,
        PersistedContext::from_context(ctx),
        resume,
    )
}

fn save_block_relaxed_checkpoint(
    ctx: &Context,
    task: &PartitionTask,
    round: usize,
    current_snapshot: &GraphCsr,
) -> io::Result<()> {
    save_checkpoint(
        &ctx.runtime.paths,
        task,
        ctx.runtime.config.phase2_solver_mode,
        PersistedContext::from_context(ctx),
        CheckpointResume::Phase2(Phase2Resume::BlockRelaxed(BlockRelaxedResume {
            round,
            elapsed_millis: current_progress_elapsed_millis(ctx),
            current_snapshot: current_snapshot.clone(),
        })),
    )
}

fn generate_tableaux(
    ctx: &mut Context,
    task: &PartitionTask,
    resume: Option<(usize, u64)>,
) -> TaskExecResult {
    if let Some(progress) = &ctx.progress {
        let (_, elapsed_millis) = resume.unwrap_or((0, 0));
        progress.set_stage(
            "tableaux",
            ctx.current_capacity as u64,
            ctx.num_tableaux as u64,
            elapsed_millis,
        );
    }

    if let Some((next_m, _)) = resume {
        let mut r_curr = [0u8; 64];
        let mut c_curr = [0u8; 64];
        let mut pcl_arr = [0i32; 64];
        return continue_tableaux_loop(ctx, task, next_m, &mut r_curr, &mut c_curr, &mut pcl_arr);
    }

    let mut dual_pi = [0i32; 64];
    let max_col = ctx.partition[0] as usize;
    for col in 0..max_col {
        for &entry in &ctx.partition[..ctx.partition_len] {
            if entry > col as i32 {
                dual_pi[col] += 1;
            }
        }
    }

    let mut r_seq = [0u8; 64];
    let mut c_seq = [0u8; 64];
    let mut k = 0usize;
    for c in 0..max_col {
        for r in 0..dual_pi[c] as usize {
            r_seq[k] = (r + 1) as u8;
            c_seq[k] = (c + 1) as u8;
            k += 1;
        }
    }

    ctx.col_inds[..ctx.n].copy_from_slice(&c_seq[..ctx.n]);
    ctx.row_inds[..ctx.n].copy_from_slice(&r_seq[..ctx.n]);
    hash_insert(ctx, 0);

    let mut desc = 0u32;
    for idx in 0..ctx.n.saturating_sub(1) {
        if r_seq[idx] < r_seq[idx + 1] {
            desc |= 1u32 << idx;
        }
    }
    ctx.descents[0] = desc;
    for idx in 0..ctx.n.saturating_sub(1) {
        if descent_has(desc, idx) {
            ctx.table[idx] = -1;
        }
    }

    ctx.num_tableaux = 1;
    let mut r_curr = [0u8; 64];
    let mut c_curr = [0u8; 64];
    let mut pcl_arr = [0i32; 64];
    continue_tableaux_loop(ctx, task, 0, &mut r_curr, &mut c_curr, &mut pcl_arr)
}

fn continue_tableaux_loop(
    ctx: &mut Context,
    task: &PartitionTask,
    mut m: usize,
    r_curr: &mut [u8; 64],
    c_curr: &mut [u8; 64],
    pcl_arr: &mut [i32; 64],
) -> TaskExecResult {
    let mut finished = false;

    while !finished {
        if shutdown_requested(&ctx.runtime) {
            return match save_tableaux_checkpoint(ctx, task, m) {
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

        if should_update_progress(m) {
            if let Some(progress) = &ctx.progress {
                progress.bar.set_length(ctx.current_capacity as u64);
                progress.update_position(ctx.num_tableaux as u64);
            }
        }

        let start = ctx.seq_offset(m);
        r_curr[..ctx.n].copy_from_slice(&ctx.row_inds[start..start + ctx.n]);
        c_curr[..ctx.n].copy_from_slice(&ctx.col_inds[start..start + ctx.n]);
        pcl_arr.fill(0);

        let mut mag_j = 1usize;
        let mut pcl_len = 1usize;
        pcl_arr[1] = 1;

        while mag_j < ctx.n {
            let c_next = c_curr[mag_j];
            let r_next = r_curr[mag_j];
            let c_prev = c_curr[mag_j - 1];
            let r_prev = r_curr[mag_j - 1];

            let cond = c_next == 1 || (c_next == c_prev + 1 && r_next == r_prev);
            if !cond {
                break;
            }

            if r_next == 1 {
                pcl_len += 1;
                pcl_arr[pcl_len] = 1;
            } else {
                pcl_arr[c_next as usize] += 1;
            }
            mag_j += 1;
        }

        if mag_j == ctx.n {
            finished = true;
        } else {
            let c_next = c_curr[mag_j];
            let r_next = r_curr[mag_j];

            if r_next == 1 {
                pcl_len += 1;
                pcl_arr[pcl_len] = 1;
            } else {
                pcl_arr[c_next as usize] += 1;
            }

            let mut k_col = c_next as usize - 1;
            while k_col > 0 && pcl_arr[k_col] == r_next as i32 {
                k_col -= 1;
            }
            pcl_arr[k_col] -= 1;

            let mut new_r = [0u8; 64];
            let mut new_c = [0u8; 64];
            let mut ptr_idx = 0usize;
            for i in 1..=pcl_len {
                for h in 1..=pcl_arr[i] as usize {
                    new_r[ptr_idx] = h as u8;
                    new_c[ptr_idx] = i as u8;
                    ptr_idx += 1;
                }
            }
            new_r[ptr_idx] = (pcl_arr[k_col] + 1) as u8;
            new_c[ptr_idx] = k_col as u8;
            ptr_idx += 1;

            for x in mag_j + 1..ctx.n {
                new_r[ptr_idx] = r_curr[x];
                new_c[ptr_idx] = c_curr[x];
                ptr_idx += 1;
            }

            if !ensure_capacity(ctx) {
                if shutdown_requested(&ctx.runtime) {
                    return match save_tableaux_checkpoint(ctx, task, m) {
                        Ok(()) => TaskExecResult::Interrupted,
                        Err(err) => {
                            runtime_println(
                                &ctx.runtime,
                                compact_log_line(
                                    "warn",
                                    format_args!(
                                        "checkpoint-save part={} err={err}",
                                        task.part_str
                                    ),
                                ),
                            );
                            TaskExecResult::Failed
                        }
                    };
                }
                return TaskExecResult::Failed;
            }

            let curr_idx = ctx.num_tableaux;
            let dst = ctx.seq_offset(curr_idx);
            ctx.row_inds[dst..dst + ctx.n].copy_from_slice(&new_r[..ctx.n]);
            ctx.col_inds[dst..dst + ctx.n].copy_from_slice(&new_c[..ctx.n]);
            hash_insert(ctx, curr_idx);
            ctx.num_tableaux += 1;

            let mut desc = 0u32;
            let mut temp_r = [0u8; 64];
            let mut temp_c = [0u8; 64];

            for idx in 0..ctx.n.saturating_sub(1) {
                let curr_table_idx = ctx.table_index(curr_idx, idx);
                if new_r[idx] == new_r[idx + 1] {
                    ctx.table[curr_table_idx] = (curr_idx + 1) as i32;
                } else if new_c[idx] == new_c[idx + 1] {
                    ctx.table[curr_table_idx] = -((curr_idx + 1) as i32);
                    desc |= 1u32 << idx;
                } else if new_r[idx] < new_r[idx + 1] {
                    desc |= 1u32 << idx;
                    temp_r[..ctx.n].copy_from_slice(&new_r[..ctx.n]);
                    temp_c[..ctx.n].copy_from_slice(&new_c[..ctx.n]);
                    temp_r.swap(idx, idx + 1);
                    temp_c.swap(idx, idx + 1);

                    let neighbor_idx = hash_find(ctx, &temp_c[..ctx.n]);
                    if neighbor_idx != -1 {
                        let neighbor = neighbor_idx as usize;
                        let neighbor_table_idx = ctx.table_index(neighbor, idx);
                        ctx.table[curr_table_idx] = neighbor_idx + 1;
                        ctx.table[neighbor_table_idx] = (curr_idx + 1) as i32;
                    }
                }
            }

            ctx.descents[curr_idx] = desc;
        }

        m += 1;
    }

    if let Some(progress) = &ctx.progress {
        progress.bar.set_length(ctx.num_tableaux as u64);
        progress.update_position(ctx.num_tableaux as u64);
    }
    ctx.flat_graph = Some(alloc_graph(ctx.num_tableaux));
    build_desc_mask_buckets(ctx);
    TaskExecResult::Success
}

fn res_num(ctx: &Context, u_idx: usize, t_idx: usize) -> usize {
    let u = ctx.col_seq(u_idx);
    let t = ctx.col_seq(t_idx);

    let mut k = 0usize;
    while k + 8 <= ctx.n {
        // SAFETY: `k + 8 <= n`, so the 8-byte reads stay within the slice bounds.
        let a = unsafe { ptr::read_unaligned(u.as_ptr().add(k).cast::<u64>()) };
        // SAFETY: `k + 8 <= n`, so the 8-byte reads stay within the slice bounds.
        let b = unsafe { ptr::read_unaligned(t.as_ptr().add(k).cast::<u64>()) };
        let diff = a ^ b;
        if diff != 0 {
            let bit_idx = diff.trailing_zeros() as usize;
            let byte_offset = bit_idx >> 3;
            let result = k + byte_offset;
            return if result < ctx.n { result } else { 0 };
        }
        k += 8;
    }

    while k < ctx.n {
        if u[k] != t[k] {
            return k;
        }
        k += 1;
    }

    0
}

fn favut(ctx: &Context, u_idx: usize, t_idx: usize, r: usize) -> Option<(usize, usize)> {
    if r == 0 {
        return None;
    }

    let x = ctx.col_seq(u_idx);
    let y = ctx.col_seq(t_idx);

    let v1 = x[r];
    let v2 = y[r];
    let mn = v1.min(v2);
    let mut mx = v1.max(v2);
    mx -= 1;

    let val_prev = x[r - 1];
    if (mn..=mx).contains(&val_prev) {
        return Some((u_idx, t_idx));
    }

    let mut s = r as i32 - 2;
    while s >= 0 {
        let idx = s as usize;
        if (mn..=mx).contains(&x[idx]) {
            break;
        }
        s -= 1;
    }
    if s < 0 {
        return None;
    }

    let s = s as usize;
    let mut z = [0u8; 64];
    z[..ctx.n].copy_from_slice(x);
    for k in s..r - 1 {
        z[k] = x[k + 1];
    }
    z[r - 1] = x[s];

    let mut zy = [0u8; 64];
    zy[..r].copy_from_slice(&z[..r]);
    zy[r..ctx.n].copy_from_slice(&y[r..ctx.n]);

    let fu = hash_find(ctx, &z[..ctx.n]);
    let ft = hash_find(ctx, &zy[..ctx.n]);
    (fu != -1 && ft != -1).then_some((fu as usize, ft as usize))
}

fn favut_profiled(
    ctx: &Context,
    u_idx: usize,
    t_idx: usize,
    r: usize,
    stats: &mut Phase2Stats,
) -> Option<(usize, usize)> {
    if r == 0 {
        stats.favut_failures += 1;
        return None;
    }

    let x = ctx.col_seq(u_idx);
    let y = ctx.col_seq(t_idx);

    let v1 = x[r];
    let v2 = y[r];
    let mn = v1.min(v2);
    let mut mx = v1.max(v2);
    mx -= 1;

    let val_prev = x[r - 1];
    if (mn..=mx).contains(&val_prev) {
        stats.favut_identity_successes += 1;
        return Some((u_idx, t_idx));
    }

    let mut s = r as i32 - 2;
    while s >= 0 {
        let idx = s as usize;
        if (mn..=mx).contains(&x[idx]) {
            break;
        }
        s -= 1;
    }
    if s < 0 {
        stats.favut_failures += 1;
        return None;
    }

    let s = s as usize;
    let mut z = [0u8; 64];
    z[..ctx.n].copy_from_slice(x);
    for k in s..r - 1 {
        z[k] = x[k + 1];
    }
    z[r - 1] = x[s];

    let mut zy = [0u8; 64];
    zy[..r].copy_from_slice(&z[..r]);
    zy[r..ctx.n].copy_from_slice(&y[r..ctx.n]);

    let fu = hash_find(ctx, &z[..ctx.n]);
    let ft = hash_find(ctx, &zy[..ctx.n]);
    if fu != -1 && ft != -1 {
        stats.favut_transform_successes += 1;
        Some((fu as usize, ft as usize))
    } else {
        stats.favut_failures += 1;
        None
    }
}

#[inline(always)]
fn bump_global_tag(ctx: &mut Context) {
    ctx.global_tag += 1;
    ctx.cached_weight_vertex = usize::MAX;
    ctx.cached_weight_edge_len = 0;
    if ctx.global_tag == i32::MAX {
        ctx.cache_tags.fill(0);
        ctx.global_tag = 1;
    }
}

#[inline(always)]
fn prepare_weight_cache(ctx: &mut Context, graph: &[VertexFlat], vertex: usize) -> bool {
    let edge_len = graph[vertex].edges.len();
    if ctx.cached_weight_vertex == vertex && ctx.cached_weight_edge_len == edge_len {
        return true;
    }

    bump_global_tag(ctx);
    for edge in &graph[vertex].edges {
        let target = edge.target as usize;
        ctx.weight_cache[target] = edge.weight;
        ctx.cache_tags[target] = ctx.global_tag;
    }
    ctx.weight_cache[vertex] = 1;
    ctx.cache_tags[vertex] = ctx.global_tag;
    ctx.cached_weight_vertex = vertex;
    ctx.cached_weight_edge_len = edge_len;
    false
}

fn build_phase1_graph(ctx: &Context, graph: &mut [VertexFlat]) -> i64 {
    let mut total_edges = 0i64;
    for t in 0..ctx.num_tableaux {
        let des_t = ctx.descents[t];
        let parity_t = ctx.length_parity[t];
        for s in 0..ctx.table_width {
            if descent_has(des_t, s) {
                let val = ctx.table[ctx.table_index(t, s)];
                if val > 0 {
                    let u = (val - 1) as usize;
                    if u < t && ctx.length_parity[u] != parity_t {
                        add_edge_to_graph(graph, u, t, 1);
                        total_edges += 1;
                    }
                }
            }
        }
    }
    total_edges
}

#[derive(Clone, Copy)]
struct RestrictionCandidateFilter<'a> {
    component_ids: &'a [u16],
    component_t: u16,
    last_descent_mask: u32,
    t_has_last_descent: bool,
}

impl<'a> RestrictionCandidateFilter<'a> {
    #[inline(always)]
    fn new(
        ctx: &Context,
        component_ids: &'a [u16],
        component_t: u16,
        last_descent_mask: u32,
        t: usize,
    ) -> Option<Self> {
        (component_t != u16::MAX).then_some(Self {
            component_ids,
            component_t,
            last_descent_mask,
            t_has_last_descent: (ctx.descents[t] & last_descent_mask) != 0,
        })
    }

    #[inline(always)]
    fn skips(self, descents: &[u32], u: usize) -> bool {
        self.component_ids[u] == self.component_t
            && (self.t_has_last_descent || (descents[u] & self.last_descent_mask) == 0)
    }
}

#[inline(always)]
fn collect_phase2_candidates(ctx: &mut Context, t: usize) -> usize {
    let mut stats = Phase2Stats::default();
    collect_phase2_candidates_impl::<false>(ctx, t, None, &mut stats)
}

#[inline(always)]
fn collect_phase2_candidates_filtered(
    ctx: &mut Context,
    t: usize,
    filter: Option<RestrictionCandidateFilter<'_>>,
) -> usize {
    let mut stats = Phase2Stats::default();
    collect_phase2_candidates_impl::<false>(ctx, t, filter, &mut stats)
}

#[inline(always)]
fn should_skip_restriction_component_candidate(
    ctx: &Context,
    component_ids: &[u16],
    component_t: u16,
    last_descent_mask: u32,
    u: usize,
    t: usize,
) -> bool {
    component_t != u16::MAX
        && component_ids[u] == component_t
        && ((ctx.descents[u] & last_descent_mask) == 0
            || (ctx.descents[t] & last_descent_mask) != 0)
}

#[inline(always)]
fn branching_diag_key(ctx: &Context, u: usize, t: usize, i: usize, j: usize) -> u64 {
    if ctx.n < 2 {
        return 0;
    }

    let last_bit = ctx.n - 2;
    let u_start = ctx.seq_offset(u);
    let t_start = ctx.seq_offset(t);
    let n_pos = ctx.n - 1;
    let n_prev = ctx.n - 2;

    let row_n = ctx.row_inds[t_start + n_pos];
    let col_n = ctx.col_inds[t_start + n_pos];
    let u_row_prev = ctx.row_inds[u_start + n_prev];
    let u_col_prev = ctx.col_inds[u_start + n_prev];
    let t_row_prev = ctx.row_inds[t_start + n_prev];
    let t_col_prev = ctx.col_inds[t_start + n_prev];

    let u_last = ctx.table[ctx.table_index(u, last_bit)];
    let t_last = ctx.table[ctx.table_index(t, last_bit)];
    let mut flags = 0u16;
    if u_last > 0 {
        flags |= 1 << 0;
    }
    if u_last.abs() - 1 == t as i32 {
        flags |= 1 << 1;
    }
    if t_last > 0 {
        flags |= 1 << 2;
    }
    if t_last.abs() - 1 == u as i32 {
        flags |= 1 << 3;
    }
    if u_col_prev == col_n {
        flags |= 1 << 4;
    }
    if t_col_prev == col_n {
        flags |= 1 << 5;
    }
    if t_row_prev == row_n {
        flags |= 1 << 6;
    }

    let du = row_n.saturating_sub(u_row_prev).min(15);
    let dt = t_row_prev.saturating_sub(row_n).min(15);
    if du == 1 && u_col_prev == col_n {
        flags |= 1 << 7;
    }
    if i == j {
        flags |= 1 << 8;
    }
    if j + 1 == ctx.n - 1 {
        flags |= 1 << 9;
    }
    if i + 1 == ctx.n - 1 {
        flags |= 1 << 10;
    }

    let i_bit = i.saturating_sub(1);
    let j_bit = j.saturating_sub(1);
    let i_mask = if i == 0 { 0 } else { 1u32 << i_bit };
    let in_diff = (ctx.descents[u] & i_mask) != 0 && (ctx.descents[t] & i_mask) == 0;
    if in_diff {
        flags |= 1 << 11;
    }
    let (ft, favut_success) = if !in_diff && i > 0 {
        if let Some((_, new_ft)) = favut(ctx, u, t, i) {
            (new_ft, true)
        } else {
            (t, false)
        }
    } else {
        (t, false)
    };
    if favut_success {
        flags |= 1 << 12;
    }
    if ft < t {
        flags |= 1 << 13;
    } else if j > 0 {
        let val_v = ctx.table[ctx.table_index(ft, j_bit)];
        let v = val_v.abs() - 1;
        if v >= 0 {
            let des_v = ctx.descents[v as usize];
            if (des_v & i_mask) != 0 {
                flags |= 1 << 14;
            }
            if i == j.saturating_sub(1) {
                flags |= 1 << 15;
            }
        }
    }

    u64::from(flags)
        | ((i.min(255) as u64) << 16)
        | ((j.min(255) as u64) << 24)
        | ((u64::from(du)) << 32)
        | ((u64::from(dt)) << 36)
}

#[inline(always)]
fn decode_branching_diag_key(key: u64) -> (u8, u8, u8, u8, u16) {
    let flags = (key & 0xffff) as u16;
    let i = ((key >> 16) & 0xff) as u8;
    let j = ((key >> 24) & 0xff) as u8;
    let du = ((key >> 32) & 0x0f) as u8;
    let dt = ((key >> 36) & 0x0f) as u8;
    (i, j, du, dt, flags)
}

fn branch_flags_to_string(flags: u16) -> String {
    const NAMES: [&str; 16] = [
        "uS+", "uS=t", "tS+", "tS=u", "uColN", "tColN", "tRowN", "uAboveN", "i=j", "j=n-2",
        "i=n-2", "fav", "favut", "direct", "iInV", "adj",
    ];
    let mut parts = Vec::new();
    for (idx, name) in NAMES.iter().enumerate() {
        if (flags & (1 << idx)) != 0 {
            parts.push(*name);
        }
    }
    if parts.is_empty() {
        "-".to_string()
    } else {
        parts.join("|")
    }
}

#[inline(always)]
fn collect_phase2_candidates_profiled(
    ctx: &mut Context,
    t: usize,
    stats: &mut Phase2Stats,
    filter: Option<RestrictionCandidateFilter<'_>>,
) -> usize {
    collect_phase2_candidates_impl::<true>(ctx, t, filter, stats)
}

#[inline(always)]
fn collect_phase2_candidates_impl<const PROFILE: bool>(
    ctx: &mut Context,
    t: usize,
    filter: Option<RestrictionCandidateFilter<'_>>,
    stats: &mut Phase2Stats,
) -> usize {
    if PROFILE {
        stats.collection_calls += 1;
    }
    let mut candidate_count = 0usize;
    let des_t = ctx.descents[t];
    // At n=32, scan vertices instead of allocating all 2^31 descent-mask buckets.
    if ctx.mask_offsets.is_empty() {
        for u in 0..t {
            let des_u = ctx.descents[u];
            if ctx.length_parity[u] == ctx.length_parity[t]
                || (des_t & des_u) != des_t
                || des_t == des_u
            {
                continue;
            }
            if filter.is_some_and(|filter| filter.skips(&ctx.descents, u)) {
                if PROFILE {
                    stats.restriction_component_skips += 1;
                }
                continue;
            }
            ctx.phase2_candidates[candidate_count] = u as i32;
            candidate_count += 1;
        }
        if PROFILE {
            stats.collected_candidates += candidate_count as u64;
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
        if PROFILE {
            stats.bucket_visits += 1;
            if start != end {
                stats.nonempty_bucket_visits += 1;
            }
        }
        for &u in &ctx.mask_vertices[start..end] {
            let u_idx = u as usize;
            if u_idx >= t {
                break;
            }
            if let Some(filter) = filter {
                if filter.skips(&ctx.descents, u_idx) {
                    if PROFILE {
                        stats.restriction_component_skips += 1;
                    }
                    continue;
                }
            }
            ctx.phase2_candidates[candidate_count] = u;
            candidate_count += 1;
        }

        extra = (extra - 1) & complement;
    }

    if candidate_count > 1 {
        if PROFILE {
            stats.sort_calls += 1;
            stats.sort_items += candidate_count as u64;
        }
        ctx.phase2_candidates[..candidate_count].sort_unstable();
    }

    if PROFILE {
        stats.collected_candidates += candidate_count as u64;
    }
    candidate_count
}

#[inline(always)]
fn evaluate_phase2_candidate(
    ctx: &mut Context,
    graph: &[VertexFlat],
    u: usize,
    t: usize,
    j: usize,
) -> i32 {
    let mut stats = Phase2Stats::default();
    evaluate_phase2_candidate_impl::<false>(ctx, graph, u, t, j, &mut stats)
}

#[inline(always)]
fn evaluate_phase2_candidate_profiled(
    ctx: &mut Context,
    graph: &[VertexFlat],
    u: usize,
    t: usize,
    j: usize,
    stats: &mut Phase2Stats,
) -> i32 {
    evaluate_phase2_candidate_impl::<true>(ctx, graph, u, t, j, stats)
}

#[inline(always)]
fn evaluate_phase2_candidate_impl<const PROFILE: bool>(
    ctx: &mut Context,
    graph: &[VertexFlat],
    u: usize,
    t: usize,
    j: usize,
    stats: &mut Phase2Stats,
) -> i32 {
    if PROFILE {
        stats.evaluated_candidates += 1;
    }
    if ctx.length_parity[u] == ctx.length_parity[t] {
        if PROFILE {
            stats.reject_same_parity += 1;
        }
        return 0;
    }

    let des_t = ctx.descents[t];
    let des_u = ctx.descents[u];
    if (des_t & des_u) != des_t || des_t == des_u {
        if PROFILE {
            stats.reject_descents += 1;
        }
        return 0;
    }

    let i = res_num(ctx, u, t);
    if i == 0 || i >= j {
        if PROFILE {
            stats.reject_resnum += 1;
        }
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
        if PROFILE {
            stats.favut_calls += 1;
        }
        let favut_result = if PROFILE {
            favut_profiled(ctx, u, t, i, stats)
        } else {
            favut(ctx, u, t, i)
        };
        if let Some((new_fu, new_ft)) = favut_result {
            fu = new_fu;
            ft = new_ft;
            if PROFILE {
                stats.favut_successes += 1;
            }
        }
    }

    let des_fu = ctx.descents[fu];
    let des_ft = ctx.descents[ft];
    let in_diff_f = (des_fu & i_mask) != 0 && (des_ft & i_mask) == 0;
    if !in_diff_f {
        if PROFILE {
            stats.reject_after_favut += 1;
        }
        return 0;
    }

    let mut weight = 0i64;
    if ft < t {
        if PROFILE {
            stats.direct_lookups += 1;
            let (found_weight, scanned) = get_weight_in_graph_min_scan_profiled(graph, ft, fu);
            weight = i64::from(found_weight);
            stats.direct_lookup_scanned_edges += scanned;
            if weight > 0 {
                stats.direct_lookup_hits += 1;
            }
        } else {
            weight = i64::from(get_weight_in_graph_min_scan(graph, ft, fu));
        }
    } else {
        if PROFILE {
            stats.recurrence_cases += 1;
        }
        let cache_reused = prepare_weight_cache(ctx, graph, fu);
        if PROFILE {
            if cache_reused {
                stats.recurrence_cache_reuses += 1;
            } else {
                stats.recurrence_cache_edges += graph[fu].edges.len() as u64;
            }
        }

        let val_v = ctx.table[ctx.table_index(ft, j_bit)];
        let v = val_v.abs() - 1;
        if v >= 0 {
            let v = v as usize;
            let des_v = ctx.descents[v];
            let i_in_des_v = (des_v & i_mask) != 0;

            if !i_in_des_v {
                let mut sumji = 0i64;
                let mut sumij = 0i64;
                if PROFILE {
                    stats.simple_cases += 1;
                    stats.simple_scanned_edges += graph[v].edges.len() as u64;
                }
                for edge in &graph[v].edges {
                    let x = edge.target as usize;
                    let w_vx = i64::from(edge.weight);
                    let w_xfu = if ctx.cache_tags[x] == ctx.global_tag {
                        i64::from(ctx.weight_cache[x])
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
                }
                weight = sumij - sumji;
            } else if i == j - 1 {
                let val_w = ctx.table[ctx.table_index(v, i_bit)];
                if val_w > 0 {
                    let w_idx = (val_w - 1) as usize;
                    let mut sumji = 0i64;
                    let sumij = 0i64;
                    if PROFILE {
                        stats.adjacent_cases += 1;
                        stats.adjacent_scanned_edges += graph[w_idx].edges.len() as u64;
                    }
                    for edge in &graph[w_idx].edges {
                        let x = edge.target as usize;
                        let w_wx = i64::from(edge.weight);
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
                            let w_yfu = if ctx.cache_tags[y_idx] == ctx.global_tag {
                                i64::from(ctx.weight_cache[y_idx])
                            } else {
                                0
                            };
                            if w_yfu != 0 {
                                sumji += w_wx * w_yfu;
                            }
                        }
                    }
                    weight = sumji - sumij;
                }
            }
        } else if PROFILE {
            stats.recurrence_missing_v += 1;
        }
    }

    let weight = checked_edge_weight(weight);
    if PROFILE {
        if weight > 0 {
            stats.positive_weights += 1;
        } else {
            stats.zero_weights += 1;
        }
    }
    weight
}

fn evaluate_phase2_candidate_csr(
    ctx: &mut Context,
    graph: &GraphCsr,
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
        weight = i64::from(get_weight_in_csr(graph, ft, fu));
    } else {
        bump_global_tag(ctx);

        for edge in &graph.edges[graph.offsets[fu]..graph.offsets[fu + 1]] {
            let target = edge.target as usize;
            ctx.weight_cache[target] = edge.weight;
            ctx.cache_tags[target] = ctx.global_tag;
        }
        ctx.weight_cache[fu] = 1;
        ctx.cache_tags[fu] = ctx.global_tag;

        let val_v = ctx.table[ctx.table_index(ft, j_bit)];
        let v = val_v.abs() - 1;
        if v >= 0 {
            let v = v as usize;
            let des_v = ctx.descents[v];
            let i_in_des_v = (des_v & i_mask) != 0;

            if !i_in_des_v {
                let mut sumji = 0i64;
                let mut sumij = 0i64;
                for edge in &graph.edges[graph.offsets[v]..graph.offsets[v + 1]] {
                    let x = edge.target as usize;
                    let w_vx = i64::from(edge.weight);
                    let w_xfu = if ctx.cache_tags[x] == ctx.global_tag {
                        i64::from(ctx.weight_cache[x])
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
                }
                weight = sumij - sumji;
            } else if i == j - 1 {
                let val_w = ctx.table[ctx.table_index(v, i_bit)];
                if val_w > 0 {
                    let w_idx = (val_w - 1) as usize;
                    let mut sumji = 0i64;
                    let sumij = 0i64;
                    for edge in &graph.edges[graph.offsets[w_idx]..graph.offsets[w_idx + 1]] {
                        let x = edge.target as usize;
                        let w_wx = i64::from(edge.weight);
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
                            let w_yfu = if ctx.cache_tags[y_idx] == ctx.global_tag {
                                i64::from(ctx.weight_cache[y_idx])
                            } else {
                                0
                            };
                            if w_yfu != 0 {
                                sumji += w_wx * w_yfu;
                            }
                        }
                    }
                    weight = sumji - sumij;
                }
            }
        }
    }

    checked_edge_weight(weight)
}

fn compute_weighted_graph_inplace<F: InPlaceFlavor>(
    ctx: &mut Context,
    task: &PartitionTask,
    result: &mut SolverResult,
    resume: Option<(usize, u64, SolverResult, Vec<VertexFlat>)>,
) -> TaskExecResult {
    let apply_seed_edges = resume.is_none();
    let (mut graph, start_t, elapsed_millis) =
        if let Some((next_t, saved_elapsed_millis, saved_result, saved_graph)) = resume {
            *result = saved_result;
            (saved_graph, next_t, saved_elapsed_millis)
        } else {
            let mut graph = ctx.flat_graph.take().unwrap_or_default();
            result.total_edges = build_phase1_graph(ctx, &mut graph);
            result.special_edges = 0;
            result.epochs = 1;
            (graph, 1, 0)
        };

    let restriction_seed = if ctx.runtime.config.seed_restriction {
        // Resumed graphs already contain seed edges; rebuild only their candidate metadata.
        match seed_restriction_edges(ctx, task, &mut graph, apply_seed_edges) {
            Ok((seeded_edges, component_ids, seeded_count, seeded_specials)) => {
                result.total_edges += seeded_count;
                result.special_edges += seeded_specials;
                Some((seeded_edges, component_ids))
            }
            Err(err) => {
                runtime_println(
                    &ctx.runtime,
                    compact_log_line(
                        "seed",
                        format_args!("part={} failed err={err}", task.part_str),
                    ),
                );
                return TaskExecResult::Failed;
            }
        }
    } else {
        None
    };
    let last_descent_mask = restriction_last_descent_mask(ctx);

    let mut longest_word_symmetry = if ctx.runtime.config.longest_word_symmetry {
        match build_longest_word_symmetry(ctx) {
            Ok(symmetry) => {
                runtime_println(
                    &ctx.runtime,
                    compact_log_line(
                        "sym",
                        format_args!(
                            "part={} kind=longest-word tableaux={}",
                            task.part_str, ctx.num_tableaux
                        ),
                    ),
                );
                Some(symmetry)
            }
            Err(err) => {
                runtime_println(
                    &ctx.runtime,
                    compact_log_line(
                        "sym",
                        format_args!("part={} failed err={err}", task.part_str),
                    ),
                );
                return TaskExecResult::Failed;
            }
        }
    } else {
        None
    };
    let mut phase2_stats = ctx.runtime.config.phase2_stats.then(Phase2Stats::default);
    let mut branching_diag = ctx
        .runtime
        .config
        .branching_diagnostics
        .then(BranchingDiagnostics::default);

    if let Some(progress) = &ctx.progress {
        progress.set_stage(
            "phase2",
            ctx.num_tableaux as u64,
            start_t as u64,
            elapsed_millis,
        );
    }

    for t in start_t..ctx.num_tableaux {
        if shutdown_requested(&ctx.runtime) {
            return match save_inplace_checkpoint::<F>(ctx, task, t, *result, &graph) {
                Ok(()) => TaskExecResult::Interrupted,
                Err(err) => {
                    runtime_println(
                        &ctx.runtime,
                        format!("Failed to save checkpoint for {}: {err}", task.part_str),
                    );
                    TaskExecResult::Failed
                }
            };
        }

        if should_update_progress(t) {
            if let Some(progress) = &ctx.progress {
                progress.update_position(t as u64);
            }
        }

        let j = ctx.max_positive_descent.get(t).copied().unwrap_or(0) as usize;
        if j == 0 {
            if let Some(stats) = phase2_stats.as_mut() {
                stats.targets_without_j += 1;
            }
            continue;
        }
        if let Some(stats) = phase2_stats.as_mut() {
            stats.targets_with_j += 1;
        }
        let component_t = restriction_seed
            .as_ref()
            .map_or(u16::MAX, |(_, component_ids)| component_ids[t]);
        let collection_filter = if branching_diag.is_none() {
            match (last_descent_mask, restriction_seed.as_ref()) {
                (Some(last_descent_mask), Some((_, component_ids))) => {
                    RestrictionCandidateFilter::new(
                        ctx,
                        component_ids,
                        component_t,
                        last_descent_mask,
                        t,
                    )
                }
                _ => None,
            }
        } else {
            None
        };
        let used_collection_restriction_filter = collection_filter.is_some();
        let candidate_count = if let Some(stats) = phase2_stats.as_mut() {
            let start = Instant::now();
            let count = collect_phase2_candidates_profiled(ctx, t, stats, collection_filter);
            stats.collection_micros += start.elapsed().as_micros();
            count
        } else {
            collect_phase2_candidates_filtered(ctx, t, collection_filter)
        };
        let mut pending_for_t = longest_word_symmetry
            .as_mut()
            .map(|symmetry| std::mem::take(&mut symmetry.pending[t]))
            .unwrap_or_default();
        if pending_for_t.len() > 1 {
            pending_for_t.sort_unstable_by_key(|entry| entry.source);
        }
        let mut pending_idx = 0usize;
        let mut same_target_pending: HashMap<usize, i32> = HashMap::new();
        let seeded_for_t = restriction_seed
            .as_ref()
            .map_or(&[][..], |(seeded_edges, _)| seeded_edges[t].as_slice());
        let mut seeded_idx = 0usize;
        let candidate_loop_start = phase2_stats.as_ref().map(|_| Instant::now());

        for idx in 0..candidate_count {
            let u = ctx.phase2_candidates[idx] as usize;
            let same_restriction_component =
                restriction_seed.as_ref().is_some_and(|(_, component_ids)| {
                    component_t != u16::MAX && component_ids[u] == component_t
                });
            if !used_collection_restriction_filter {
                if let (Some(last_descent_mask), Some((_, component_ids))) =
                    (last_descent_mask, restriction_seed.as_ref())
                {
                    if should_skip_restriction_component_candidate(
                        ctx,
                        component_ids,
                        component_t,
                        last_descent_mask,
                        u,
                        t,
                    ) {
                        if let Some(stats) = phase2_stats.as_mut() {
                            stats.restriction_component_skips += 1;
                        }
                        if let Some(diag) = branching_diag.as_mut() {
                            diag.skipped_same_component += 1;
                        }
                        continue;
                    }
                }
            }
            while seeded_idx < seeded_for_t.len() && seeded_for_t[seeded_idx].target < u as i32 {
                seeded_idx += 1;
            }
            if seeded_idx < seeded_for_t.len() && seeded_for_t[seeded_idx].target == u as i32 {
                if let Some(stats) = phase2_stats.as_mut() {
                    stats.restriction_seed_skips += 1;
                }
                if same_restriction_component {
                    if let Some(diag) = branching_diag.as_mut() {
                        diag.seeded_same_component += 1;
                    }
                }
                continue;
            }

            if let Some(symmetry) = longest_word_symmetry.as_mut() {
                while pending_idx < pending_for_t.len() && pending_for_t[pending_idx].source < u {
                    pending_idx += 1;
                }

                let pending_weight = if pending_idx < pending_for_t.len()
                    && pending_for_t[pending_idx].source == u
                {
                    let weight = pending_for_t[pending_idx].weight;
                    pending_idx += 1;
                    Some(weight)
                } else {
                    same_target_pending.remove(&u)
                };

                if let Some(weight) = pending_weight {
                    symmetry.skipped += 1;
                    if let Some(stats) = phase2_stats.as_mut() {
                        stats.symmetry_skips += 1;
                    }
                    if weight > 0 && get_weight_in_graph_min_scan(&graph, u, t) == 0 {
                        record_phase2_edge(ctx, &mut graph, result, u, t, weight);
                    }
                    continue;
                }
            }

            let diag_key = if same_restriction_component && branching_diag.is_some() {
                Some(branching_diag_key(ctx, u, t, res_num(ctx, u, t), j))
            } else {
                None
            };
            let weight = if let Some(stats) = phase2_stats.as_mut() {
                evaluate_phase2_candidate_profiled(ctx, &graph, u, t, j, stats)
            } else {
                evaluate_phase2_candidate(ctx, &graph, u, t, j)
            };
            if let (Some(diag), Some(key)) = (branching_diag.as_mut(), diag_key) {
                diag.record(key, weight);
            }
            if weight > 0 {
                record_phase2_edge(ctx, &mut graph, result, u, t, weight);

                let mapped_candidate = longest_word_symmetry
                    .as_ref()
                    .and_then(|symmetry| symmetry.mapped_candidate(ctx, u, t));
                if let Some((mapped_source, mapped_target)) = mapped_candidate {
                    if phase2_order_before(u, t, mapped_source, mapped_target) {
                        if let Some(symmetry) = longest_word_symmetry.as_mut() {
                            if mapped_target == t {
                                same_target_pending.insert(mapped_source, weight);
                                symmetry.stored += 1;
                            } else {
                                symmetry.store_pending(mapped_source, mapped_target, weight);
                            }
                        }
                    }
                }
            }
        }

        if let (Some(stats), Some(start)) = (phase2_stats.as_mut(), candidate_loop_start) {
            stats.candidate_loop_micros += start.elapsed().as_micros();
        }
    }

    if let Some(symmetry) = &longest_word_symmetry {
        runtime_println(
            &ctx.runtime,
            compact_log_line(
                "sym",
                format_args!(
                    "part={} stored={} skipped={}",
                    task.part_str, symmetry.stored, symmetry.skipped
                ),
            ),
        );
    }
    if let Some(stats) = &phase2_stats {
        print_phase2_stats(&ctx.runtime, task, stats);
    }
    if let Some(diag) = &branching_diag {
        print_branching_diagnostics(&ctx.runtime, task, diag);
    }

    if let Some(progress) = &ctx.progress {
        progress.update_position(ctx.num_tableaux as u64);
    }
    ctx.flat_graph = Some(graph);
    TaskExecResult::Success
}

fn compute_weighted_graph_fixed_point(
    ctx: &mut Context,
    task: &PartitionTask,
    result: &mut SolverResult,
    resume: Option<(usize, usize, u64, SolverResult, GraphCsr, Vec<VertexFlat>)>,
    compare_state: Option<(&SolverResult, &[VertexFlat])>,
) -> TaskExecResult {
    let (
        mut current_snapshot,
        start_epoch,
        mut resume_next_t,
        mut resume_elapsed_millis,
        mut resume_epoch_result,
        mut resume_next_builder,
    ) = if let Some((epoch, next_t, elapsed_millis, epoch_result, current_snapshot, next_builder)) =
        resume
    {
        (
            current_snapshot,
            epoch,
            next_t,
            elapsed_millis,
            Some(epoch_result),
            Some(next_builder),
        )
    } else {
        let mut builder = ctx.flat_graph.take().unwrap_or_default();
        result.total_edges = build_phase1_graph(ctx, &mut builder);
        result.special_edges = 0;
        result.epochs = 0;
        (csr_from_graph(&builder), 1, 1, 0, None, None)
    };

    for epoch in start_epoch..=ctx.runtime.config.fixed_point_max_epochs as usize {
        let mut epoch_result = if let Some(saved) = resume_epoch_result.take() {
            saved
        } else {
            SolverResult {
                total_edges: 0,
                special_edges: 0,
                epochs: epoch as i32,
            }
        };

        let mut next_builder = if let Some(saved) = resume_next_builder.take() {
            saved
        } else {
            let mut builder = alloc_graph(ctx.num_tableaux);
            epoch_result.total_edges = build_phase1_graph(ctx, &mut builder);
            builder
        };

        let start_t = resume_next_t;
        resume_next_t = 1;
        let elapsed_millis = resume_elapsed_millis;
        resume_elapsed_millis = 0;

        if let Some(progress) = &ctx.progress {
            progress.set_stage(
                &format!("fixed e{epoch}"),
                ctx.num_tableaux as u64,
                start_t as u64,
                elapsed_millis,
            );
        }

        for t in start_t..ctx.num_tableaux {
            if shutdown_requested(&ctx.runtime) {
                return match save_fixed_point_checkpoint(
                    ctx,
                    task,
                    epoch,
                    t,
                    epoch_result,
                    &current_snapshot,
                    &next_builder,
                    compare_state,
                ) {
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

            if should_update_progress(t) {
                if let Some(progress) = &ctx.progress {
                    progress.update_position(t as u64);
                }
            }

            let j = ctx.max_positive_descent.get(t).copied().unwrap_or(0) as usize;
            if j == 0 {
                continue;
            }
            let candidate_count = collect_phase2_candidates(ctx, t);

            for idx in 0..candidate_count {
                let u = ctx.phase2_candidates[idx] as usize;
                let weight = evaluate_phase2_candidate_csr(ctx, &current_snapshot, u, t, j);
                if weight > 0 {
                    add_edge_to_graph(&mut next_builder, u, t, weight);
                    epoch_result.total_edges += 1;
                    if weight != 1 {
                        epoch_result.special_edges += 1;
                        if DEBUG_MODE {
                            let _guard = ctx.runtime.print_lock.lock().unwrap();
                            println!(
                                "{}",
                                compact_log_line(
                                    "edge",
                                    format_args!(
                                        "kind=special src={} dst={} weight={weight}",
                                        u + 1,
                                        t + 1
                                    )
                                )
                            );
                        }
                    }
                }
            }
        }

        let next_snapshot = csr_from_graph(&next_builder);
        if csr_graphs_equal(&current_snapshot, &next_snapshot) {
            ctx.flat_graph = Some(graph_from_csr(&next_snapshot, ctx.num_tableaux));
            *result = epoch_result;
            if let Some(progress) = &ctx.progress {
                progress.update_position(ctx.num_tableaux as u64);
            }
            return TaskExecResult::Success;
        }

        current_snapshot = next_snapshot;
    }

    ctx.flat_graph = Some(graph_from_csr(&current_snapshot, ctx.num_tableaux));
    result.epochs = ctx.runtime.config.fixed_point_max_epochs;
    TaskExecResult::Failed
}

trait Phase2Solver {
    type Resume;
    type CompareState<'a>;

    fn run(
        ctx: &mut Context,
        task: &PartitionTask,
        result: &mut SolverResult,
        resume: Option<Self::Resume>,
        compare_state: Self::CompareState<'_>,
    ) -> TaskExecResult;

    fn failure_reason(runtime: &Runtime) -> String;
}

struct InPlacePhase2<F>(PhantomData<F>);

impl<F: InPlaceFlavor> Phase2Solver for InPlacePhase2<F> {
    type Resume = (usize, u64, SolverResult, Vec<VertexFlat>);
    type CompareState<'a> = ();

    fn run(
        ctx: &mut Context,
        task: &PartitionTask,
        result: &mut SolverResult,
        resume: Option<Self::Resume>,
        _compare_state: Self::CompareState<'_>,
    ) -> TaskExecResult {
        compute_weighted_graph_inplace::<F>(ctx, task, result, resume)
    }

    fn failure_reason(_runtime: &Runtime) -> String {
        "inplace solver failed".to_string()
    }
}

struct FixedPointPhase2;

impl Phase2Solver for FixedPointPhase2 {
    type Resume = (usize, usize, u64, SolverResult, GraphCsr, Vec<VertexFlat>);
    type CompareState<'a> = Option<(&'a SolverResult, &'a [VertexFlat])>;

    fn run(
        ctx: &mut Context,
        task: &PartitionTask,
        result: &mut SolverResult,
        resume: Option<Self::Resume>,
        compare_state: Self::CompareState<'_>,
    ) -> TaskExecResult {
        compute_weighted_graph_fixed_point(ctx, task, result, resume, compare_state)
    }

    fn failure_reason(runtime: &Runtime) -> String {
        format!(
            "fixed-point solver did not converge in {} epochs",
            runtime.config.fixed_point_max_epochs
        )
    }
}

struct BlockRelaxedPhase2;

impl Phase2Solver for BlockRelaxedPhase2 {
    type Resume = (usize, u64, GraphCsr);
    type CompareState<'a> = ();

    fn run(
        ctx: &mut Context,
        task: &PartitionTask,
        result: &mut SolverResult,
        resume: Option<Self::Resume>,
        _compare_state: Self::CompareState<'_>,
    ) -> TaskExecResult {
        newalg::compute_weighted_graph_block_relaxed(ctx, task, result, resume)
    }

    fn failure_reason(runtime: &Runtime) -> String {
        format!(
            "block-relaxed solver did not converge in {} rounds",
            runtime.config.fixed_point_max_epochs
        )
    }
}

fn interrupted_outcome(progress: &TaskProgress, reserved_bytes: usize) -> TaskProcessOutcome {
    progress.finish();
    TaskProcessOutcome {
        result: TaskExecResult::Interrupted,
        reserved_bytes,
        fail_reason: String::new(),
    }
}

fn failed_outcome(
    progress: &TaskProgress,
    reserved_bytes: usize,
    fail_reason: impl Into<String>,
) -> TaskProcessOutcome {
    progress.finish();
    TaskProcessOutcome {
        result: TaskExecResult::Failed,
        reserved_bytes,
        fail_reason: fail_reason.into(),
    }
}

fn run_phase2_solver<S: Phase2Solver>(
    ctx: &mut Context,
    task: &PartitionTask,
    progress: &TaskProgress,
    result: &mut SolverResult,
    resume: Option<S::Resume>,
    compare_state: S::CompareState<'_>,
) -> Result<f64, TaskProcessOutcome> {
    let solver_start = Instant::now();
    match S::run(ctx, task, result, resume, compare_state) {
        TaskExecResult::Success => Ok(solver_start.elapsed().as_secs_f64()),
        TaskExecResult::Interrupted => Err(interrupted_outcome(progress, ctx.reserved_bytes)),
        TaskExecResult::Failed => Err(failed_outcome(
            progress,
            ctx.reserved_bytes,
            S::failure_reason(&ctx.runtime),
        )),
    }
}

fn get_specht_dimension_approx(n: usize, part: &[i32], len: usize) -> f64 {
    let mut log_num = 0.0f64;
    for value in 2..=n {
        log_num += (value as f64).ln();
    }

    let mut conjugate = [0i32; 128];
    let max_col = part[0] as usize;
    for col in 0..max_col {
        for &entry in &part[..len] {
            if entry > col as i32 {
                conjugate[col] += 1;
            }
        }
    }

    let mut log_denom = 0.0f64;
    for row in 0..len {
        for col in 0..part[row] as usize {
            let hook_length = (part[row] - col as i32) + (conjugate[col] - row as i32) - 1;
            log_denom += (hook_length as f64).ln();
        }
    }

    (log_num - log_denom).exp()
}

#[derive(Clone, Copy)]
struct GraphFingerprint {
    state: u64,
}

impl GraphFingerprint {
    fn new() -> Self {
        Self {
            state: GRAPH_HASH_SEED,
        }
    }

    fn update(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.state ^= byte as u64;
            self.state = self.state.wrapping_mul(GRAPH_HASH_PRIME);
        }
    }

    fn short_hex(self) -> String {
        format!("{:08x}", (self.state & 0xFFFF_FFFF) as u32)
    }
}

fn write_hashed<W: Write>(
    writer: &mut W,
    hash: &mut GraphFingerprint,
    bytes: &[u8],
) -> io::Result<()> {
    writer.write_all(bytes)?;
    hash.update(bytes);
    Ok(())
}

fn export_csr_upper(ctx: &Context, filename: &Path) -> io::Result<String> {
    let graph = ctx
        .flat_graph
        .as_ref()
        .ok_or_else(|| io::Error::other("graph not built"))?;

    let num_vertices = u32::try_from(ctx.num_tableaux).map_err(|_| {
        io::Error::other(format!(
            "too many vertices for graph file target format: {}",
            ctx.num_tableaux
        ))
    })?;
    let mut degrees = vec![0u32; ctx.num_tableaux];
    let mut offsets = vec![0u64; ctx.num_tableaux + 1];

    let mut num_edges = 0u64;
    for (u, vertex) in graph.iter().enumerate() {
        for edge in &vertex.edges {
            let v = edge.target as usize;
            if u < v {
                degrees[u] += 1;
                num_edges += 1;
            }
        }
    }

    for u in 0..ctx.num_tableaux {
        offsets[u + 1] = offsets[u] + degrees[u] as u64;
    }

    let mut targets = vec![0u32; num_edges as usize];
    let mut weights = vec![0i32; num_edges as usize];
    let mut cursor = offsets[..ctx.num_tableaux].to_vec();

    for (u, vertex) in graph.iter().enumerate() {
        for edge in &vertex.edges {
            let v = edge.target as usize;
            if u < v {
                let pos = cursor[u] as usize;
                targets[pos] = v as u32;
                weights[pos] = edge.weight;
                cursor[u] += 1;
            }
        }
    }

    let mut header: GraphFileHeader = unsafe { std::mem::zeroed() };
    header.magic = GRAPH_MAGIC;
    header.version = GRAPH_VERSION;
    header.n = ctx.n as u32;
    header.partition_len = ctx.partition_len as u32;
    header.num_vertices = num_vertices;
    header.num_edges = num_edges;

    let mut part_u32 = [0u32; 64];
    for idx in 0..ctx.partition_len {
        part_u32[idx] = ctx.partition[idx] as u32;
    }

    ensure_parent_dir(filename)?;
    let tmp_path = filename.with_extension("bin.tmp");
    let mut hash = GraphFingerprint::new();

    {
        let file = File::create(&tmp_path)?;
        let mut writer = BufWriter::new(file);
        write_hashed(&mut writer, &mut hash, pod_as_bytes(&header))?;
        write_hashed(
            &mut writer,
            &mut hash,
            slice_as_bytes(&part_u32[..ctx.partition_len]),
        )?;
        write_hashed(&mut writer, &mut hash, slice_as_bytes(&offsets))?;
        if num_edges > 0 {
            write_hashed(&mut writer, &mut hash, slice_as_bytes(&targets))?;
            write_hashed(&mut writer, &mut hash, slice_as_bytes(&weights))?;
        }
        writer.flush()?;
    }
    fs::rename(tmp_path, filename)?;
    Ok(hash.short_hex())
}

fn process_partition_task(task: &PartitionTask, runtime: &Arc<Runtime>) -> TaskProcessOutcome {
    if let Ok(Some(record)) = load_complete_record(&runtime.paths, task) {
        delete_checkpoint(&runtime.paths, task);
        runtime_println(runtime, cached_summary_line(task, &record));
        return TaskProcessOutcome {
            result: TaskExecResult::Success,
            reserved_bytes: task.est_bytes,
            fail_reason: String::new(),
        };
    }

    let mut checkpoint = match load_checkpoint(&runtime.paths, task) {
        Ok(checkpoint) => checkpoint,
        Err(err) => {
            return TaskProcessOutcome {
                result: TaskExecResult::Failed,
                reserved_bytes: task.est_bytes,
                fail_reason: format!("failed to load checkpoint: {err}"),
            };
        }
    };

    if let Some(payload) = &checkpoint {
        if !payload.is_solver_compatible(runtime.config.phase2_solver_mode) {
            runtime_println(
                runtime,
                compact_log_line(
                    "warn",
                    format_args!(
                        "checkpoint-ignore part={} saved-solver={} active-solver={}",
                        task.part_str,
                        phase2_solver_name(payload.solver_mode),
                        phase2_solver_name(runtime.config.phase2_solver_mode)
                    ),
                ),
            );
            delete_checkpoint(&runtime.paths, task);
            checkpoint = None;
        }
    }

    let progress = TaskProgress::new(runtime, task);
    let mut ctx = if let Some(payload) = &checkpoint {
        payload.persisted.restore(task, Arc::clone(runtime))
    } else {
        Context::new(task, Arc::clone(runtime))
    };
    ctx.progress = Some(progress.clone());

    if DEBUG_MODE {
        runtime_println(
            runtime,
            compact_log_line("debug", format_args!("part={} n={}", task.part_str, task.n)),
        );
    }

    let mut resume_state = checkpoint.map(|payload| payload.resume);
    let tableaux_status = match resume_state.take() {
        Some(CheckpointResume::Tableaux(resume)) => {
            generate_tableaux(&mut ctx, task, Some(resume.into_tuple()))
        }
        phase2_resume @ Some(CheckpointResume::Phase2(_)) => {
            resume_state = phase2_resume;
            build_desc_mask_buckets(&mut ctx);
            TaskExecResult::Success
        }
        None => generate_tableaux(&mut ctx, task, None),
    };

    match tableaux_status {
        TaskExecResult::Success => {}
        TaskExecResult::Interrupted => return interrupted_outcome(&progress, ctx.reserved_bytes),
        TaskExecResult::Failed => {
            return failed_outcome(
                &progress,
                ctx.reserved_bytes,
                "capacity limit or memory-growth wait timeout during tableau generation",
            );
        }
    }

    let mut result = SolverResult::default();
    let mut legacy_result = SolverResult::default();
    let mut fixed_result = SolverResult::default();
    let solver_seconds;
    let mut legacy_seconds = 0.0f64;
    let mut fixed_seconds = 0.0f64;

    match runtime.config.phase2_solver_mode {
        Phase2SolverMode::InPlace => {
            let resume = match resume_state.take() {
                Some(CheckpointResume::Phase2(Phase2Resume::InPlace(resume))) => {
                    Some(resume.into_solver_resume())
                }
                _ => None,
            };
            solver_seconds = match run_phase2_solver::<InPlacePhase2<MainInPlace>>(
                &mut ctx,
                task,
                &progress,
                &mut result,
                resume,
                (),
            ) {
                Ok(seconds) => seconds,
                Err(outcome) => return outcome,
            };
        }
        Phase2SolverMode::FixedPoint => {
            let resume = match resume_state.take() {
                Some(CheckpointResume::Phase2(Phase2Resume::FixedPoint(resume))) => {
                    Some(resume.into_solver_resume())
                }
                _ => None,
            };
            solver_seconds = match run_phase2_solver::<FixedPointPhase2>(
                &mut ctx,
                task,
                &progress,
                &mut result,
                resume,
                None,
            ) {
                Ok(seconds) => seconds,
                Err(outcome) => return outcome,
            };
        }
        Phase2SolverMode::BlockRelaxed => {
            let resume = match resume_state.take() {
                Some(CheckpointResume::Phase2(Phase2Resume::BlockRelaxed(resume))) => {
                    Some(resume.into_solver_resume())
                }
                _ => None,
            };
            solver_seconds = match run_phase2_solver::<BlockRelaxedPhase2>(
                &mut ctx,
                task,
                &progress,
                &mut result,
                resume,
                (),
            ) {
                Ok(seconds) => seconds,
                Err(outcome) => return outcome,
            };
        }
        Phase2SolverMode::Compare => {
            let legacy_graph = match resume_state.take() {
                Some(CheckpointResume::Phase2(Phase2Resume::CompareFixedPoint(compare_resume))) => {
                    let (saved_legacy_result, saved_legacy_graph, fixed_resume) =
                        compare_resume.into_parts();
                    legacy_result = saved_legacy_result;
                    fixed_seconds = match run_phase2_solver::<FixedPointPhase2>(
                        &mut ctx,
                        task,
                        &progress,
                        &mut fixed_result,
                        Some(fixed_resume.into_solver_resume()),
                        Some((&legacy_result, &saved_legacy_graph)),
                    ) {
                        Ok(seconds) => seconds,
                        Err(outcome) => return outcome,
                    };
                    saved_legacy_graph
                }
                other_resume => {
                    let resume = match other_resume {
                        Some(CheckpointResume::Phase2(Phase2Resume::CompareInPlace(resume))) => {
                            Some(resume.into_solver_resume())
                        }
                        _ => None,
                    };
                    legacy_seconds = match run_phase2_solver::<InPlacePhase2<CompareInPlace>>(
                        &mut ctx,
                        task,
                        &progress,
                        &mut legacy_result,
                        resume,
                        (),
                    ) {
                        Ok(seconds) => seconds,
                        Err(outcome) => return outcome,
                    };

                    let mut legacy_graph =
                        clone_graph(ctx.flat_graph.as_ref().unwrap_or(&Vec::new()));
                    sort_vertex_graph(&mut legacy_graph);
                    ctx.flat_graph = Some(alloc_graph(ctx.num_tableaux));
                    fixed_seconds = match run_phase2_solver::<FixedPointPhase2>(
                        &mut ctx,
                        task,
                        &progress,
                        &mut fixed_result,
                        None,
                        Some((&legacy_result, &legacy_graph)),
                    ) {
                        Ok(seconds) => seconds,
                        Err(outcome) => return outcome,
                    };
                    legacy_graph
                }
            };

            if !graphs_equal(
                &legacy_graph,
                ctx.flat_graph.as_ref().unwrap_or(&Vec::new()),
            ) {
                return failed_outcome(
                    &progress,
                    ctx.reserved_bytes,
                    format!(
                        "solver mismatch: inplace edges={} specials={}, fixed-point edges={} specials={}",
                        legacy_result.total_edges,
                        legacy_result.special_edges,
                        fixed_result.total_edges,
                        fixed_result.special_edges
                    ),
                );
            }

            result = fixed_result;
            solver_seconds = fixed_seconds;
        }
    }

    if let Some(graph) = ctx.flat_graph.as_mut() {
        sort_vertex_graph(graph);
    }

    let graph_path = runtime.paths.graph_path(task);
    let fingerprint = match export_csr_upper(&ctx, &graph_path) {
        Ok(fingerprint) => fingerprint,
        Err(err) => {
            return failed_outcome(
                &progress,
                ctx.reserved_bytes,
                format!("export failed: {err}"),
            );
        }
    };

    if let Err(err) =
        save_complete_record(&runtime.paths, task, ctx.num_tableaux, result, &fingerprint)
    {
        return failed_outcome(
            &progress,
            ctx.reserved_bytes,
            format!("failed to write completion metadata: {err}"),
        );
    }

    delete_checkpoint(&runtime.paths, task);

    match runtime.config.phase2_solver_mode {
        Phase2SolverMode::Compare => {
            runtime_println(
                runtime,
                compact_log_line(
                    "cmp",
                    format_args!(
                        "part={} solver=inplace edges={} specials={} epochs={} time={:.6}s",
                        task.part_str,
                        legacy_result.total_edges,
                        legacy_result.special_edges,
                        legacy_result.epochs,
                        legacy_seconds
                    ),
                ),
            );
            runtime_println(
                runtime,
                compact_log_line(
                    "cmp",
                    format_args!(
                        "part={} solver=fixed-point edges={} specials={} epochs={} time={:.6}s match=yes fp={}",
                        task.part_str,
                        fixed_result.total_edges,
                        fixed_result.special_edges,
                        fixed_result.epochs,
                        fixed_seconds,
                        fingerprint
                    ),
                ),
            );
        }
        _ if DEBUG_MODE => {
            runtime_println(
                runtime,
                compact_log_line(
                    "debug",
                    format_args!(
                        "part={} tableaux={} edges={} specials={} solver={} time={:.6}s epochs={} fp={}",
                        task.part_str,
                        ctx.num_tableaux,
                        result.total_edges,
                        result.special_edges,
                        phase2_solver_name(runtime.config.phase2_solver_mode),
                        solver_seconds,
                        result.epochs,
                        fingerprint
                    ),
                ),
            );
        }
        _ => {
            if result.special_edges > 0 {
                runtime_println(
                    runtime,
                    compact_log_line(
                        "alert",
                        format_args!(
                            "part={} specials={} total={} solver={} epochs={} fp={} time={:.6}s",
                            task.part_str,
                            result.special_edges,
                            result.total_edges,
                            phase2_solver_name(runtime.config.phase2_solver_mode),
                            result.epochs,
                            fingerprint,
                            solver_seconds
                        ),
                    ),
                );
            } else {
                runtime_println(
                    runtime,
                    compact_log_line(
                        "done",
                        format_args!(
                            "part={} n={} dim={:.0} solver={} epochs={} fp={} time={:.6}s",
                            task.part_str,
                            task.n,
                            task.dim_approx,
                            phase2_solver_name(runtime.config.phase2_solver_mode),
                            result.epochs,
                            fingerprint,
                            solver_seconds
                        ),
                    ),
                );
            }
        }
    }

    {
        let _guard = runtime.log_lock.lock().unwrap();
        append_completed_log(
            &runtime.paths,
            task,
            ctx.num_tableaux,
            result.total_edges,
            result.special_edges,
        );
    }

    progress.finish();
    TaskProcessOutcome {
        result: TaskExecResult::Success,
        reserved_bytes: ctx.reserved_bytes,
        fail_reason: String::new(),
    }
}

fn collect_task(n: usize, part: &[i32], len: usize, tasks: &mut Vec<PartitionTask>) {
    let mut canon = [0i32; 64];
    canon[..len].copy_from_slice(&part[..len]);
    let mut canon_len = len;
    canonicalize_partition_lexmax(&mut canon, &mut canon_len);

    tasks.push(PartitionTask {
        n,
        partition: canon,
        len: canon_len,
        part_str: String::new(),
        dim_approx: 0.0,
        est_bytes: 0,
        initial_capacity: 0,
        attempts: 0,
        state: TaskState::Pending,
    });
}

fn generate_partitions_recursive(
    n: i32,
    max_val: i32,
    buffer: &mut [i32; 64],
    depth: usize,
    target_n: i32,
    tasks: &mut Vec<PartitionTask>,
) {
    if n == 0 {
        if is_partition_canonical_lexmax(&buffer[..depth], depth) {
            collect_task(target_n as usize, &buffer[..depth], depth, tasks);
        }
        return;
    }

    let start = max_val.min(n);
    for value in (1..=start).rev() {
        buffer[depth] = value;
        generate_partitions_recursive(n - value, value, buffer, depth + 1, target_n, tasks);
    }
}

fn prepare_tasks_for_run(
    tasks: &mut [PartitionTask],
    settings: &Settings,
    paths: &RuntimePaths,
) -> SchedulerCounts {
    let mut counts = SchedulerCounts::default();

    for task in tasks {
        task.part_str = partition_to_string(&task.partition, task.len);
        task.dim_approx =
            get_specht_dimension_approx(task.n, &task.partition[..task.len], task.len);
        task.initial_capacity =
            match checked_specht_dimension(task.n, &task.partition[..task.len], task.len) {
                Ok(dimension) => dimension.max(1),
                Err(reason) => {
                    eprintln!("Partition {}: {reason}", task.part_str);
                    append_failed_log(paths, task, &reason);
                    task.state = TaskState::Failed;
                    counts.failed += 1;
                    continue;
                }
            };
        task.est_bytes = estimate_context_bytes_for_capacity(
            task.n,
            task.initial_capacity,
            settings.phase2_solver_mode,
        );
        task.est_bytes = (task.est_bytes as f64 * MEMORY_ESTIMATE_HEADROOM) as usize;
        task.attempts = 0;

        if let Ok(Some(summary)) = checkpoint_summary(paths, task) {
            if summary.solver_mode == settings.phase2_solver_mode
                || summary.resume_kind == CheckpointResumeKind::Tableaux
            {
                let resume_bytes = estimate_context_bytes_for_capacity(
                    task.n,
                    summary.current_capacity.max(task.initial_capacity),
                    settings.phase2_solver_mode,
                );
                task.est_bytes = task
                    .est_bytes
                    .max((resume_bytes as f64 * MEMORY_ESTIMATE_HEADROOM) as usize);
            }
        }

        if !settings.force_single_partition {
            if load_complete_record(paths, task).ok().flatten().is_some() {
                task.state = TaskState::Skip;
                continue;
            }
        }

        task.state = TaskState::Pending;
        counts.pending += 1;
    }

    counts
}

fn try_acquire_next_task(runtime: &Arc<Runtime>) -> Option<(usize, PartitionTask)> {
    if runtime.shutdown_requested.load(Ordering::SeqCst) {
        return None;
    }

    let mut selected = None;
    let mut budget_snapshot = 0usize;

    {
        let mut state = runtime.state.lock().unwrap();
        for idx in 0..state.tasks.len() {
            if state.tasks[idx].state == TaskState::Pending {
                let budget = compute_usable_budget_bytes_unlocked(
                    state.global_reserved_bytes,
                    &runtime.config,
                );
                if state.global_reserved_bytes <= budget
                    && state.tasks[idx].est_bytes
                        <= budget.saturating_sub(state.global_reserved_bytes)
                {
                    state.global_reserved_bytes += state.tasks[idx].est_bytes;
                    state.tasks[idx].state = TaskState::Running;
                    state.tasks[idx].attempts += 1;
                    state.task_pending_count -= 1;
                    state.task_running_count += 1;
                    state.last_progress_time = Instant::now();
                    budget_snapshot = budget;
                    selected = Some((idx, state.tasks[idx].clone()));
                    break;
                }
            }
        }
    }

    if let Some((idx, task)) = selected {
        let _guard = runtime.log_lock.lock().unwrap();
        append_started_log(&runtime.paths, &task, budget_snapshot);
        Some((idx, task))
    } else {
        None
    }
}

fn acquire_synchronous_task(runtime: &Arc<Runtime>) -> Option<(usize, PartitionTask)> {
    let mut state = runtime.state.lock().unwrap();
    for idx in 0..state.tasks.len() {
        if state.tasks[idx].state == TaskState::Pending {
            state.tasks[idx].state = TaskState::Running;
            state.tasks[idx].attempts += 1;
            state.task_pending_count -= 1;
            state.task_running_count += 1;
            state.last_progress_time = Instant::now();
            return Some((idx, state.tasks[idx].clone()));
        }
    }
    None
}

fn maybe_defer_remaining_pending_tasks(runtime: &Arc<Runtime>) -> bool {
    let mut deferred = Vec::new();
    let mut budget_snapshot = 0usize;

    {
        let mut state = runtime.state.lock().unwrap();
        let timeout_elapsed = runtime.config.memory_wait_seconds >= 0
            && state.last_progress_time.elapsed()
                >= Duration::from_secs(runtime.config.memory_wait_seconds as u64);

        if state.task_pending_count > 0 && state.task_running_count == 0 && timeout_elapsed {
            budget_snapshot =
                compute_usable_budget_bytes_unlocked(state.global_reserved_bytes, &runtime.config);
            for task in &mut state.tasks {
                if task.state == TaskState::Pending {
                    task.state = TaskState::Deferred;
                    deferred.push(task.clone());
                }
            }
            state.task_deferred_count += deferred.len();
            state.task_pending_count = 0;
            state.last_progress_time = Instant::now();
        }
    }

    if deferred.is_empty() {
        return false;
    }

    let _guard = runtime.log_lock.lock().unwrap();
    for task in deferred {
        append_deferred_log(
            &runtime.paths,
            &task,
            "not enough usable RAM before timeout",
            budget_snapshot,
        );
    }
    true
}

fn finalize_task_outcome(
    runtime: &Arc<Runtime>,
    idx: usize,
    task: &PartitionTask,
    outcome: TaskProcessOutcome,
) {
    {
        let mut state = runtime.state.lock().unwrap();
        if state.tasks[idx].state == TaskState::Running {
            state.task_running_count -= 1;
            match outcome.result {
                TaskExecResult::Success => {
                    state.tasks[idx].state = TaskState::Done;
                    state.task_done_count += 1;
                }
                TaskExecResult::Interrupted => {
                    state.tasks[idx].state = TaskState::Pending;
                    state.task_pending_count += 1;
                }
                TaskExecResult::Failed => {
                    state.tasks[idx].state = TaskState::Failed;
                    state.task_failed_count += 1;
                }
            }
            state.last_progress_time = Instant::now();
        }
    }

    if outcome.result == TaskExecResult::Failed {
        let _guard = runtime.log_lock.lock().unwrap();
        append_failed_log(
            &runtime.paths,
            task,
            if outcome.fail_reason.is_empty() {
                "unknown"
            } else {
                &outcome.fail_reason
            },
        );
    }
}

fn run_synchronously(runtime: &Arc<Runtime>) {
    let Some((idx, task)) = acquire_synchronous_task(runtime) else {
        return;
    };
    let outcome = process_partition_task(&task, runtime);
    finalize_task_outcome(runtime, idx, &task, outcome);
}

fn run_scheduler(runtime: &Arc<Runtime>) {
    runtime.state.lock().unwrap().last_progress_time = Instant::now();

    thread::scope(|scope| {
        for _ in 0..runtime.config.threads_to_use {
            let runtime = Arc::clone(runtime);
            scope.spawn(move || {
                loop {
                    if let Some((idx, task)) = try_acquire_next_task(&runtime) {
                        let outcome = process_partition_task(&task, &runtime);
                        release_reserved_bytes_after_task(&runtime, outcome.reserved_bytes);
                        finalize_task_outcome(&runtime, idx, &task, outcome);

                        continue;
                    }

                    let (pending, running) = {
                        let state = runtime.state.lock().unwrap();
                        (state.task_pending_count, state.task_running_count)
                    };

                    if runtime.shutdown_requested.load(Ordering::SeqCst) {
                        if running == 0 {
                            break;
                        }
                        sleep_millis(MEMORY_POLL_MILLISECONDS);
                        continue;
                    }

                    if pending == 0 && running == 0 {
                        break;
                    }

                    if maybe_defer_remaining_pending_tasks(&runtime) {
                        break;
                    }

                    sleep_millis(MEMORY_POLL_MILLISECONDS);
                }
            });
        }
    });
}

fn phase2_solver_name(mode: Phase2SolverMode) -> &'static str {
    match mode {
        Phase2SolverMode::InPlace => "inplace",
        Phase2SolverMode::FixedPoint => "fixed-point",
        Phase2SolverMode::BlockRelaxed => "block-relaxed",
        Phase2SolverMode::Compare => "compare",
    }
}

#[inline(always)]
fn descent_has(mask: u32, bit: usize) -> bool {
    ((mask >> bit) & 1) != 0
}

fn slice_as_bytes<T>(slice: &[T]) -> &[u8] {
    // SAFETY: `slice` is a valid contiguous memory region of `size_of_val(slice)` bytes.
    unsafe { std::slice::from_raw_parts(slice.as_ptr().cast::<u8>(), size_of_val(slice)) }
}

fn pod_as_bytes<T>(value: &T) -> &[u8] {
    // SAFETY: `value` is a valid initialized POD value for raw byte serialization.
    unsafe { std::slice::from_raw_parts((value as *const T).cast::<u8>(), size_of::<T>()) }
}

fn mb(bytes: usize) -> usize {
    bytes / (1024 * 1024)
}

fn now_unix_seconds() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64
}

fn sleep_millis(ms: u64) {
    thread::sleep(Duration::from_millis(ms));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unique_test_dir(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "wgraphgen_{label}_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
        ))
    }

    fn build_test_task(partition: &[i32], settings: &Settings, dir: &Path) -> PartitionTask {
        let paths = RuntimePaths::new(dir.to_path_buf()).expect("failed to create runtime paths");
        let mut tasks = Vec::new();
        collect_task(
            partition.iter().sum::<i32>() as usize,
            partition,
            partition.len(),
            &mut tasks,
        );
        let _ = prepare_tasks_for_run(&mut tasks, settings, &paths);
        tasks.pop().expect("missing partition task")
    }

    fn build_test_runtime(settings: Settings, dir: &Path) -> Arc<Runtime> {
        let paths = RuntimePaths::new(dir.to_path_buf()).expect("failed to create runtime paths");
        Arc::new(Runtime::new(
            settings,
            paths,
            Vec::new(),
            SchedulerCounts::default(),
        ))
    }

    fn generate_test_context(task: &PartitionTask, runtime: &Arc<Runtime>) -> Context {
        let mut ctx = Context::new(task, Arc::clone(runtime));
        assert_eq!(
            generate_tableaux(&mut ctx, task, None),
            TaskExecResult::Success
        );
        ctx
    }

    fn run_inplace(partition: &[i32]) -> (SolverResult, Vec<VertexFlat>) {
        let dir = unique_test_dir("inplace");
        let settings = Settings {
            force_single_partition: true,
            threads_to_use: 1,
            output_dir: dir.clone(),
            phase2_solver_mode: Phase2SolverMode::InPlace,
            ..Settings::default()
        };
        let task = build_test_task(partition, &settings, &dir);
        let runtime = build_test_runtime(settings, &dir);
        let mut ctx = generate_test_context(&task, &runtime);
        let mut result = SolverResult::default();
        assert_eq!(
            compute_weighted_graph_inplace::<MainInPlace>(&mut ctx, &task, &mut result, None),
            TaskExecResult::Success
        );
        let mut graph = ctx.flat_graph.take().expect("missing inplace graph");
        sort_vertex_graph(&mut graph);
        let _ = fs::remove_dir_all(&dir);
        (result, graph)
    }

    fn run_block_relaxed(partition: &[i32], block_size: usize) -> (SolverResult, Vec<VertexFlat>) {
        let dir = unique_test_dir("block");
        let settings = Settings {
            force_single_partition: true,
            threads_to_use: 1,
            output_dir: dir.clone(),
            phase2_solver_mode: Phase2SolverMode::BlockRelaxed,
            phase2_block_size: block_size,
            fixed_point_max_epochs: 64,
            ..Settings::default()
        };
        let task = build_test_task(partition, &settings, &dir);
        let runtime = build_test_runtime(settings, &dir);
        let mut ctx = generate_test_context(&task, &runtime);
        let mut result = SolverResult::default();
        assert_eq!(
            newalg::compute_weighted_graph_block_relaxed(&mut ctx, &task, &mut result, None),
            TaskExecResult::Success
        );
        let mut graph = ctx.flat_graph.take().expect("missing block-relaxed graph");
        sort_vertex_graph(&mut graph);
        let _ = fs::remove_dir_all(&dir);
        (result, graph)
    }

    fn assert_block_relaxed_matches_inplace(partition: &[i32], block_size: usize) {
        let (inplace_result, inplace_graph) = run_inplace(partition);
        let (block_result, block_graph) = run_block_relaxed(partition, block_size);

        assert_eq!(block_result.total_edges, inplace_result.total_edges);
        assert_eq!(block_result.special_edges, inplace_result.special_edges);
        assert!(graphs_equal(&block_graph, &inplace_graph));
    }

    #[test]
    fn range_validation_enforces_descent_mask_bounds() {
        assert!(validate_range(1, 32).is_ok());
        for (min_n, max_n) in [(0, 8), (-1, 8), (1, 33), (33, 33), (8, 1)] {
            assert!(validate_range(min_n, max_n).is_err());
        }
    }

    #[test]
    fn partition_parser_rejects_unsupported_sizes_and_sum_overflow() {
        let mut part = [0i32; 64];
        assert_eq!(parse_partition_string("32", &mut part), Some((1, 32)));
        assert_eq!(parse_partition_string("3,2,1", &mut part), Some((3, 6)));
        for input in ["0", "33", "65", "32_1", "1_2", "2147483647_1"] {
            assert!(parse_partition_string(input, &mut part).is_none());
        }
    }

    #[test]
    fn range_tasks_do_not_skip_research_partitions() {
        let dir = unique_test_dir("no_research_skips");
        let settings = Settings::default();
        let task = build_test_task(&[6, 6, 3, 3], &settings, &dir);
        assert_eq!(task.state, TaskState::Pending);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn oversized_vertex_count_fails_before_context_allocation() {
        assert_eq!(checked_specht_dimension(6, &[3, 2, 1], 3), Ok(16));
        assert!(checked_specht_dimension(32, &[8, 8, 8, 8], 4).is_err());

        let dir = unique_test_dir("vertex_limit");
        let paths = RuntimePaths::new(dir.clone()).expect("failed to create runtime paths");
        let settings = Settings {
            force_single_partition: true,
            ..Settings::default()
        };
        let mut tasks = Vec::new();
        collect_task(32, &[8, 8, 8, 8], 4, &mut tasks);
        let counts = prepare_tasks_for_run(&mut tasks, &settings, &paths);
        assert_eq!(counts.pending, 0);
        assert_eq!(counts.failed, 1);
        assert_eq!(tasks[0].state, TaskState::Failed);
        assert_eq!(tasks[0].initial_capacity, 0);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn candidate_scan_matches_descent_buckets() {
        let dir = unique_test_dir("candidate_scan");
        let settings = Settings::default();
        let task = build_test_task(&[4, 2, 1], &settings, &dir);
        let runtime = build_test_runtime(settings, &dir);
        let mut ctx = generate_test_context(&task, &runtime);
        let expected = (0..ctx.num_tableaux)
            .map(|t| {
                let count = collect_phase2_candidates(&mut ctx, t);
                ctx.phase2_candidates[..count].to_vec()
            })
            .collect::<Vec<_>>();
        assert!(expected.iter().any(|candidates| !candidates.is_empty()));
        ctx.mask_offsets.clear();
        for (t, candidates) in expected.iter().enumerate() {
            let count = collect_phase2_candidates(&mut ctx, t);
            assert_eq!(&ctx.phase2_candidates[..count], candidates);
        }
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn n32_retains_phase2_metadata_without_dense_buckets() {
        let dir = unique_test_dir("n32");
        let settings = Settings::default();
        let task = build_test_task(&[31, 1], &settings, &dir);
        let runtime = build_test_runtime(settings, &dir);
        let ctx = generate_test_context(&task, &runtime);
        assert_eq!(ctx.full_desc_mask, 0x7fff_ffff);
        assert!(ctx.mask_offsets.is_empty());
        assert_eq!(ctx.phase2_candidates.len(), ctx.num_tableaux);
        assert_eq!(ctx.max_positive_descent.len(), ctx.num_tableaux);
        assert!(ctx.max_positive_descent.iter().any(|&j| j > 0));
        let _ = fs::remove_dir_all(&dir);
        assert_block_relaxed_matches_inplace(&[31, 1], 2);
    }

    #[test]
    fn inplace_supports_one_box_without_restriction_mask_underflow() {
        let (result, graph) = run_inplace(&[1]);
        assert_eq!(result.total_edges, 0);
        assert_eq!(graph.len(), 1);
    }

    #[test]
    fn restriction_seeded_checkpoint_resume_preserves_graph_and_counts() {
        let dir = unique_test_dir("seeded_resume");
        let settings = Settings {
            force_single_partition: true,
            threads_to_use: 1,
            seed_restriction: true,
            output_dir: dir.clone(),
            ..Settings::default()
        };
        let task = build_test_task(&[4, 3, 1], &settings, &dir);
        let runtime = build_test_runtime(settings, &dir);
        let mut baseline_ctx = generate_test_context(&task, &runtime);
        let mut expected_result = SolverResult::default();
        assert_eq!(
            compute_weighted_graph_inplace::<MainInPlace>(
                &mut baseline_ctx,
                &task,
                &mut expected_result,
                None,
            ),
            TaskExecResult::Success
        );
        let mut expected_graph = baseline_ctx
            .flat_graph
            .take()
            .expect("missing baseline graph");
        sort_vertex_graph(&mut expected_graph);

        let ctx = generate_test_context(&task, &runtime);
        let mut graph = alloc_graph(ctx.num_tableaux);
        let phase1_edges = build_phase1_graph(&ctx, &mut graph);
        let (_, _, seeded_count, seeded_specials) =
            seed_restriction_edges(&ctx, &task, &mut graph, true)
                .expect("failed to import seed edges");
        assert!(seeded_count > 0, "fixture must import non-phase1 edges");
        let saved_result = SolverResult {
            total_edges: phase1_edges + seeded_count,
            special_edges: seeded_specials,
            epochs: 1,
        };
        save_inplace_checkpoint::<MainInPlace>(&ctx, &task, 1, saved_result, &graph)
            .expect("failed to save seeded checkpoint");
        let payload = load_checkpoint(&runtime.paths, &task)
            .expect("failed to load seeded checkpoint")
            .expect("missing seeded checkpoint");
        let mut resumed_ctx = payload.persisted.restore(&task, Arc::clone(&runtime));
        build_desc_mask_buckets(&mut resumed_ctx);
        let CheckpointResume::Phase2(Phase2Resume::InPlace(resume)) = payload.resume else {
            panic!("unexpected seeded checkpoint variant");
        };
        let mut resumed_result = SolverResult::default();
        assert_eq!(
            compute_weighted_graph_inplace::<MainInPlace>(
                &mut resumed_ctx,
                &task,
                &mut resumed_result,
                Some(resume.into_solver_resume()),
            ),
            TaskExecResult::Success
        );
        let mut resumed_graph = resumed_ctx
            .flat_graph
            .take()
            .expect("missing resumed graph");
        sort_vertex_graph(&mut resumed_graph);
        assert_eq!(resumed_result.total_edges, expected_result.total_edges);
        assert_eq!(resumed_result.special_edges, expected_result.special_edges);
        assert_eq!(resumed_result.epochs, expected_result.epochs);
        assert!(graphs_equal(&resumed_graph, &expected_graph));
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn compare_checkpoint_resume_handles_both_phase2_variants() {
        for fixed_point_resume in [false, true] {
            let dir = unique_test_dir("compare_resume");
            let settings = Settings {
                force_single_partition: true,
                threads_to_use: 1,
                phase2_solver_mode: Phase2SolverMode::Compare,
                output_dir: dir.clone(),
                ..Settings::default()
            };
            let task = build_test_task(&[4, 2, 1], &settings, &dir);
            let runtime = build_test_runtime(settings, &dir);
            let mut ctx = generate_test_context(&task, &runtime);
            let mut expected_result = SolverResult::default();
            assert_eq!(
                compute_weighted_graph_inplace::<CompareInPlace>(
                    &mut ctx,
                    &task,
                    &mut expected_result,
                    None,
                ),
                TaskExecResult::Success
            );
            sort_vertex_graph(ctx.flat_graph.as_mut().expect("missing baseline graph"));
            let expected_path = dir.join("expected.bin");
            export_csr_upper(&ctx, &expected_path).expect("failed to export baseline graph");

            let mut phase1 = alloc_graph(ctx.num_tableaux);
            let phase1_result = SolverResult {
                total_edges: build_phase1_graph(&ctx, &mut phase1),
                special_edges: 0,
                epochs: 1,
            };
            if fixed_point_resume {
                save_fixed_point_checkpoint(
                    &ctx,
                    &task,
                    1,
                    1,
                    phase1_result,
                    &csr_from_graph(&phase1),
                    &phase1,
                    Some((&expected_result, ctx.flat_graph.as_ref().unwrap())),
                )
                .expect("failed to save compare fixed-point checkpoint");
            } else {
                save_inplace_checkpoint::<CompareInPlace>(&ctx, &task, 1, phase1_result, &phase1)
                    .expect("failed to save compare inplace checkpoint");
            }
            let payload = load_checkpoint(&runtime.paths, &task)
                .expect("failed to load compare checkpoint")
                .expect("missing compare checkpoint");
            let expected_kind = if fixed_point_resume {
                CheckpointResumeKind::CompareFixedPoint
            } else {
                CheckpointResumeKind::CompareInPlace
            };
            assert_eq!(payload.resume.kind(), expected_kind);

            let outcome = process_partition_task(&task, &runtime);
            assert_eq!(
                outcome.result,
                TaskExecResult::Success,
                "{}",
                outcome.fail_reason
            );
            let record = load_complete_record(&runtime.paths, &task)
                .expect("failed to load resumed completion record")
                .expect("missing resumed completion record");
            assert_eq!(record.total_edges, expected_result.total_edges);
            assert_eq!(record.special_edges, expected_result.special_edges);
            assert_eq!(
                fs::read(runtime.paths.graph_path(&task)).unwrap(),
                fs::read(&expected_path).unwrap(),
            );
            assert!(!runtime.paths.checkpoint_path(&task).exists());
            let _ = fs::remove_dir_all(&dir);
        }
    }

    #[test]
    fn block_relaxed_matches_inplace_on_small_shapes() {
        for partition in [&[3, 1][..], &[4, 2][..], &[3, 2, 1][..], &[4, 2, 1][..]] {
            assert_block_relaxed_matches_inplace(partition, 2);
        }
    }

    #[test]
    fn block_relaxed_single_block_matches_inplace() {
        assert_block_relaxed_matches_inplace(&[4, 3], usize::MAX);
    }

    #[test]
    fn graph_export_preserves_weights_above_u8() {
        let dir = unique_test_dir("wide_weight");
        let settings = Settings {
            force_single_partition: true,
            output_dir: dir.clone(),
            ..Settings::default()
        };
        let task = build_test_task(&[2], &settings, &dir);
        let runtime = build_test_runtime(settings, &dir);
        let mut ctx = Context::with_capacity(&task, runtime, 2);
        ctx.num_tableaux = 2;
        ctx.flat_graph = Some(vec![
            VertexFlat {
                edges: vec![Edge {
                    target: 1,
                    weight: 300,
                }],
            },
            VertexFlat {
                edges: vec![Edge {
                    target: 0,
                    weight: 300,
                }],
            },
        ]);

        let path = dir.join("wide_weight.bin");
        export_csr_upper(&ctx, &path).expect("failed to export graph");
        let bytes = fs::read(&path).expect("failed to read exported graph");

        assert_eq!(read_u32_at(&bytes, 0).unwrap(), GRAPH_MAGIC);
        assert_eq!(read_u32_at(&bytes, 4).unwrap(), GRAPH_VERSION);
        let partition_len = read_u32_at(&bytes, 12).unwrap() as usize;
        let num_vertices = read_u32_at(&bytes, 16).unwrap() as usize;
        let num_edges = read_u64_at(&bytes, 24).unwrap() as usize;
        assert_eq!(num_vertices, 2);
        assert_eq!(num_edges, 1);

        let offsets_start = size_of::<GraphFileHeader>() + partition_len * size_of::<u32>();
        let targets_start = offsets_start + (num_vertices + 1) * size_of::<u64>();
        let weights_start = targets_start + num_edges * size_of::<u32>();
        assert_eq!(read_i32_unchecked(&bytes, weights_start), 300);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn synchronous_mode_rejects_multiple_partitions() {
        let err =
            validate_execution_mode(&Settings::default(), 2).expect_err("expected sync error");
        assert!(err.contains("--async"));
    }

    #[test]
    fn async_mode_allows_multiple_partitions() {
        let settings = Settings {
            async_mode: true,
            ..Settings::default()
        };
        assert!(validate_execution_mode(&settings, 2).is_ok());
    }

    #[test]
    fn sqrt_progress_eta_is_longer_than_linear_at_halfway() {
        assert_eq!(estimate_sqrt_progress_eta_millis(1_000, 5, 10), 3_000);
    }

    #[test]
    fn sqrt_progress_eta_still_drops_near_completion() {
        assert_eq!(estimate_sqrt_progress_eta_millis(8_100, 9, 10), 1_900);
    }
}
