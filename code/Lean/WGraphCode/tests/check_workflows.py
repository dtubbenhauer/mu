#!/usr/bin/env python3
"""Check range scheduling, completion reuse, and optional Rust algorithms."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile

from compare_implementations import ROOT, run_program
from graph_info import compare_graphs


def main() -> None:
    output_root = ROOT / "test-output"
    output_root.mkdir(exist_ok=True)
    run_root = Path(tempfile.mkdtemp(prefix="workflows-", dir=output_root))
    binaries = {
        "c": ROOT / "c" / "wgraphgen",
        "rust": ROOT / "target" / "release-lto" / "wgraphgen",
    }
    graph_sets = {}
    for label, binary in binaries.items():
        directory = run_root / f"range-{label}"
        command = [
            str(binary),
            "--min-n", "1", "--max-n", "6", "--threads", "2",
            "--memory-reserve-mb", "0", "--memory-wait-seconds", "0",
            "--dir", str(directory),
        ]
        if label == "rust":
            command.append("--async")
        run_program(command, run_root / f"range-{label}.log", 120)
        graph_sets[label] = {
            path.relative_to(directory) for path in directory.glob("S_*/*.bin")
        }
        if not graph_sets[label] or Path("S_1/1.bin") not in graph_sets[label]:
            raise AssertionError(f"range generation did not export the trivial graph: {label}")
        run_program(command, run_root / f"range-{label}-cached.log", 120)
        cached_log = (run_root / f"range-{label}-cached.log").read_text()
        if "done=0" not in cached_log:
            raise AssertionError(f"range completion records were not reused: {label}")
    if graph_sets["c"] != graph_sets["rust"]:
        raise AssertionError("range mode generated different sets of graph files")
    for relative in sorted(graph_sets["c"]):
        compare_graphs(run_root / "range-c" / relative, run_root / "range-rust" / relative)
    print(f"PASS parallel range generation and completion reuse: {len(graph_sets['c'])} graphs", flush=True)

    partition = "3_2_1"
    baseline = run_root / "range-rust" / "S_6" / f"{partition}.bin"
    modes = (
        ("compare", ["--phase2-solver", "compare"]),
        ("block-relaxed", ["--phase2-solver", "block-relaxed", "--phase2-block-size", "2", "--threads", "2"]),
    )
    for label, flags in modes:
        directory = run_root / label
        run_program(
            [str(binaries["rust"]), "--partition", partition, "--dir", str(directory), *flags],
            run_root / f"{label}.log",
            120,
        )
        compare_graphs(baseline, directory / "S_6" / f"{partition}.bin")
        print(f"PASS Rust {label} matches the default solver", flush=True)

    partition = "5_5_3_3"
    variants = (
        ("default", []),
        ("symmetry", ["--longest-word-symmetry"]),
        ("restriction", ["--seed-restriction"]),
        ("restriction-symmetry", ["--seed-restriction", "--longest-word-symmetry"]),
    )
    default_graph = None
    special_summary = None
    for label, flags in variants:
        directory = run_root / label
        run_program(
            [str(binaries["rust"]), "--partition", partition, "--threads", "2", "--dir", str(directory), *flags],
            run_root / f"{label}.log",
            1800,
        )
        graph = directory / "S_16" / f"{partition}.bin"
        if label == "default":
            default_graph = graph
        special_summary = compare_graphs(default_graph, graph)
        print(f"PASS Rust {label}: every weighted edge matches on {partition}", flush=True)
    if special_summary["weight_counts"] != {"1": 2076821, "5": 16}:
        raise AssertionError("optional Rust workflows disagree with the known weight distribution")

    report = {
        "range_graphs_matched": len(graph_sets["c"]),
        "completion_reuse_passed": True,
        "small_solver_variants": [label for label, _ in modes],
        "special_edge_variants": [label for label, _ in variants],
        "special_graph_summary": special_summary,
    }
    (run_root / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"PASS all workflow checks. Report: {run_root / 'report.json'}", flush=True)


if __name__ == "__main__":
    main()
