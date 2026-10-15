#!/usr/bin/env python3
"""Run C and Rust on fresh data directories and compare every weighted edge."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from graph_info import compare_graphs  # noqa: E402


PARTITIONS = (
    "3_2",
    "3_2_1",
    "4_3_2_1",
    "4_4_2_2",
    "5_5_3_3",
    "5_5_2_2_2",
    "5_5_4_3",
    "8_6_5",
)


def run_program(command: list[str], log_path: Path, timeout: int) -> float:
    started = time.monotonic()
    with log_path.open("w", encoding="utf-8") as log:
        result = subprocess.run(
            command,
            cwd=ROOT,
            stdout=log,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    if result.returncode:
        raise RuntimeError(
            f"command failed (exit {result.returncode}): {' '.join(command)}\n"
            f"See {log_path}\n{log_path.read_text()[-6000:]}"
        )
    return time.monotonic() - started


def check_cli(binary: Path, log_dir: Path, timeout: int) -> None:
    result = subprocess.run([str(binary), "--help"], capture_output=True, text=True, timeout=timeout)
    if result.returncode or "--partition" not in result.stdout + result.stderr:
        raise AssertionError(f"--help did not succeed for {binary}")
    for label, arguments in (
        ("invalid_partition", ["--partition", "3_0"]),
        ("invalid_range", ["--min-n", "8", "--max-n", "3"]),
        ("invalid_size", ["--partition", "33"]),
    ):
        directory = log_dir / label
        directory.mkdir()
        result = subprocess.run(
            [str(binary), *arguments, "--dir", str(directory)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        if result.returncode == 0:
            raise AssertionError(f"invalid arguments were accepted by {binary}: {arguments}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=Path, default=ROOT / "c" / "wgraphgen")
    parser.add_argument("--rust", type=Path, default=ROOT / "target" / "release-lto" / "wgraphgen")
    parser.add_argument("--quick", action="store_true", help="omit the last two partitions")
    parser.add_argument("--partitions", nargs="+", help="override the default partition list")
    parser.add_argument("--timeout", type=int, default=1800, help="timeout in seconds per program and partition")
    parser.add_argument("--reference-root", type=Path, help="optional directory with S_n/ or data/S_n/ reference graphs")
    args = parser.parse_args()
    c_binary, rust_binary = args.c.resolve(), args.rust.resolve()
    for binary in (c_binary, rust_binary):
        if not binary.is_file():
            raise SystemExit(f"missing executable: {binary}; run make all first")
    if args.timeout <= 0:
        raise SystemExit("timeout must be positive")
    partitions = args.partitions or list(PARTITIONS[:-2] if args.quick else PARTITIONS)
    output_root = ROOT / "test-output"
    output_root.mkdir(exist_ok=True)
    run_root = Path(tempfile.mkdtemp(prefix="comparison-", dir=output_root))
    print(f"Logs and generated graphs: {run_root}", flush=True)
    fixture_path = ROOT / "tests" / "reference_graphs.json"
    fixtures = json.loads(fixture_path.read_text()) if fixture_path.exists() else {"graphs": {}}
    report = {
        "date_utc": datetime.now(timezone.utc).isoformat(),
        "partitions": [],
        "comparison": "exact equality of every weighted edge, independent of CSR ordering",
    }

    for label, binary in (("c", c_binary), ("rust", rust_binary)):
        cli_dir = run_root / f"cli-{label}"
        cli_dir.mkdir()
        check_cli(binary, cli_dir, args.timeout)
    print("PASS command-line help and invalid-input checks", flush=True)

    for partition in partitions:
        partition_root = run_root / partition
        partition_root.mkdir()
        n = sum(map(int, partition.split("_")))
        graph_paths = {}
        elapsed = {}
        for label, binary in (("c", c_binary), ("rust", rust_binary)):
            data_dir = partition_root / label
            print(f"Running {label}: {partition}", flush=True)
            elapsed[label] = run_program(
                [str(binary), "--partition", partition, "--threads", "1", "--dir", str(data_dir)],
                partition_root / f"{label}.log",
                args.timeout,
            )
            graph_paths[label] = data_dir / f"S_{n}" / f"{partition}.bin"
            if not graph_paths[label].is_file():
                raise AssertionError(f"expected output graph missing: {graph_paths[label]}")
            print(f"Finished {label}: {partition} ({elapsed[label]:.3f}s)", flush=True)

        summary = compare_graphs(graph_paths["c"], graph_paths["rust"])
        fixture = fixtures["graphs"].get(partition)
        if fixture:
            for key, expected in fixture["summary"].items():
                if summary[key] != expected:
                    raise AssertionError(f"reference mismatch for {partition}: {key}")
        reference_matched = False
        if args.reference_root:
            reference_root = args.reference_root.resolve()
            for root in (reference_root, reference_root / "data"):
                reference_path = root / f"S_{n}" / f"{partition}.bin"
                if reference_path.is_file():
                    compare_graphs(graph_paths["rust"], reference_path)
                    reference_matched = True
                    break
        entry = {
            "partition": partition,
            **summary,
            "c_seconds": round(elapsed["c"], 6),
            "rust_seconds": round(elapsed["rust"], 6),
            "c_rust_match": True,
            "fixture_match": bool(fixture),
            "reference_file_match": reference_matched,
        }
        report["partitions"].append(entry)
        (run_root / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(
            f"PASS {partition}: vertices={summary['vertices']} edges={summary['edges']} "
            f"specials={summary['special_edges']} weights={summary['weight_counts']}",
            flush=True,
        )
    print(f"PASS all {len(partitions)} partitions. Report: {run_root / 'report.json'}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, RuntimeError, ValueError, OSError, subprocess.TimeoutExpired) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
