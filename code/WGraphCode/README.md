# WGraphGenerator

**Authors: Tom Goertzen and Keeley Hoek**

WGraphGenerator computes the weighted W-graph associated with a partition
of the symmetric group. This is based on Proposition 9.5 in Nguyen, Van Minh. Type $A$ admissible cells are Kazhdan–Lusztig. Algebraic Combinatorics, Volume 3 (2020) no. 1, pp. 55-105. doi: 10.5802/alco.91. 

The vertices of the computed W-graph correspond to standard Young tableaux. Its positive edge weights are mu-coefficients for the corresponding type A Kazhdan--Lusztig cell. This folder provides a C implementation and an optimized Rust implementation of the same algorithm.

Both programs enumerate tableaux, construct their descent and generator data, compute unit and non-unit weighted edges, and export the graph in a
compact binary format. A single partition or a range of partition sizes can be computed. All completed graphs are exported, including those with only unit weights.

On a MacBook Pro M1 with 16 GB RAM, generating and exporting the graph for `(5,5,3,3)` took **5.9 seconds in C** and **3.9 seconds in Rust**, using one thread and optimized builds. These wall-clock timings exclude compilation.

## Folder layout

```text
.
|-- README.md
|-- Cargo.toml                 Rust workspace and optimized build profiles
|-- Cargo.lock                 Pinned Rust dependencies
|-- Makefile                   Build and test both implementations
|-- c/
|   |-- Makefile
|   |-- test_wide_weight.c     Weight, overflow, and export regression test
|   `-- wgraphgen.c            C implementation with OpenMP scheduling
|-- rust/
|   |-- Cargo.toml
|   `-- src/
|       |-- main.rs            Generator, CLI, caches, and checkpoints
|       `-- newalg.rs          Experimental block-relaxed solver
|-- tools/
|   `-- graph_info.py          Validate, inspect, and compare graph files
|-- tests/
|   |-- compare_implementations.py
|   |-- check_workflows.py     Scheduling, cache, and optional solver checks
|   `-- reference_graphs.json  Expected graph statistics and checksums
`-- docs/
    |-- BINARY_FORMAT.md
    |-- VALIDATION.md
    |-- test-results.json      Recorded eight-partition comparison
    `-- workflow-results.json Recorded scheduling and solver checks
```

Run the commands below from the `WGraphCode/` directory.

## Build and run C

The C program needs a C11 compiler, Make, and OpenMP. On Linux with GCC:

```bash
make c CC=gcc
./c/wgraphgen --partition 5_5_3_3 --threads 1 --dir data/c
```

On macOS, install the OpenMP runtime and use Clang:

```bash
brew install libomp
make c CC=clang
./c/wgraphgen --partition 5_5_3_3 --threads 1 --dir data/c
```

The C Makefile locates Homebrew's `libomp`. Run `make -C c help` for build
overrides if your compiler or OpenMP installation is elsewhere.

To compute all partitions of sizes 5 through 8, up to conjugacy:

```bash
./c/wgraphgen --min-n 5 --max-n 8 --threads 4 --dir data/c
```

OpenMP workers compute different partitions. The default in-place algorithm
for one partition is sequential, so `--threads 1` is appropriate for that
mode.

## Build and run Rust

Install Rust through rustup. Rust 1.85 or later is required for edition 2024;
the included dependency lockfile must also be supported by your toolchain.

```bash
cargo build --locked --profile release-lto
cargo run --locked --profile release-lto -- --partition 5_5_3_3 --dir data/rust
```

After building, the executable can be run directly:

```bash
./target/release-lto/wgraphgen --partition 8_6_5 --dir data/rust
```

Rust range mode uses the asynchronous scheduler explicitly:

```bash
cargo run --locked --profile release-lto -- \
  --async --min-n 5 --max-n 8 --threads 4 --dir data/rust
```

The Rust implementation additionally supports local reuse of lower graphs,
an optional evacuation symmetry, progress reporting, and checkpoints. These
options retain the standard in-place solver:

```bash
./target/release-lto/wgraphgen --partition 5_5_4_3 \
  --seed-restriction --longest-word-symmetry --dir data/rust
```

`--seed-restriction` loads available graphs for removable-corner shapes of
size `n-1`; missing lower graphs are computed locally. It seeds the edges
inside restriction components and computes the remaining edges.
`--longest-word-symmetry` uses tableau evacuation to skip mirrored
candidates. Both are experimental options and are disabled by default.

Alternative Rust solvers are selected by `--phase2-solver fixed-point`,
`--phase2-solver block-relaxed`, or `--phase2-solver compare`. The last runs
the in-place and fixed-point methods and checks their graph equality.
`block-relaxed` uses `--threads` for parallel work within a partition.
These alternatives are experimental; use the default `inplace` solver for
normal generation. `--phase2-stats` prints detailed profiling counters.

## Options and output

Both executables provide their full option list with `--help`.

| Option | Meaning |
| --- | --- |
| `--partition 3_2_1` | Compute one partition, written in decreasing order |
| `--min-n A --max-n B` | Compute canonical partitions of sizes A through B |
| `--threads T` | Worker count, default 1 |
| `--dir PATH` | Output root, default `data` |
| `--memory-fraction F` | Fraction of available memory used by scheduling |
| `--memory-reserve-mb M` | Fixed memory reserve for scheduling |
| `--memory-wait-seconds S` | Wait before deferring tasks that cannot fit |

Partitions are canonicalized with their conjugates: the lexicographically
larger shape is used for computation and filenames. Input sizes satisfy
`1 <= n <= 32`, consistent with the 32-bit descent masks. Vertex indices use
signed 32-bit storage, and graph weights use signed 32-bit storage with
64-bit recurrence sums. Computations remain limited by available memory and
running time; the dimension is the number of standard tableaux of the shape.

For `--partition 5_5_3_3 --dir data/rust`, the graph is written to
`data/rust/S_16/5_5_3_3.bin`. Logs for started, completed, deferred, and failed
partitions are also stored under the selected output root.

C range runs skip entries in their completed log. Rust checks completion
metadata and an existing graph before reusing a finished computation. Rust
also saves checkpoints when interrupted with Ctrl-C; rerun the same command
with the same output directory to resume. C restarts an interrupted
partition. Use a fresh output directory for a new independent computation.

Files contain upper-triangular CSR adjacency: each edge is stored once with
`source < target`. Both programs write format version 3 with 32-bit weights.
See [the binary format](docs/BINARY_FORMAT.md) for the header and vertex
ordering.

Inspect or compare graphs with Python 3.10 or later, using only its standard
library:

```bash
python3 tools/graph_info.py data/rust/S_16/5_5_3_3.bin
python3 tools/graph_info.py data/c/S_16/5_5_3_3.bin \
  --compare data/rust/S_16/5_5_3_3.bin
```

## Tests

Build both programs, run the Rust unit tests, and compare every weighted
edge on the eight regression partitions:

```bash
make test
```

The partition list is `3_2`, `3_2_1`, `4_3_2_1`, `4_4_2_2`, `5_5_3_3`,
`5_5_2_2_2`, `5_5_4_3`, and `8_6_5`. The test runner uses fresh directories
and preserves generated graphs, logs, and a JSON report in `test-output/`.
Use `make quick-test` to omit the last two partitions. See
[validation results](docs/VALIDATION.md) for the tested reference outputs.

The full test target also exercises parallel range scheduling, completion
reuse, alternate Rust solvers on a small partition, and restriction seeding
and evacuation symmetry on `(5,5,3,3)`. The C unit test checks that a weight
of 300 survives caching and binary export, and checks recurrence overflow.

## Acknowledgements

We thank Van Minh Nguyen, who provided Magma code for the algorithm in his paper *Type A admissible cells are Kazhdan--Lusztig*, Algebraic Combinatorics, Volume 3 (2020), no. 1, pp. 55--105. His code was of substantial help in
writing this code.

The authors used several late 2025 and early 2026 ChatGPT models for assistance with writing the C and Rust code. The output of the code was compared to the output of the original Magma code.