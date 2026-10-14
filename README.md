# Code and Erratum for *Exponentially large mu-coefficients*

This repository contains the Lean verification and W-graph computation programs accompanying the paper

*Exponentially large mu-coefficients*

by Tom Goertzen, Abel Lacabanne, Daniel Tubbenhauer and Pedro Vaz.

The paper constructs an explicit family of ordinary Kazhdan--Lusztig coefficients `mu = 2^r` in `S_(12+18r)`, inside a single left cell with a three-row rectangular recording tableau. The proof uses a fixed 28-dimensional interface and induction.

## Contact

If you find any errors in the paper **please email me**:

[dtubbenhauer@gmail.com](mailto:dtubbenhauer@gmail.com?subject=[GitHub]%20mu)

Same goes for any errors related to this page.

## Shoutout

The verification uses [Lean](https://lean-lang.org/) and its standard library. The W-graph programs are by Tom Goertzen and Keeley Hoek, based on Van Minh Nguyen's algorithm; see the [program README](code/WGraphCode/README.md).

## What is in this repository?

```text
code/Lean/WebMu/                  proof modules and their dependencies
code/Lean/AuditIndependentMain.lean  main theorem dependency audit
code/Lean/ASSUMPTIONS.md           mathematical inputs and computational trust
code/Lean/verify_lean.sh           build and audit command
code/WGraphCode/                  W-graph generator in C and Rust
```

The literal tensor and diagram data needed for verification are included in the Lean sources.

## Reproducing the verification

Install [Lean with elan](https://lean-lang.org/install/), then run from the repository root:

```sh
sh code/Lean/verify_lean.sh
```

The project pins Lean 4.22.0-rc2 and uses only Std. Once the toolchain is installed, it needs no network or external data. A fresh build takes several minutes.

The three main declarations in [FaithfulEndpoint.lean](code/Lean/WebMu/Revised/FaithfulEndpoint.lean) are:

- `WebMu.Revised.paper_main_faithful`
- `WebMu.Revised.paper_canonicality_faithful`
- `WebMu.Revised.paper_unbounded_faithful`

## Reproducing the W-graph computations

The generator computes weighted type A W-graphs from a partition. Its vertices are standard Young tableaux, and its positive edge weights are mu-coefficients in the corresponding cell.

With a C11 compiler, Make and OpenMP installed, run from the repository root:

```sh
cd code/WGraphCode
make c
./c/wgraphgen --partition 3_2_1 --threads 1 --dir data/c
python3 tools/graph_info.py data/c/S_6/3_2_1.bin
```

The Rust implementation, larger examples, options and tests are documented in [code/WGraphCode/README.md](code/WGraphCode/README.md). Graph inspection needs only Python 3.10 or newer. The W-graph programs run independently of the Lean project.

## Notes for the paper

The proof treats every block count by induction. Its representation theoretic inputs are explicit theorem parameters; see [ASSUMPTIONS.md](code/Lean/ASSUMPTIONS.md). Large finite checks use `native_decide`, which trusts Lean's native compiler and runtime as well as its kernel.

## Erratum

Empty so far.
