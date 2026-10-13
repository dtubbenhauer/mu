# Code and Erratum for *Exponentially large mu-coefficients*

This repository contains code and data for the computations and Lean verification accompanying the paper

*Exponentially large mu-coefficients*

by Tom Goertzen, Abel Lacabanne, Daniel Tubbenhauer and Pedro Vaz.

The paper constructs an explicit family of ordinary Kazhdan--Lusztig coefficients `mu = 2^r` in `S_(12+18r)`. The two permutations lie in the same left cell, with a rectangular recording tableau with three rows. The proof uses a fixed 28-dimensional interface, local tensor calculations and induction.

## Contact

If you find any errors in the paper **please email me**:

[dtubbenhauer@gmail.com](mailto:dtubbenhauer@gmail.com?subject=[GitHub]%20mu)

Same goes for any errors related to this page.

## Shoutout

The formal verification uses [Lean](https://lean-lang.org/) and its standard library. The supporting computations and figures use [SymPy](https://www.sympy.org/), [NumPy](https://numpy.org/), [NetworkX](https://networkx.org/) and [Matplotlib](https://matplotlib.org/).

## What is in this repository?

```text
code/Lean/                    standalone Lean project, audits and verification records
code/revision-audit/          exact local proof, selected rows and spider atlas checks
code/RevisedProofStrategy/    tensor and diagram calculations and saved certificates
code/WebMuUnboundedness/      Laurent arithmetic, tableaux, webs and graph routines
code/WGraphs/                 supporting permutation and web data
code/Paper/                   example checks, correction data and figure sources
figures/                      publication figures in PDF format
```

The main entry points are [code/Lean/verify_lean.sh](code/Lean/verify_lean.sh) and [code/verify.py](code/verify.py). The original relative paths are preserved so that the programs can find their supporting modules and data.

## Reproducing the Lean verification

Install [Lean with elan](https://lean-lang.org/install/), then run from the repository root:

```sh
sh code/Lean/verify_lean.sh
```

The project pins Lean 4.22.0-rc2 and uses only Std. Once the toolchain is installed, it needs no network, Python or external data. The script builds the library and runs all nine audit entry points. A fresh build takes several minutes; no build cache is included.

The preferred declarations are `WebMu.Revised.paper_main_faithful`, `WebMu.Revised.paper_canonicality_faithful` and `WebMu.Revised.paper_unbounded_faithful` in [FaithfulEndpoint.lean](code/Lean/WebMu/Revised/FaithfulEndpoint.lean). See [COVERAGE.md](code/Lean/COVERAGE.md) for the correspondence with the paper and [verification/summary.json](code/Lean/verification/summary.json) for the supplied verification record.

## Reproducing the calculations

An independent finite check needs only Python's standard library:

```sh
python3 -I code/verify.py independent
```

For the other Python calculations, use Python 3.10 or newer and install the dependencies:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r code/requirements.txt
python3 -I code/verify.py quick
```

Run all commands from the repository root:

| Command | Checks |
| --- | --- |
| `python3 -I code/verify.py local` | Local degree bounds, transformed block rows and ends |
| `python3 -I code/verify.py rows` | Prefix covectors and the two complete coefficient rows |
| `python3 -I code/verify.py atlas` | Square and digon reductions and the terminal maps |
| `python3 -I code/verify.py quick` | File hashes, package contents, tableau conventions and figure data |
| `python3 -I code/verify.py family` | Prefix Gram entries, initial data and pairing seeds |
| `python3 -I code/verify.py examples` | Six-point, one-block and two-block examples |
| `python3 -I code/verify.py lower` | All 94 lower webs and the complete corrected two-block column |
| `python3 -I code/verify.py norm` | Norm transfer, Gram lattice and end contractions |
| `python3 -I code/verify.py closed` | Closed diagrams, tensor contractions and source readout |
| `python3 -I code/verify.py manifest` | SHA256 hashes of the supplied files |

`python3 -I code/verify.py all` runs all Python groups, including the longer norm calculations. The Lean build is separate. The tensor calculations use exact arithmetic.

## Data and figures

The most useful saved data are:

- [shift9_cap_m2_red_correction.json](code/RevisedProofStrategy/computations/shift9_cap_m2_red_correction.json): the 30-point two-block correction, with all 94 lower terms. The filename comes from the discovery calculation.
- [lower-terms-checks.json](code/Paper/dani-revision/lower-terms-checks.json): the complete corrected tensor column and lower-web coordinates.
- [norm-transfer-probe.json](code/Paper/human-readable-finite-proof/norm-transfer-probe.json): the norm transfer and integral lattice; use `integral_lattice.K` for the integral basis.
- [cap_closed_source_readout.json](code/RevisedProofStrategy/computations/cap_closed_source_readout.json): the closed-diagram readout.

The editable SVGs and graph metadata are under `code/Paper/`. To regenerate the available figures, also install `rsvg-convert` from [librsvg](https://gitlab.gnome.org/GNOME/librsvg), then run:

```sh
python3 -I code/verify.py figures
```

Figure generation writes SVG, JSON and rendered figures in the corresponding source folders, and updates the example PDFs in `figures/`. After deliberately changing files or regenerating data, refresh the checksums with:

```sh
python3 -I code/Paper/dani-revision/update_manifest.py
```

## Notes for the paper

The Lean proof treats every block count by induction. The representation-theoretic results used in the proof are explicit mathematical inputs, listed in [ASSUMPTIONS.md](code/Lean/ASSUMPTIONS.md). Large finite checks use `native_decide`, which trusts Lean's native compiler and runtime as well as its kernel.

The independent Python check reconstructs the primitive maps and selected contractions for block counts 0--20, and checks the permutations and RSK for block counts 0--40. These finite checks supplement the all-parameter Lean proof.

## Erratum

Empty so far.
