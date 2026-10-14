# Validation

All eight requested partition comparisons passed on 14 October 2026.
Recorded results are in `test-results.json` and `workflow-results.json`.

Validation is run on the cleaned C and Rust implementations, with fresh
output directories so that completed graphs cannot hide a computation.
The test runner compares every weighted edge, independently of CSR target
ordering. Reference checksums use the canonical encoding implemented in
`tools/graph_info.py`.

## Reference graphs

| Partition | Vertices | Stored edges | Non-unit edges |
| --- | ---: | ---: | --- |
| `3_2` | 5 | 6 | None |
| `3_2_1` | 16 | 32 | None |
| `4_3_2_1` | 768 | 3,814 | None |
| `4_4_2_2` | 2,640 | 17,056 | None |
| `5_5_3_3` | 171,600 | 2,076,837 | 16 edges of weight 5 |
| `5_5_2_2_2` | 250,250 | 2,698,722 | 24 edges of weight 2 |
| `5_5_4_3` | 583,440 | 8,496,063 | 80 edges of weight 5 |
| `8_6_5` | 1,662,804 | 22,560,347 | 44 edges of weight 5 |

The first four reference summaries were established by direct C-versus-Rust
comparison. The last four come from pre-existing local binary graphs, and
the new outputs are additionally compared with those reference files.
`tests/reference_graphs.json` records these distinctions and checksums.
The historical comparison with the original Magma code is acknowledged in
the README; the automated tests in this repository exercise C, Rust, and
the saved references.

## Additional checks

- Sixteen Rust unit tests cover the solver variants, parser and dimension
  bounds, descent-bucket fallback, the one-box case, wide-weight export,
  and checkpoint resumption with restriction seeding and solver comparison.
- The C unit test verifies weight-300 caching and binary export, canonical
  CSR ordering, and checked 64-bit recurrence arithmetic.
- Both executables are checked for successful help output and rejection
  of invalid partitions, reversed ranges, and unsupported sizes.
- Parallel range runs for sizes 1 through 6 generate the same 17 canonical
  graphs in C and Rust, and repeat runs reuse completion records.
- Rust fixed-point comparison and block-relaxed modes agree with the
  default solver on `(3,2,1)`.
- Rust restriction seeding, evacuation symmetry, and their combination
  agree with the default graph on `(5,5,3,3)`, including all 16 weight-5
  edges.

## Reproduction

```bash
make test
```

The runner retains each run's logs, graph files, and JSON reports in a fresh
directory under `test-output/`. The larger partitions take longer; the
default timeout is 1,800 seconds for each executable and partition. Override
it when running the comparison script directly:

```bash
python3 tests/compare_implementations.py --timeout 3600
```

The checked platform is Apple Silicon macOS with Clang, Homebrew `libomp`,
and Rust 1.94.1. Linux GCC/OpenMP build commands are supplied but have not
been executed in this validation environment.

The source package was also copied outside the original workspace. Both
programs built there, and an independent `(3,2)` run passed the same exact
graph comparison.
