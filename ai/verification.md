# What Lean checks

For the explicit permutations of [Theorem 1B.1](paper.md#thm:main), the paper proves $\mu(x_{2r},y_{2r})=2^r$ for every $r\ge0$. The Lean proof checks the web and tensor calculations, the induction on the full lattice, and the final two-state recurrence. It also carries out row insertion and computes the common rectangular recording tableau. The local calculations feed an induction valid for every block count. [Paper, verification remark](paper.md#rem:verification)

## From the tensor calculation to ordinary KL coefficients

The formalization takes standard results as theorem parameters. These include the web relations and tensor bar, the characterization of a dual canonical vector by its leading term and lattice condition, the Frenkel–Khovanov–Kirillov tensor/parabolic correspondence, the KL degree bounds and alternating parabolic formula, and the RSK description of left cells. The main theorem also uses a Bruhat-order criterion. With these inputs the computed tensor coordinate gives the **ordinary** $\mu$-coefficient. The repository lists the precise assumptions for each declaration. [Mathematical inputs](../code/Lean/ASSUMPTIONS.md) · [Manuscript dictionary](paper.md#sec:dictionary)

The following declarations belong to the namespace `WebMu.Revised`.

| Lean declaration | What it proves with those inputs |
| --- | --- |
| `paper_canonicality_faithful` | The constructed tensor is the specified dual canonical vector for every block count $m$. |
| `paper_main_faithful` | For $m=2r$, the explicit pair is Bruhat-comparable, lies in a common left cell, and has ordinary $\mu=2^r$. |
| `paper_unbounded_faithful` | For any proposed numerical bound, a pair in a common left cell exceeds it. |

[Lean declarations](../code/Lean/WebMu/Revised/FaithfulEndpoint.lean)

## Reproduce the checks

With the repository and its pinned Lean toolchain available, run this command from the repository root.

```sh
sh code/Lean/verify_lean.sh
```

The script builds the project and audits the endpoint declarations. Large finite checks use `native_decide`, so their evaluation also relies on the native compiler and runtime. The audit records the logical dependencies. [Audit source](../code/Lean/AuditIndependentMain.lean) · [Build instructions](../README.md#reproducing-the-verification)

For a small calculation to inspect first, take $m=2$. The raw web contributes $18v$ in the selected coordinate at degree one. Subtracting the lower terms changes the coefficient to $18-16=2$. The accompanying files give the 94 lower words, multipliers and selected coordinates, and the routine that contracts the tensors. [Paper, two-block calculation](paper.md#sec:basischange) · [M2Data.lean](../code/Lean/WebMu/Revised/M2Data.lean) · [M2Flow.lean](../code/Lean/WebMu/Revised/M2Flow.lean)

## Discovery and further candidates

The separate C and Rust programs compute finite type A cell $W$-graphs. Their vertices are standard tableaux, and their positive edge weights give $\mu$-coefficients in the corresponding cell. These computations led the authors to the family. [W-graph programs and examples](../code/WGraphCode/README.md)

Remark 9A.1 reports the values $19$ and $2446$ for two members of a different web family. The growth rate of this family is open. The same remark records a further candidate with $\mu=n$ in $S_{3n}$ for $n\ge4$. The authors describe its geometric argument as unchecked. The three Lean declarations above concern the exponential family. [Web family](paper.md#fig:mu19-candidate) · [Linear family](paper.md#fig:linear-mu)

[Back to the reading guide](../AI_README.md)
