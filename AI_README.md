# AI reading guide · Webs and exponentially large mu-coefficients

Hello and welcome! This is the companion to the paper by Tom Goertzen, Abel Lacabanne, Daniel Tubbenhauer and Pedro Vaz.

[Complete paper in Markdown](ai/paper.md) · [Raw full text](https://raw.githubusercontent.com/dtubbenhauer/mu/main/ai/paper.md) · [Read by section](ai/sections/README.md) · [Matching LaTeX source](ai/source.tex)

## The result

For every $r\ge0$ the paper constructs two permutations in a common left cell of $S_{12+18r}$, of rectangular shape $(4+6r,4+6r,4+6r)$, whose ordinary Kazhdan–Lusztig $\mu$-coefficient is $2^r$. Here $\mu$ is the coefficient in the highest degree allowed by the KL degree bound. The first examples give $1,2,4,8$ in $S_{12},S_{30},S_{48},S_{66}$. [Theorem 1B.1](ai/paper.md#thm:main) · [Rank bound](ai/paper.md#thm:rankbound)

## Where to start

| If you want to… | Open |
| --- | --- |
| Write down the two permutations | [Row words and the map to permutations](ai/paper.md#D:words) · [Notation](ai/notation.md) |
| Locate a precise statement or hypothesis | [Theorem index](ai/theorem_index.md) |
| Follow the proof from the webs to the ordinary KL coefficient | [Proof map](ai/proof_map.md) · [Tensor-to-KL formula](ai/paper.md#eq:FKK) |
| See why the web needs correcting | [The two-block example](ai/paper.md#eq:raw-two-coordinate). The raw coefficient of $v$ is $18$; the corrected coefficient is $2$. |
| Find where the factor of two enters | [The two rows of the constant matrix](ai/paper.md#loc:tworows) · [The coefficient for every block count](ai/paper.md#loc:coefficient) |
| Read a web or check a square resolution | [Diagram descriptions, including the reduction atlas](ai/diagrams.md) |
| See which steps Lean checks and which results it assumes | [Verification guide](ai/verification.md) · [Formal inputs](code/Lean/ASSUMPTIONS.md) |
| Trace the computational discovery | [Methods and AI assistance](ai/paper.md#sec:methods) · [W-graph programs](code/WGraphCode/README.md) |

Remark 9A.1 discusses two other families. One gives the computed values $19$ and $2446$. The other is proposed to give $\mu=n$ in $S_{3n}$ for every $n\ge4$; the authors have yet to check its geometric argument. [Figure 17](ai/paper.md#fig:mu19-candidate) · [Figure 18](ai/paper.md#fig:linear-mu)

This guide follows the 6 November 2026 manuscript, including Figure 18. The Markdown carries the paper's section, statement and figure numbering. The [LaTeX source](ai/source.tex) gives the original formulas, growth strings and drawing instructions.
