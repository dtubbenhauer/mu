# Theorem index

[AI reading guide](../AI_README.md) · [Full paper](paper.md) · [Proof map](proof_map.md) · [LaTeX source](source.tex)

## The exponential family

[Theorem 1B.1](paper.md#thm:main). For every integer $r\ge0$, take the tableaux with row words $(ABC)^{4+6r}$ and $ABAAAC\,(BBBAACACC)^{2r}\,BBCBCC$. To obtain a permutation from a word, list the positions of $C$, then $B$, then $A$, increasingly in each list. The resulting pair $x_{2r}<y_{2r}$ lies in a common left cell of $S_{12+18r}$ of shape $(4+6r,4+6r,4+6r)$ and satisfies $\mu(x_{2r},y_{2r})=2^r$.

[Corollary 8C.1](paper.md#thm:rankbound). For $n\ge12$, the maximum of $\mu(x,y)$ in $S_n$ is at least $2^{\lfloor(n-12)/18\rfloor}$. The proof embeds the largest family member that fits in $S_n$ as a standard parabolic subgroup. The paper also gives the corresponding growth conclusion for classical finite and affine types via standard parabolics.

## Results in manuscript order

The links go to the statements. For the few unlabelled lemmas, the link opens the surrounding part of the paper.

| Result | Statement or role |
|---|---|
| [Lemma 2C.2](paper.md#def:words2) | A word of content $(N,N,N)$ gives a standard tableau precisely when every prefix satisfies $\#A\ge\#B\ge\#C$. |
| [Lemma 2C.5](paper.md#lem:rectangular-cell) | For a dominant word $w$, the insertion tableau of $\pi(w)$ is $T(w)$ and the recording tableau is the fixed row-superstandard rectangle. This identifies the left cell. |
| [Lemma 2C.8](paper.md#D:words) | Both family words $a_m,c_m$ are dominant of content $(N_m,N_m,N_m)$, where $N_m=4+3m$. |
| [Lemma 2C.10](paper.md#lem:lengths) | $x_m<y_m$. Their lengths are $(27m^2+81m+60)/2$ and $(27m^2+115m+82)/2$, respectively. Their gap is $17m+11$. |
| [Lemma 3A.1](paper.md#lem:rotation) | Simultaneous rotation of the two rectangular webs preserves the symmetrized coefficient $\mu(x,y)+\mu(y,x)$. |
| [Proposition 3A.4](paper.md#thm:spider) | The non-elliptic $A_2$ webs form a basis of the invariant space, with the web relations presenting the intertwiner calculus. This is the spider theorem used in the paper. |
| [Lemma 3B.2](paper.md#sec:webs) | The tableau construction produces a non-elliptic web $W_w$. |
| [Lemma 3D.1](paper.md#lem:web-bar) | A web map intertwines the tensor bars on its source and target. |
| [Proposition 3D.2](paper.md#thm:canonical) | The unique bar-invariant tensor congruent to $e_w$ modulo $v$ in the standard lattice is $b_w$. The dominant rectangular labels give a basis of the all-positive invariant space. |
| [Proposition 4A.1](paper.md#thm:FKK) | For even $m\ge0$, $\mu(x_m,y_m)=[v][e_{a_m}]b_{c_m}$. This is where the ordinary KL coefficient enters. |
| [Lemma 5A.1](paper.md#lem:bar-symmetric-coefficients) | The coefficients of $b_w$ in the web basis are invariant under $v\mapsto v^{-1}$. |
| [Lemma 5B.1](paper.md#lem:elimination) | Eliminating the constant and negative powers in descending order of lower dominant labels, with bar-symmetric multiples of the lower $b_z$, gives $b_w$. |
| [Lemma 6B.1](paper.md#sec:construction) | The raw web factors as $W_{c_m}=\Psi_{\mathtt S}\Psi_{\mathtt M}^{m}\Psi_{\mathtt E}$ and has $12+9m$ external outputs. |
| [Definition 6C.1](paper.md#def:corrected) | The corrected tensor $\beta_m=pT^m\rho$ uses the 28-dimensional interface $V^{\otimes3}\oplus\mathbf1$. |
| [Lemma 7A.1](paper.md#loc:nonpositive) | The listed elementary pieces have nonpositive $v^{-1}$-degree. The local map $\mathtt S$ has a unique positive-degree path, of degree one and multiplicity one. |
| [Lemmas 7B.1](paper.md#loc:outer), [7B.2](paper.md#loc:offender), [7B.4](paper.md#loc:upper) | The rescaled outer map is integral. A single $v^{-2}$ term at input $ABC$ and output $(AC)^4$ exceeds the allowed local degree. Its cancellation makes the upper row of the transformed block integral over $\mathbb Z[v]$. |
| [Lemmas 7C.1](paper.md#loc:ascent), [7C.2](paper.md#loc:openidentity), [7C.4](paper.md#loc:lowerrow) | The ascent bounds and the two capping identities make the lower row integral. Its constant column at $AAA$ vanishes. |
| [Lemmas 7D.1](paper.md#loc:constantblock), [7D.2](paper.md#loc:initial), [7D.3](paper.md#loc:terminal) | In degree zero the tail starts at $AAA$, the block keeps that state and emits the middle word, and the prefix emits the start word. The tail and prefix also satisfy the required integrality. |
| [Lemma 7E.1](paper.md#prop:canonical) | $\beta_m=b_{c_m}$ for every $m\ge0$. The proof combines the bar action with the reduction of $\beta_m$ modulo $v$. |
| [Lemma 8A.2](paper.md#loc:tworows) | The $ABC$ and scalar rows of the constant matrix for the selected external word close on the same two columns. In that order the two rows restrict to $(0,1)$ and $(2,0)$. |
| [Lemma 8B.1](paper.md#loc:coefficient) | $[v][e_{a_m}]b_{c_m}=2^{m/2}$ for even $m$ and is zero for odd $m$. |
| [§8C](paper.md#S:Wrap) | The proof of Theorem 1B.1, the rank bound in Corollary 8C.1 and the applications in Remark 8C.2. |

## What the paper establishes about other families

Remark 9A.1 distinguishes two further candidates, illustrated in [Figure 17](paper.md#fig:mu19-candidate) and [Figure 18](paper.md#fig:linear-mu). For the first, the reported computations after canonical correction give $19$ in $S_{27}$ and $2446$ in $S_{36}$. For the second, the proposed formula is $\mu=n$ in $S_{3n}$ for all $n\ge4$. Together with the known small values it would realize every nonnegative integer. The authors explicitly say they have yet to check the geometric argument for this second family. The proof of exponential growth uses Theorem 1B.1.

For the scope of the Lean verification and its representation-theoretic inputs, see [Remark 1E.1](paper.md#rem:verification).
