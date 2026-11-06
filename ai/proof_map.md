# How the exponential bound is proved

[AI reading guide](../AI_README.md) · [Full paper](paper.md) · [Theorem index](theorem_index.md)

The main theorem concerns the ordinary KL polynomial of an explicit pair of permutations. The calculation takes place in a tensor power of the three-dimensional fundamental representation of $\mathfrak{sl}_3$. Two steps connect the two descriptions: identify the right dual canonical vector for every block count, then compute one coefficient of that vector.

## 1. Fix the pair and the degree

For $m\ge0$ put $N_m=4+3m$. Use the row words $a_m=(ABC)^{N_m}$ and $c_m=\mathtt S\mathtt M^m\mathtt E$, with $\mathtt S=ABAAAC$, $\mathtt M=BBBAACACC$ and $\mathtt E=BBCBCC$. Applying the same word-to-permutation map to both gives $x_m<y_m$ in a common left cell of shape $(N_m,N_m,N_m)$. The length gap is $\delta_m=17m+11$. The theorem takes $m=2r$; for odd $m$ the length gap is even and $\mu(x_m,y_m)=0$ by definition. [Words](paper.md#D:words) · [left cell](paper.md#lem:rectangular-cell) · [lengths](paper.md#lem:lengths)

## 2. Identify the tensor coordinate

Write $e_s$ for a standard tensor and $b_{c_m}$ for the dual canonical vector. The Frenkel–Khovanov–Kirillov identification gives

$$
[e_{a_m}]b_{c_m}=v^{\delta_m}P^{J,+}_{x_m,y_m}(v^{-2}),
\qquad W_J=S_{N_m}\times S_{N_m}\times S_{N_m}.
$$

For even $m$, $\delta_m$ is odd. In the alternating formula for the parabolic polynomial, all terms indexed by nonidentity elements of $W_J$ have degree at most $(\delta_m-3)/2$. Only the identity term, the ordinary $P_{x_m,y_m}$, can contribute at $(\delta_m-1)/2$. The exponent becomes $1$ after the displayed substitution. It suffices to compute $[v][e_{a_m}]b_{c_m}$. [Proposition 4A.1](paper.md#thm:FKK) · [alternating convention](paper.md#eq:parabolic)

## 3. Construct the corrected vector

The planar web $W_{c_m}$ factors into a prefix, $m$ copies of a block and a tail. Already at $m=2$, the selected coordinate starts with $v^{-1}+18v$; the dual canonical coordinate starts with $2v$. The 94 lower webs in the complete correction explain the difference. Grouping their contributions across a three-strand cut suggests adjoining one scalar state for the terms with no strands crossing the cut. [Two-block calculation](paper.md#eq:raw-two-coordinate) · [94 lower webs](paper.md#eq:94correction)

The resulting interface $V^{\otimes3}\oplus\mathbf1$ has dimension $27+1=28$ for every $m$. The corrected prefix $p$, block $T$ and tail $\rho$ define $\beta_m=pT^m\rho$. The output still grows by nine letters per block. [Maps](paper.md#eq:maps) · [iteration](paper.md#eq:iterate)

## 4. Prove canonicality for every block count

The original maps commute with the tensor bar, so $\beta_m$ is bar invariant. To use uniqueness of $b_{c_m}$ one also needs integrality in $v$ and the leading tensor modulo $v$. Change coordinates on the interface; the adjacent changes cancel in the composite. One exceptional $v^{-2}$ term cancels in the upper row. An identity for the capped web and a local degree bound handle the lower row. Both ends and the whole transformed block now have entries in $\mathbb Z[v]$. [Coordinate change](paper.md#loc:gauge) · [upper row](paper.md#loc:upper) · [capping identity](paper.md#loc:openidentity) · [lower row](paper.md#loc:lowerrow)

At $v=0$ the tail produces $AAA\otimes e_{\mathtt E}$, the block sends $AAA$ to $AAA\otimes e_{\mathtt M}$, and the prefix sends $AAA$ to $e_{\mathtt S}$. Thus $\beta_m\equiv e_{c_m}\pmod v$ in the standard lattice. Bar invariance and this congruence identify $\beta_m=b_{c_m}$. [Canonical criterion](paper.md#thm:canonical) · [Lemma 7E.1](paper.md#prop:canonical)

## 5. Read off the coefficient with two rows

Fix the external state $a_m$. Both ends now have external letters $ABCABC$, and each block has $(ABC)^3$. The corresponding row, matrix and column give $[e_{a_m}]\beta_m=p_a\mathsf A^m\rho_a$. The tail is divisible by $v$ and $[v]\rho_a=e_{ABC}$; the constant prefix is the $ABC$ row. Consequently only $\mathsf A[0]$ occurs in the first-order coefficient. Its $ABC$ and scalar rows vanish off those same two columns. In that order the calculation is

$$
K=\begin{pmatrix}0&1\\2&0\end{pmatrix},\qquad
[v][e_{a_m}]b_{c_m}=(1,0)K^m(1,0)^{\mathsf T}.
$$

Since $K^2=2I$, this gives $2^{m/2}$ for even $m$ and zero for odd $m$. The two-state reduction applies to this particular coordinate at first order; the construction of the full tensor uses all 28 interface states. [Selected ends](paper.md#loc:selectedends) · [two rows](paper.md#loc:tworows) · [coefficient](paper.md#loc:coefficient)

## 6. Return to symmetric groups

Set $m=2r$ in steps 1, 2 and 5. This gives $\mu(x_{2r},y_{2r})=2^r$ in $S_{12+18r}$, with length gap $34r+11$. For general $n\ge12$, take $r=\lfloor(n-12)/18\rfloor$ and use the standard parabolic embedding into $S_n$. [Theorem 1B.1](paper.md#thm:main) · [Corollary 8C.1](paper.md#thm:rankbound)

## Where to check a local calculation

- [Appendix A](paper.md#loc:covectorappendix) gives the prefix covectors for the two-row calculation. The constant $2$ comes from two terms in the capping expansion, each contributing $1$.
- [Appendix B](paper.md#loc:atlasappendix) gives the diagram reductions for the capping identity with fixed boundary positions.
- [Remark 1E.1](paper.md#rem:verification) distinguishes the local tensor and web calculations, lattice induction and two-state readout verified in Lean from the cited representation-theoretic results taken as inputs.
