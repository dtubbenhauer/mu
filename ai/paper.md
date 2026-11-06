# Webs and exponentially large mu-coefficients

Tom Goertzen · Abel Lacabanne · Daniel Tubbenhauer · Pedro Vaz

[AI reading guide](../AI_README.md) · [Matching LaTeX](source.tex) · [Diagram descriptions](diagrams.md)

**Abstract.** Using webs, we prove that Kazhdan–Lusztig mu-coefficients for symmetric groups grow at least exponentially with the rank, already for pairs labeled by a three-row rectangle.

**2020 Mathematics Subject Classification.** Primary: 05E10, 20C08. Secondary: 17B37, 18M30.

**Key words and phrases.** Kazhdan–Lusztig polynomials, $\mu$-coefficients, three-row partitions,
$\mathfrak{sl}_3$ webs, dual canonical bases, Hecke algebras.

**Contents**

- [1. Introduction](#section-1)
- [2. KL polynomials, cells and the family](#sec:preliminaries)
- [3. Webs and tensor coefficients](#sec:webs)
- [4. The coefficient to be computed](#sec:dictionary)
- [5. From webs to the dual canonical basis](#sec:basischange)
- [6. A corrected tensor on a fixed interface](#sec:construction)
- [7. Canonicality from local degree bounds](#sec:canonicality)
- [8. A two-state calculation of the coefficient](#sec:readout)
- [9. Methods, AI assistance and AI declaration](#sec:methods)
- [Appendix A. Details for Lemma 8A.2](#loc:covectorappendix)
- [Appendix B. Details for Lemma 7C.2](#loc:atlasappendix)
- [References](#references)

<a id="section-1" name="section-1"></a>

## 1. Introduction

We prove that $\mu$-coefficients for
$S_n=\operatorname{Aut}(\{1,\ldots,n\})$ grow at least
exponentially in $n$. By standard parabolic embeddings, this settles the boundedness question in all classical finite types and gives the same growth in their affine counterparts.

<a id="section-1A" name="section-1A"></a>

### 1A. The question

Kazhdan–Lusztig (KL) polynomials \[[KL79](#bib-KL)\] sit at the meeting point
of the representation theory of Hecke algebras, combinatorics and
the geometry of Schubert varieties. Among their coefficients,
the $\mu$-coefficients play a distinguished role. They are the
coefficients in the highest degree permitted by the KL degree
bound, taken to be zero when this bound is not attained.

**Remark 1A.1.** There are plenty of applications, and we can only give a biased list.
For a fixed Coxeter system, the full collection of $\mu$-coefficients determines all KL polynomials recursively,
and the $\mu$-coefficients determine the action of simple reflections on the KL basis and 
give the edge weights in the KL cell
$W$-graphs \[[KL79](#bib-KL)\]. Together with descent data, these weights
determine the cell representations, which in type $A$ give all
simple complex representations of symmetric groups.
For finite Weyl groups, they also determine composition
multiplicities of Verma modules in regular integral blocks of
category $\mathcal O$, via the KL character formula \[[KL79](#bib-KL)\].
For Weyl groups, $\mu(x,y)$ gives a local intersection cohomology
dimension of a Schubert variety in degree $\ell(y)-\ell(x)-1$
\[[KL80](#bib-KLPositivity)\].
The combinatorial invariance conjecture, due independently to
Lusztig and Dyer \[[Dye87](#bib-Dyer)\], predicts, in particular, that
$\mu(x,y)$ is an invariant of the abstract Bruhat interval $[x,y]$.
(A proof with Lean verification was recently claimed in
\[[OAI26](#bib-OpenAICIC)\].)
These examples are just the tip of the iceberg.

The $\mu$-coefficients are nonnegative integers \[[KL80](#bib-KLPositivity)\].
For a long time, they were conjectured to take only the values
$0$ and $1$, see e.g. \[[LS81](#bib-LS), [GM88](#bib-GarsiaMcLarnan)\]. McLarnan and Warrington disproved this conjecture
in 2002 \[[MW03](#bib-MW)\], and subsequent computations produced
considerably larger examples \[[War11](#bib-Warrington)\].
This left a natural question that remained open for more
than two decades: Are the $\mu$-coefficients bounded? If not, how quickly can they grow?

**Remark 1A.2.** The question is different from asking whether the coefficients
of KL polynomials can be arbitrarily large. Indeed, Polo
showed that every polynomial with nonnegative integer
coefficients and constant term $1$ occurs as a KL polynomial
of some symmetric group \[[Pol99](#bib-Polo99)\]. However, the
$\mu$-coefficient must occur in the highest degree permitted
by the KL degree bound, and Polo's construction does not
ensure this.

Scott–Xi constructed examples with $\mu=n+2$ in affine type
$\widetilde A_n$ for $n\ge4$ \[[SX10](#bib-SX)\], proving
unboundedness as the rank varies.
Lübeck's computations \[[Lüb20](#bib-Luebeck)\] suggested exponential growth
with the rank for first cohomology dimensions; see also
\[[PS14](#bib-ParkerStewart)\] for upper bounds.
For finite symmetric groups, even unboundedness remained open.
Our explicit family settles this question with a much stronger
conclusion (cf. [Corollary 8C.1](#thm:rankbound)):

**The $\mu$-coefficients of symmetric groups grow at least
exponentially in the rank, already within left cells of
three-row rectangular shape.**

This is a dramatic jump in complexity compared with many known
results and examples.
Several natural classes of pairs in finite and affine types
satisfy $0$-$1$ bounds \[[Gre09](#bib-Green), [Jon09](#bib-Jones), [Xi05](#bib-Xi)\], while the explicit
unbounded affine families of Scott–Xi and Chen \[[SX10](#bib-SX), [Che18](#bib-Chen)\]
exhibit only linear growth with the rank.
That exponential growth already occurs for three-row rectangles
makes the contrast even sharper: within two-row partitions, all
$\mu$-coefficients lie in $\{0,1\}$, see e.g.
\[[LS81](#bib-LS)\].

Our contribution is also methodological: we introduce a new
approach to $\mu$-coefficients using webs, in which the
construction of these striking examples becomes “obvious”
despite their complicated description as permutations.
(Proving that the construction works remains very difficult.)

**Remark 1A.3.** We will pass freely between
$\mu$-coefficients in symmetric groups and those occurring inside a
single left cell. More precisely, Lanini–McNamara prove that every $\mu$-coefficient
arising in a symmetric group also occurs for a pair of elements in a
common left cell of a possibly larger symmetric group
\[[LM21](#bib-LM), Corollary 4.3\], but
exponential growth inside left cells immediately implies exponential
growth for symmetric groups in general, cf. [Corollary 8C.1](#thm:rankbound).

Finally, at the end of [Section 8C](#S:Wrap), we sketch some 
interesting consequences of our main result.

<a id="section-1B" name="section-1B"></a>

### 1B. The main result in more detail

Our family can be written down using two words. A row word records a
standard tableau by assigning to entry $i$ the letter $A$, $B$ or $C$
according to whether $i$ lies in the first, second or third row. For example, the $(2,2,2)$ tableau below gives the row word and permutation

$$
\begin{array}{cc}
1&2\\
3&5\\
4&6
\end{array}
\quad\leftrightsquigarrow\quad
AABCBC
\quad\leftrightsquigarrow\quad
(4,6,3,5,1,2)
\quad\leftrightsquigarrow\quad
\text{six-strand permutation diagram}
.
$$

We read rows from bottom to top, left to right within each row, to get
the permutation in one-line notation. Strands connect bottom position
$i$ to the top position given by the $i$th entry.

<a id="thm:main" name="thm:main"></a>

**Theorem 1B.1.** For $r\ge0$, let $S_r,T_r$ be the standard tableaux with row words

$$
(ABC)^{4+6r},\qquad
\underbrace{ABAAAC}_{\mathtt{S}}(\underbrace{BBBAACACC}_{\mathtt{M}})^{2r}\underbrace{BBCBCC}_{\mathtt{E}}.
$$

For the associated permutations $x_{2r}<y_{2r}$ in $S_{12+18r}$, cf. [Figure 1](#fig:permutation-pair), one has

$$
\mu(x_{2r},y_{2r})=2^r.
$$

They lie in a common left cell of shape $(4+6r,4+6r,4+6r)$.

<a id="fig:permutation-pair" name="fig:permutation-pair"></a>

![Figure 1. Permutation pair](figures/figure-01.png)

**Figure 1.** The permutations $x_2$ and $y_2$, corresponding to $r=1$.
Strands are colored by tableau row. Reading from bottom to top,
the strand starting at position $i$ ends at the permutation value
at $i$. [Diagram description](diagrams.md#figure-1).

For example, the first four values are

$$
\begin{array}{c|cccc}
r&0&1&2&3\\\hline
\text{symmetric group}&S_{12}&S_{30}&S_{48}&S_{66}\\
\text{cell shape}&(4,4,4)&(10,10,10)&(16,16,16)&(22,22,22)\\
\mu(x_{2r},y_{2r})&1&2&4&8
\end{array}
$$

(The length gap is
$\delta_r=\ell(y_{2r})-\ell(x_{2r})=34r+11$, so the coefficient
occurs at degree $17r+5$. Since
$\mu(x_{2r},y_{2r})=2^{(\delta_r-11)/34}$, the growth is
exponential in the length gap itself.) Thus the permutations, their cell and the degree of the
coefficient are all explicit.
Below, $m$ counts the nine-letter blocks; the theorem uses $m=2r$.
For odd $m$, the corresponding $\mu$-coefficient is zero.

<a id="section-1C" name="section-1C"></a>

### 1C. The web picture

An $\mathfrak{sl}_3$ web is a planar trivalent graph representing an
invariant tensor of $\mathfrak{sl}_3$, cf. \[[Kup96](#bib-Kuperberg)\]. For three-row rectangles, standard tableaux index
both the web basis and the dual canonical basis of the same invariant
space. Frenkel–Khovanov–Kirillov (FKK) identify tensor coordinates of dual
canonical vectors with normalized parabolic KL polynomials \[[FKK98](#bib-FKK)\].
This gives a way to look for large KL coefficients using pictures.

Khovanov–Kuperberg (KK) showed that a basis web need not be dual canonical
\[[KK99](#bib-KK)\]. Their counterexample contains a hexagon surrounded by six
hexagons, the “hexagon-in-hexagons” picture. Our family repeats this
pattern along a strip. Heuristically, cf. [Figure 2](#fig:intro-hexagons), the construction is:

**Put hexagon-in-hexagons patches next to one another,
join them along three strands, and attach fixed start and end pieces.**

<a id="fig:intro-hexagons" name="fig:intro-hexagons"></a>

![Figure 2. Three repeating web patches](figures/figure-02.png)

**Figure 2.** A schematic of the repeated hexagon-in-hexagons pattern and
the three-strand gluing. The central hexagons are shaded. Orientations,
external legs and the precise attachments are omitted; the actual
pieces are given in [Section 6](#sec:construction). [Diagram description](diagrams.md#figure-2).

The exact construction is slightly different; see [Figure 7](#fig:family24) for examples.

<a id="section-1D" name="section-1D"></a>

### 1D. The proof in a nutshell

Repeating the picture gives a web, but we need the corresponding
dual canonical vector before applying the KL interpretation. Write
$W_w$ for the web with tableau label $w$, and $b_w$ for the dual
canonical vector with the same label. The change of basis has the form

$$
b_w=W_w+\sum_{z\prec w}\mathcal K_{z,w}(v)W_z,\qquad \mathcal K_{z,w}(v)\in\mathbb{Z}[v,v^{-1}],
$$

where the sum runs over lower tableau labels in the triangular order.
This unitriangular change of basis is described in
\[[Tub14](#bib-TubbenhauerCrystal), Corollary 3.7\], using the intermediate
crystal basis construction of Leclerc–Toffin \[[LT00](#bib-LeclercToffin)\].
The correction removes constant and negative powers of $v$ from the
nonleading tensor coordinates while preserving bar invariance.

For our family, the FKK normalization turns the highest allowed KL
degree into the power $v$. Thus $\mu$ is the coefficient of $v$ in the
relevant tensor coordinate; see [Proposition 4A.1](#thm:FKK).

This correction matters already for the first example with $\mu=2$.
The relevant coordinate of the raw web begins
$v^{-1}+18v+125v^3+\cdots$, whereas the coordinate of its dual
canonical vector begins $2v+70v^3+\cdots$. The lower terms remove
$v^{-1}+16v+\cdots$, so the required coefficient of $v$ is $18-16=2$.
[Section 5](#sec:basischange) gives the change of basis, with pictures
of the lower webs and a smaller four-dimensional example.

For the whole family, we incorporate the correction into the repeated
block. The resulting map uses the fixed interface
$V^{\otimes3}\oplus\mathbf{1}$, of dimension $28$, where $V$ is the
three-dimensional fundamental representation of $\mathfrak{sl}_3$ and $\mathbf{1}$ is the
trivial representation. The number of external strands grows, but
the interface stays the same.

The proof then has two parts. First, local web identities and degree bounds show that the
corrected tensor is dual canonical for any number of blocks, see
[Lemma 7E.1](#prop:canonical).
Second, a two-state calculation gives the required coefficient, see
[Lemma 8B.1](#loc:coefficient). Adding two blocks doubles its first-order
coefficient. The FKK identification and the ordinary KL degree bound
then give $\mu(x_{2r},y_{2r})=2^r$.

**Remark 1D.1.** Web algebras provide a categorical explanation of the change of
basis: webs define projective modules, while suitably normalized
indecomposable projectives give dual canonical vectors
\[[Mac14](#bib-MackaayDual), [MPT14](#bib-MPT), [Rob13](#bib-RobertFamily), [Rob15](#bib-RobertCharacterization), [Tub20](#bib-TubbenhauerGln)\]. Our proof uses
the tensor characterization of the dual canonical basis.

**Remark 1D.2.** This paper is a predecessor to \[[G+26a](#bib-Affine)\], but can be read independently.
Both papers follow roughly the same strategy with the following differences.

| Finite: this paper | Affine |
| --- | --- |
| Repeat planar web blocks. The rank is fixed. | Fix the annular web graph. Vary the rank and thicknesses. |
| Standard coefficients via FKK: evaluate explicit local maps on basis words. | Standard coefficients via Hecke–Schur: count intermediate flags to obtain Gaussian polynomials. |
| Correct the blocks on a fixed $28$-dimensional connecting space. Prove dual canonicality by local bounds. | Use degree bounds, bar symmetry and positivity to restrict canonical terms to six families. |
| Select the required tensor coordinate. Reduce the calculation to two states. | The desired terms occur once. Subtract one auxiliary family. Four others do not affect degree one. |
| Two more blocks double the coefficient: $\mu(x_{2r},y_{2r})=2^r$. | Gaussian cancellation gives $\sum_{j=1}^m\mu_{j;m}=\binom{m+1}{2}$. |

In both cases, webs serve as a visual guide.

<a id="section-1E" name="section-1E"></a>

### 1E. Computations and Lean verification

We found the family by computing left cell $W$-graphs using Nguyen's
method \[[Ngu20](#bib-Nguyen)\]. We computed the cell $W$-graphs for
all shapes of size at most $19$ and selected larger shapes. For $(8,6,5)$, the nonzero weights are
$1$ and $5$. For $(9,7,7)$, of dimension $38\,244\,492$, they are
$1,2,3,4,5,7,19$. Completing selected tableau pairs to rectangles
produced web pictures in which the repeated pattern became visible.
This continues the computational study of large KL coefficients in
\[[LTV26](#bib-LTVBigData)\]; a different approach to cell bases through
optimization appears in \[[GW26](#bib-GoertzenWilliamson)\]. [Section 9](#sec:methods) describes the discovery,
including AI assistance. A Lean verification and more code related to the paper 
can be found in \[[G+26b](#bib-GoLaTuVa-mu-code)\].

<a id="rem:verification" name="rem:verification"></a>

**Remark 1E.1.** The Lean formalization verifies the local tensor and diagram
calculations, the lattice induction and the two-state readout for
every block count. The cited representation theoretic results, e.g. \[[FKK98](#bib-FKK), [KK99](#bib-KK)\], are
explicit inputs (in other words, we only verify the 
contributions of this paper, not its dependencies).

### Acknowledgments

We thank the ANU Kioloa Coastal Campus, where the common interest of
TG and DT was discovered at a workshop organized by Anthony Licata
and Oded Yacobi. We thank Keeley Hoek for helping with
translating C code into very efficient Rust code for computing
$W$-graphs, and Lukas Lewark for making the
`webdraw` program available for computing Kuperberg polynomials.

TG acknowledges funding by the Australian Government
through the ARC Discovery Project DP230102982. DT was supported by 
ARC Future Fellowship FT230100489 and notes for the record that, 
shocking as it may seem, actual human thought went into constructing these pages.
P.V. is supported by the Fonds de la Recherche Scientifique-FNRS (Belgium) under Grant no. J.0235.26.

<a id="sec:preliminaries" name="sec:preliminaries"></a>

## 2. KL polynomials, cells and the family

This paper is largely self-contained, although we assume some familiarity with KL combinatorics (for the symmetric group) and webs. Standard references include \[[BB05](#bib-BjornerBrenti), [Kup96](#bib-Kuperberg)\].

<a id="section-2A" name="section-2A"></a>

### 2A. KL polynomials and the critical coefficient

Let $S_n$ be the symmetric group with adjacent transpositions
$s_i=(i,i+1)$. We compose permutations by $(xy)(i)=x(y(i))$
and write them in one-line notation. 
Write $\ell(w)$ for the number of inversions of $w$, called its length.
This is also the minimum number of adjacent transpositions in a product equal to $w$;
an expression attaining this minimum is reduced.
The Bruhat relation $x\le y$ means that a reduced expression for $x$
is a subword of a reduced expression for $y$.
The Hecke algebra over $\mathbb Z[q^{1/2},q^{-1/2}]$ has basis
$\{T_w\mid w\in S_n\}$, braid relations, and quadratic relations
$(T_s-q)(T_s+1)=0$. Its KL basis is characterized by

$$
C'_y=q^{-\ell(y)/2}\sum_{x\le y}P_{x,y}(q)T_x,
\qquad \overline{C'_y}=C'_y.
$$

Here $P_{x,y}(q)\in\mathbb Z[q]$, $\overline{q^{1/2}}=q^{-1/2}$,
$\overline{T_w}=T_{w^{-1}}^{-1}$, $P_{y,y}=1$, and
$\deg P_{x,y}\le(\ell(y)-\ell(x)-1)/2$ for $x<y$ \[[KL79](#bib-KL)\]. The following 
are the *$\mu$-coefficients*.

**Definition 2A.1.** We write

$$
\mu(x,y)=
\begin{cases}
[q^{(\ell(y)-\ell(x)-1)/2}]P_{x,y}(q)&x<y\text{ with odd length gap},\\
0&\text{otherwise}.
\end{cases}
$$

The notation $[q^k]f(q)$ means the coefficient of $q^k$ in $f(q)$,
and similarly for other variables. 

In the definition of $\mu$, the exponent is the allowed top degree,
which need not be the actual degree of the polynomial.
For example, $P_{x,y}=1$ gives $\mu(x,y)=0$ when the length gap is
greater than one, even though the polynomial has leading coefficient one.

<a id="section-2B" name="section-2B"></a>

### 2B. Left cells and standard tableaux

The multiplication formula

$$
C'_s C'_w=
\begin{cases}
(q^{1/2}+q^{-1/2})C'_w,&sw<w,\\
C'_{sw}+\displaystyle\sum_{\substack{z<w,sz<z}}\mu(z,w)C'_z,&sw>w,
\end{cases}
$$

explains why the $\mu$-coefficients determine cell representations
\[[KL79](#bib-KL)\]. Define $x\preceq_L y$ if there is a sequence
$y=w_0,w_1,\ldots,w_k=x$ in which $C'_{w_{j+1}}$ occurs with nonzero
coefficient in some $C'_sC'_{w_j}$. The equivalence classes for mutual
reachability are the left cells. The spans of downward-closed
unions of cells are left ideals; successive quotients give the
left cell modules. Descent sets and $\mu$-weights encode their
generator actions in a $W$-graph.

A standard tableau of shape $\lambda\vdash n$ fills the Young diagram
of $\lambda$ with $1,\ldots,n$, increasingly along rows and columns.
Use ordinary row insertion for the Robinson–Schensted–Knuth (RSK) correspondence
$w\mapsto(P(w),Q(w))$, where $P$ is the insertion tableau and $Q$ the
recording tableau. In type $A$, the left cells are exactly the sets
with fixed $Q$, see \[[Ari00](#bib-Ariki), Theorem A\]; fixing only its shape gives a two-sided cell, cf. \[[BB05](#bib-BjornerBrenti), p. 199, Exercise 11(b)\].
The resulting cell modules, specialized at $q=1$,
are simple and give all simple representations of $S_n$.
They are Specht modules; transposing the partition corresponds to
the sign twist between the two usual KL basis conventions. Throughout
this paper, a cell's shape means the shape of its recording tableau
under row insertion, independently of this convention for labeling representations.

<a id="section-2C" name="section-2C"></a>

### 2C. Words and the explicit family

To specify both the diagrams and the permutations, we use three-letter
words. This avoids choosing an auxiliary tableau in the RSK correspondence. We use the English convention for tableaux.

<a id="def:words2" name="def:words2"></a>

**Definition 2C.1.** Order $A<B<C$ and let $N\ge1$. A word of content $(N,N,N)$ contains $N$ copies of each
letter. It is dominant if every prefix satisfies
$\#A\ge\#B\ge\#C$. Its tableau has the positions of $A,B,C$ in its
first, second, and third rows. 

**Lemma 2C.2.** Dominance is exactly the condition
that this row-increasing tableau is standard.

*Proof.* 
The $i$th $A$ precedes the $i$th $B$, and the $i$th $B$
precedes the $i$th $C$, exactly when every prefix has
$\#A\ge\#B\ge\#C$. These are precisely the column inequalities. ∎

<a id="def:words" name="def:words"></a>

**Definition 2C.3.** For any word $w$ of this content, define $\pi(w)\in S_{3N}$ by listing
the positions of $C$, then of $B$, then of $A$, increasingly within
each list. 

**Example 2C.4.** For instance,

$$
ABCABC\longleftrightarrow
\begin{array}{cc}1&4\\2&5\\3&6\end{array},
\qquad \pi(ABCABC)=(3,6,2,5,1,4),
$$

where the final entry is one-line notation.

The map in [Definition 2C.3](#def:words) does more than assign permutations
to tableaux of equal shape: it fixes their recording tableau.

<a id="lem:rectangular-cell" name="lem:rectangular-cell"></a>

**Lemma 2C.5.** Let $w$ be a dominant word of content $(N,N,N)$, with tableau $T(w)$.
Then

$$
P\big(\pi(w)\big)=T(w),\qquad
Q\big(\pi(w)\big)=
\begin{array}{cccc}
1&2&\cdots&N\\
N+1&N+2&\cdots&2N\\
2N+1&2N+2&\cdots&3N
\end{array}.
$$

Consequently, all these permutations belong to a single left cell
of shape $(N,N,N)$.

*Proof.* 
Write the three rows of $T(w)$ as $(a_i)$, $(b_i)$, $(c_i)$, so that
$a_i<b_i<c_i$. The permutation $\pi(w)$ is the concatenation of
$(c_i)$, $(b_i)$, $(a_i)$. Inserting the first block creates the first
row. When $b_i$ is inserted, the first row is
$b_1,\ldots,b_{i-1},c_i,\ldots,c_N$: thus $c_i$ is bumped and appended
to the second row. The next block similarly bumps $b_i$ and then
$c_i$, creating the $i$th box of the third row. Hence the insertion
tableau is $T(w)$, and successive blocks create all boxes in rows
one, two and three, in that order. This gives the displayed $Q$.
The type $A$ cell classification gives the last assertion. ∎

[Lemma 2C.5](#lem:rectangular-cell) gives the common left cell assertion
in [Theorem 1B.1](#thm:main).

<a id="D:words" name="D:words"></a>

**Definition 2C.6.** For $m\ge0$, define

<a id="eq:words" name="eq:words"></a>

**Equation 2C.7.**

$$
\begin{gathered}
\mathtt{S}=ABAAAC\text{ (start)},\qquad \mathtt{M}=BBBAACACC\text{ (middle)},\qquad \mathtt{E}=BBCBCC\text{ (end)},\\
N_m=4+3m,\qquad a_m=(ABC)^{N_m},\qquad c_m=\mathtt{S}\mathtt{M}^m\mathtt{E},\\
x_m=\pi(a_m),\qquad y_m=\pi(c_m).
\end{gathered}
$$

We call $m$ the block count; $\mathtt{S},\mathtt{M},\mathtt{E}$ are the prefix,
repeated block and tail, respectively.

**Lemma 2C.8.** The words $a_m,c_m$ are dominant, and $x_m,y_m$ correspond to
tableaux of shape $(N_m,N_m,N_m)$.

*Proof.* 
Dominance of $a_m=(ABC)^{N_m}$ is immediate.
The contents of $\mathtt{S},\mathtt{M},\mathtt{E}$ are $(4,1,1)$, $(3,3,3)$ and $(0,3,3)$,
respectively, so both words have content $(N_m,N_m,N_m)$.

Every prefix of $\mathtt{S}$ is dominant, and its final prefix differences
are $(3,0)$. Starting from these differences, every prefix of $\mathtt{M}$
preserves dominance, and the whole block returns to $(3,0)$.
The final block $\mathtt{E}$ preserves dominance and ends at $(0,0)$.
Thus $c_m$ is dominant. The preceding lemma gives the claimed
tableau shape. ∎

<a id="rem:minimal-cell" name="rem:minimal-cell"></a>

**Remark 2C.9.** The tableau with row word $a_m$ is filled down columns. The permutation
$x_m$ is the least element of its left cell in Bruhat order and in left
weak order; cf. \[[Ngu20](#bib-Nguyen), Remark 6.21\]. Indeed, let $u$ relabel this
tableau to any standard tableau $T(w)$ of the same shape. Then
$\pi(w)=ux_m$ and $\ell(\pi(w))=\ell(u)+\ell(x_m)$: an inversion of $u$
can only go from an earlier column and a lower row to a later column
and a higher row. In particular, $x_m\le y_m$.

<a id="lem:lengths" name="lem:lengths"></a>

**Lemma 2C.10.** For the words in [Equation 2C.7](#eq:words), $x_m<y_m$ and

$$
\ell(x_m)=\frac{27m^2+81m+60}{2},\qquad
\ell(y_m)=\frac{27m^2+115m+82}{2},\qquad
\delta_m:=\ell(y_m)-\ell(x_m)=17m+11.
$$

*Proof.* 
Put $N=N_m$. The inequality $x_m\le y_m$ follows from
[Remark 2C.9](#rem:minimal-cell).

For $i<j$, the pair $(i,j)$ is an inversion of $\pi(w)^{-1}$
exactly when $w_i<w_j$.
Within $\mathtt{S},\mathtt{M},\mathtt{E}$, there are $6,17,8$ such pairs,
respectively. Each pair of distinct pieces, in the order in $c_m$,
contributes $27$. Hence

$$
\ell(y_m)=6+17m+8+27\left(2m+1+\binom m2\right),\qquad
\ell(x_m)=3N+3\binom N2.
$$

Expanding gives the stated lengths and the strict inequality. ∎

For odd $m$, the length gap in
[Lemma 2C.10](#lem:lengths) is even, so $\mu(x_m,y_m)=0$.
Thus it remains to compute $\mu(x_m,y_m)$ for even $m$.

<a id="sec:webs" name="sec:webs"></a>

## 3. Webs and tensor coefficients

We now turn to webs. The basic idea is simple. The $\mathfrak{sl}_3$ invariant spaces $\operatorname{Inv}(V^{\otimes3N})$,
where $V$ is the three-dimensional fundamental representation, carry two natural bases: the web basis $W_w$, which is concrete and comparatively easy to compute, and the dual canonical basis $b_w$, which is subtler but, up to the standard identifications, corresponds to the KL basis. Thus our main task is to understand the change of basis from $W_w$ to $b_w$. Once this is explicit enough for our family, [Theorem 1B.1](#thm:main) follows. This will occupy most of the paper.

<a id="section-3A" name="section-3A"></a>

### 3A. The planar calculus

Fix $\mathbb{K}=\mathbb Q(v)$ and $R=\mathbb Z[v]$, with $v$ a formal
parameter. Joining strands composes maps; placing
pictures side by side takes their tensor product. 
Moreover, before we even start recalling webs, we have the structure
of an operad/planar algebra:

<a id="lem:rotation" name="lem:rotation"></a>

**Lemma 3A.1.** For a pair of three-row rectangular tableaux, let $x,y$ be their
associated permutations from [Definition 2C.3](#def:words). The symmetrized
coefficient $\mu(x,y)+\mu(y,x)$ is unchanged after simultaneously
rotating their webs and applying [Definition 2C.3](#def:words) to the resulting
tableaux.

*Proof.* 
Rotation of a three-row rectangular web corresponds to promotion
of its tableau, see \[[PPR09](#bib-PPR), Theorem 2.5\], and simultaneous promotion
preserves the symmetrized coefficient, see \[[Rho10](#bib-Rhoades), Proposition 3.2\].
Rhoades writes this coefficient as $\mu[P,Q]$; the maximum of the
two ordered coefficients equals our sum, since at most one is nonzero. ∎

We draw most webs in a disk. When a picture specifies a map
or a tensor coordinate, its boundary order and labels are fixed.

<a id="def:web" name="def:web"></a>

**Definition 3A.2.** An $A_2$ web, or $\mathfrak{sl}_3$ web, is a planar graph in a disk or rectangle, with
ordered univalent boundary vertices and trivalent internal vertices.
Internal vertices are bipartite, and we draw them hollow and filled
for sources and sinks. Every edge is oriented from a source to a sink;
boundary signs use the input/output convention below. Closed circle components
are allowed. The boundary order, boundary signs, and cyclic orders of
edges at vertices are part of the data.

Set
$d=v+v^{-1}$, and $e=v^2+1+v^{-2}=d^2-1$.
The web category consists of $\mathbb{K}$-linear combinations of these
webs, modulo the circle, digon, and square relations in
[Figure 3](#fig:relations).

A web is non-elliptic if it has no circle component and no
internal digon or square face.

<a id="fig:relations" name="fig:relations"></a>

![Figure 3. Circle, digon and square relations](figures/figure-03.png)

**Figure 3.** The $A_2$ relations. Hollow and filled internal vertices are
sources and sinks, respectively. All undisplayed parts of each web
remain fixed. Reversing all vertex types gives the same relations. [Diagram description](diagrams.md#figure-3).

**Remark 3A.3.** For the reader familiar with e.g. \[[Kup96](#bib-Kuperberg)\]:
hollow and filled internal vertices specify orientation, so arrows
can be omitted. At a positive output boundary vertex the edge enters the diagram;
at a positive input it leaves the diagram. Negative signs reverse
these conventions.

Let $V^+$ be the three-dimensional fundamental $U_{{v^{-1}}}(\mathfrak{sl}_3)$
module and $V^-$ its dual, in the normalization of [Equation 3C.1](#eq:localmaps) (we follow \[[KK99](#bib-KK)\]); put $V=V^+$. 
An ordered sequence of signs represents a tensor product of these
modules. Vertical composition and horizontal juxtaposition represent
composition and tensor product of maps. A web with no inputs and $n$
positive outputs is therefore a map $\mathbf{1}\to V^{\otimes n}$, or
equivalently an invariant tensor. Here $\mathbf{1}$ is the one-dimensional
trivial module.

<a id="thm:spider" name="thm:spider"></a>

**Proposition 3A.4.** Non-elliptic $A_2$ webs form a basis of the corresponding
invariant tensor space. The web relations present the associated
intertwiner calculus.

*Proof.* 
This is the $A_2$ case of \[[Kup96](#bib-Kuperberg), Sections 4–6, Theorems 5.1 and 6.1\]. ∎

The non-elliptic webs form bases of the invariant spaces, while the
standard tensors form a basis of the ambient tensor power. For $n=3N$,
the all-positive invariant space is the multiplicity space corresponding
to the rectangular partition $(N,N,N)$ under quantum Schur–Weyl
duality; see \[[FKK98](#bib-FKK), Section 2\]. Below we work with the tensor
realization.

<a id="section-3B" name="section-3B"></a>

### 3B. Tableaux and the displayed family

The dominant word of [Definition 2C.1](#def:words2) determines the leading
boundary state of a non-elliptic web. 
Starting from the tableau, read the second row from left to right,
matching each entry with the nearest unused smaller first-row entry.
Then match the third row with the second row in the same way.
Insert a trivalent vertex above each second-row boundary point,
and replace each crossing by a dumbbell, e.g.

$$
\text{crossing}
\rightsquigarrow
\text{vertical dumbbell}
\text{ or }
\text{horizontal dumbbell}
,
$$

where the choice between I (middle) and H (right) is determined by bipartiteness.
We denote the resulting web by $W_w$.

<a id="ex:tableau-to-web" name="ex:tableau-to-web"></a>

**Example 3B.1.** For $w=AABCBC$, the first matching gives $(2,3),(1,5)$,
and the second gives $(3,4),(5,6)$.
The arcs do not cross:

$$
\text{tableau }AABCBC\ \longmapsto\ \text{arc diagram}\ \longmapsto W_{AABCBC}
.
$$

Resolving the two boundary junctions gives tripods on
$(2,3,4)$ and $(1,5,6)$.

For $w=ABACBC$, the first matching gives $(1,2),(3,5)$,
and the second gives $(2,4),(5,6)$.
The arcs $(2,4)$ and $(3,5)$ cross once:

$$
\text{tableau }ABACBC\ \longmapsto\ \text{arc diagram}\ \longmapsto W_{ABACBC}
.
$$

Resolving the two boundary junctions and the crossing gives $W_w$.

**Lemma 3B.2.** The web $W_w$ is non-elliptic.

*Proof.* 
The KK growth
algorithm constructs this web directly from the word
\[[KK99](#bib-KK), Section 5\]. The above description is Tymoczko's
equivalent construction \[[Tym12](#bib-Tymoczko), Sections 2–4, Theorem 4.9\]. ∎

**Remark 3B.3.** There is another useful tableau-to-web construction in
\[[MPT14](#bib-MPT), Section 4.1\]. The algorithm therein is
more general: it allows arbitrary sign strings and semistandard tableaux,
and naturally produces a web together with a flow. In the all-positive
standard case considered here, it recovers the same KK
web. Tymoczko's construction is more convenient for our purposes because
the intermediate arc diagram makes the web easy to draw.

<a id="sec:elementarytensors" name="sec:elementarytensors"></a>

### 3C. Elementary tensors and decorations

We fix the coordinates of the elementary web maps in
[Figure 4](#fig:generators). Here we draw maps in a rectangle,
with inputs at the bottom and outputs at the top.

<a id="fig:generators" name="fig:generators"></a>

![Figure 4. Local web generators](figures/figure-04.png)

**Figure 4.** The generators $y,\lambda,\sigma',\sigma$ are the split,
merge, cup and cap. The derived maps $H,\tau,\eta$ are bracketed;
$\tau$ is the tripod and $\eta$ its evaluation. Inputs are at the
bottom and outputs at the top; $+,-$ specify modules. Reversing
all signs and vertex types gives the other sign patterns. [Diagram description](diagrams.md#figure-4).

Write $e_A,e_B,e_C$ for the standard basis vectors of either
signed module $V^\pm$, labeled by $1,0,-1$, respectively.
Their weights are $\varepsilon_1,\varepsilon_2,\varepsilon_3$
in $V^+$ and $-\varepsilon_3,-\varepsilon_2,-\varepsilon_1$ in $V^-$.
Here the $\varepsilon_i$ are the coordinate weights on the diagonal
traceless Cartan subalgebra, so $\varepsilon_1+\varepsilon_2+\varepsilon_3=0$.
For a word $w=w_1\cdots w_n$ in $\{A,B,C\}$, put
$e_w=e_{w_1}\otimes\cdots\otimes e_{w_n}$.
We often abbreviate $e_A,e_B,e_C$ to $A,B,C$ and $e_w$ to $w$,
with the signed tensor factors understood.
For example, $AB=e_A\otimes e_B$.
Comparisons use the order $A<B<C$, and $\delta_{a<b}$ is an indicator.
The notation $[e_w]f$ denotes the coefficient of $e_w$ in $f$.

The cup and cap are
$\sigma':\mathbf{1}\to V^+\otimes V^-$ and
$\sigma:V^-\otimes V^+\to\mathbf{1}$.
The trivalent maps and the cup and cap are given in coordinates
by the following formulas. Here $\nu(a,b)=\nu(ab)$ is the label assigned to the unordered pair $\{a,b\}$ below.

<a id="eq:localmaps" name="eq:localmaps"></a>

**Equation 3C.1.**

$$
\begin{gathered}
y(A)=AB+v BA,\qquad y(B)=AC+v CA,\qquad y(C)=BC+v CB,\\
\lambda(ab)=v^{-\delta_{a<b}}\nu(a,b)\quad(a\ne b),
\qquad \lambda(aa)=0,\\
\nu(AB)=A,\qquad \nu(AC)=B,\qquad \nu(BC)=C,
\qquad \nu(a,b)=\nu(b,a),\\[2pt]
\sigma'(1)=AC+v BB+v^2CA,\qquad
\sigma(AC)=v^{-2},\quad \sigma(BB)=v^{-1},\quad \sigma(CA)=1,\\
\sigma(s)=0\quad(s\notin\{AC,BB,CA\}).
\end{gathered}
$$

The same formulas apply after globally reversing the signs and vertex
types. The map $H$ exchanges opposite boundary signs by a planar web.

**Remark 3C.2.** The formulas in [Equation 3C.1](#eq:localmaps) are as in
\[[KK99](#bib-KK), Section 2\], with $v=-q_{\rm KK}^{-1/2}$.

For the derived maps in [Figure 4](#fig:generators), put
$H=(I\otimes\lambda)(y\otimes I)$,
$\tau=(I\otimes y)\sigma'$ and $\eta=\sigma(\lambda\otimes I)$.
Their coordinates are

$$
\begin{array}{c|ccccccccc}
s&AA&AB&AC&BA&BB&BC&CA&CB&CC\\\hline
H(s)&AA&BA&v^{-1} AC+BB&AB&AC+CA&CB&BB+v CA&BC&CC
\end{array},
$$

while the nonzero coordinates of $\tau,\eta$, ordered as $ABC,ACB,BAC,BCA,CAB,CBA$, are

<a id="eq:tripod" name="eq:tripod"></a>

**Equation 3C.3.**

$$
\tau=(1,v,v,v^2,v^2,v^3)^{\mathsf T},\qquad
\eta=(v^{-3},v^{-2},v^{-2},v^{-1},v^{-1},1).
$$

In particular,
$\tau^{\mathsf T}=v^3\eta$ and $\eta\tau=de$.
Transpose throughout means ordinary coordinate transpose over $\mathbb{K}$, and we write $\tau^j$ for the tensor
product of $j$ tripods.

**Remark 3C.4.** Fix the states on the boundary edges of a web.
A compatible decoration labels each internal edge by $A,B$ or $C$
so that the corresponding local coefficients in
[Equation 3C.1](#eq:localmaps) are nonzero.
Its weight is the product of these coefficients.
The coefficient for the fixed boundary states is the sum of these
weights over all compatible decorations.

<a id="section-3D" name="section-3D"></a>

### 3D. The dual canonical condition

We first recall the bar involution. For a sign word
$S=s_1\cdots s_n$, write
$V^S=V^{s_1}\otimes\cdots\otimes V^{s_n}$.
On $V^+$ and $V^-$, the bar fixes the standard basis vectors and sends
$v$ to $v^{-1}$. On tensor products it is not the entrywise bar.
Instead, Lusztig's tensor bar
$\Phi_S\colon V^S\longrightarrow V^S$
is defined inductively using the quasi $R$-matrix $\overline\Theta$: if
$S=TT'$, then
$\Phi_S(x\otimes y) = \overline\Theta\bigl(\Phi_T(x)\otimes\Phi_{T'}(y)\bigr)$.
Thus $\Phi_S$ is $v$-antilinear and is the bar involution relevant for
the dual canonical basis. We will use [Lemma 3D.1](#lem:web-bar) to establish
bar invariance without computing the tensor bar explicitly. For its
construction, see \[[Lus93](#bib-Lusztig), Chapter 27\] and
\[[KK99](#bib-KK), Section 6\].

<a id="lem:web-bar" name="lem:web-bar"></a>

**Lemma 3D.1.** Every web (without linear combination) is bar equivariant. More precisely, if a web represents
a map
$W\colon V^S\longrightarrow V^{S'}$,
then
$\Phi_{S'}\circ W=W\circ\Phi_S$.

*Proof.* 
This is proved for arbitrary monomial web maps in the proof of
\[[KK99](#bib-KK), Proposition 2\]. ∎

The point of [Lemma 3D.1](#lem:web-bar) is that bar invariance does not
distinguish the web basis from the dual canonical basis. The difference
is the triangularity condition.

<a id="thm:canonical" name="thm:canonical"></a>

**Proposition 3D.2.** For every sign word $S$ of length $n$ and every state word
$w\in\{A,B,C\}^n$, there is a unique tensor $b_w\in V^S$
(the dual canonical basis element) fixed by $\Phi_S$ and satisfying

$$
b_w\equiv e_w\pmod{v\bigoplus_z R e_z}.
$$

For $S=+^{3N}$, the vectors $b_w$ indexed by dominant words of
content $(N,N,N)$ form a basis of $\operatorname{Inv}(V^{\otimes3N})$.

*Proof.* 
The canonical basis input is Lusztig's tensor product construction
\[[Lus93](#bib-Lusztig), Chapter 27\].
In the exact conventions used here, see
\[[KK99](#bib-KK), Theorem 3\]. The invariant subspace assertion is
\[[Lus93](#bib-Lusztig), Section 27.2.5\], recalled in \[[KK99](#bib-KK), Section 6\]. ∎

<a id="ex:six" name="ex:six"></a>

**Example 3D.3.** There are five dominant words for $(2,2,2)$:

$$
w_1=AABBCC,\quad w_2=AABCBC,\quad
w_3=ABABCC,\quad w_4=ABACBC,\quad w_5=ABCABC.
$$

Their five webs are shown in [Figure 5](#fig:six). Columns in the following
matrix are webs, and rows are the selected standard tensor states $e_{w_i}$:

<a id="eq:sixcoordinates" name="eq:sixcoordinates"></a>

**Equation 3D.4.**

$$
\bigl([e_{w_i}]W_{w_j}\bigr)_{i,j}=
\begin{pmatrix}
1&0&0&0&0\\
v&1&0&0&0\\
v&0&1&0&0\\
v^2&v&v&1&0\\
v&v^2&v^2&v&1
\end{pmatrix}.
$$

For example, $[e_{ABCABC}]W_{AABBCC}=v$, while
$[e_{ABCABC}]W_{ABCABC}=1$. The entries come from the elementary
tables above. All five webs are dual canonical, also by \[[KK99](#bib-KK), Theorem 1\]:
in their full tensor
expansions the leading coordinate is $1$ and every other coordinate
belongs to $v\mathbb{Z}[v]$. Thus [Equation 3D.4](#eq:sixcoordinates) is a tensor-coordinate
matrix, even though the web-to-dual-canonical matrix here is the identity.

<a id="fig:six" name="fig:six"></a>

![Figure 5. Five six-point webs](figures/figure-05.png)

**Figure 5.** The five all-positive six-point webs, in the order of
[Example 3D.3](#ex:six). The boundary order starts at the left and goes clockwise. [Diagram description](diagrams.md#figure-5).

<a id="section-3E" name="section-3E"></a>

### 3E. A teaser for our main family

[Figure 6](#fig:family01) and [Figure 7](#fig:family24) show
$W_{a_m}$ and $W_{c_m}$ for $m\in\{0,1,2,4\}$. These webs are
non-elliptic, but $W_{c_m}$ need not be dual canonical. By
[Theorem 1B.1](#thm:main) and [Lemma 2C.10](#lem:lengths), the corresponding
$\mu$-coefficients are $1,0,2,4$, respectively.

<a id="fig:family01" name="fig:family01"></a>

![Figure 6. Zero and one block](figures/figure-06.png)

**Figure 6.** The indexing webs for $m=0$ and $m=1$, with tableaux below
each diagram. Boundary labels are fixed; edges join opposite vertex
types. [Diagram description](diagrams.md#figure-6).

<a id="fig:family24" name="fig:family24"></a>

![Figure 7. Two and four blocks](figures/figure-07.png)

**Figure 7.** The members $m=2$ and $m=4$, of shapes $(10,10,10)$ and
$(16,16,16)$. [Diagram description](diagrams.md#figure-7).

<a id="sec:dictionary" name="sec:dictionary"></a>

## 4. The coefficient to be computed

The following statement reduces the calculation of
$\mu(x_m,y_m)$ to a single tensor coordinate.

<a id="thm:FKK" name="thm:FKK"></a>

**Proposition 4A.1.** For every even $m\ge0$,
$\mu(x_m,y_m)=[v]([e_{a_m}]b_{c_m})$.

*Proof.* 
Put $N=N_m$, $x=x_m$, $y=y_m$, and
$\delta=\ell(y)-\ell(x)$.
The permutations $x,y$ are minimal length representatives of
the cosets $xW_J,yW_J$ in $S_{3N}/W_J$, where
$W_J=S_N\times S_N\times S_N$ and $J$ omits the simple
reflections in positions $N,2N$.

Use Deodhar's parabolic polynomial \[[Deo87](#bib-Deodhar)\] in the
alternating convention of \[[FKK98](#bib-FKK), (1.6)\]:

<a id="eq:parabolic" name="eq:parabolic"></a>

**Equation 4A.2.**

$$
P^{J,+}_{x,y}(q)
=\sum_{h\in W_J,\,xh\le y}(-1)^{\ell(h)}P_{xh,y}(q).
$$

The FKK identification \[[FKK98](#bib-FKK), Theorem $2.5'$\] gives

<a id="eq:FKK" name="eq:FKK"></a>

**Equation 4A.3.**

$$
[e_{a_m}]b_{c_m}
=v^{\delta_m}P^{J,+}_{x_m,y_m}(v^{-2}).
$$

To check the conventions, write FKK's quantum parameter as $z$
and their polynomial variable as $Q=z^{-2}$, and set $z=-v^{-1}$.
We use their module with $u=Q$, which gives the alternating
sum in [Equation 4A.2](#eq:parabolic).
The bar in their equation (1.4) replaces $Q$ by
$Q^{-1}=v^{-2}$, while $(-z)^{-\delta}=v^{\delta}$.
Their map (2.16) identifies the standard parabolic basis with
the standard tensors without an additional sign, and (2.17)
fixes the dual canonical normalization.
Here $A,B,C$ correspond to their
$\mathbf e_1,\mathbf e_2,\mathbf e_3$.
Their initial word $C^NB^NA^N$ gives our representatives
$\pi(w)$. The coproduct in \[[KK99](#bib-KK), Section 2\] is FKK's
second coproduct (2.12), and their tensor bar $\psi'$ is our $\Phi$.

By [Lemma 2C.10](#lem:lengths), $\delta=17m+11$ is odd and at least $11$.
For $h\ne1$ appearing in [Equation 4A.2](#eq:parabolic), minimality
gives $\ell(xh)=\ell(x)+\ell(h)$. Also $xh\ne y$, since $x,y$ are
distinct minimal representatives, so $xh<y$.
The ordinary KL degree bound, together with $\ell(h)\ge1$
and the oddness of $\delta$, therefore gives

$$
\deg P_{xh,y}\le
\left\lfloor\tfrac{\delta-\ell(h)-1}{2}\right\rfloor
\le\tfrac{\delta-3}{2}.
$$

Thus, only $h=1$ contributes to degree $(\delta-1)/2$ in
[Equation 4A.2](#eq:parabolic), and this coefficient is $\mu(x,y)$.
Under [Equation 4A.3](#eq:FKK), a term $q^k$ becomes $v^{\delta-2k}$.
Thus, the coefficient of $v$ is precisely this critical coefficient. ∎

The remaining sections use the change of basis from webs to the
dual canonical basis to construct $b_{c_m}$ and compute $\mu(x_m,y_m)$.

**Example 4A.4.** For the six-point example in [Example 3D.3](#ex:six), take
$a=ABCABC$, $c=AABBCC$. Then
$x=\pi(a)=(3,6,2,5,1,4)$, $y=\pi(c)=(5,6,3,4,1,2)$ and
$\ell(y)-\ell(x)=3$. Direct KL recursion gives $P_{x,y}(q)=1+q$
and $P^{J,+}_{x,y}(q)=q$. The same FKK dictionary gives
$[e_a]b_c=v^3P^{J,+}_{x,y}(v^{-2})=v$, agreeing with
[Equation 3D.4](#eq:sixcoordinates).

<a id="ex:fkk-two" name="ex:fkk-two"></a>

**Example 4A.5.** For $m=2$, the permutations lie in $S_{30}$ and their length gap
is $45$. By [Equation 5C.1](#eq:raw-two-coordinate) below and
[Proposition 4A.1](#thm:FKK), $\mu(x_2,y_2)=2$.
More explicitly, [Equation 4A.3](#eq:FKK) gives

$$
P^{J,+}_{x_2,y_2}(q)
=4q^{16}+77q^{17}+377q^{18}+607q^{19}
+355q^{20}+70q^{21}+2q^{22}.
$$

Indeed, $v^{k-45}=q^{(45-k)/2}$ under $q=v^{-2}$,
so the term $2v$
becomes $2q^{22}$. The degree $22$ is the critical degree,
and the ordinary KL polynomial has the same coefficient $2$ there.

<a id="sec:basischange" name="sec:basischange"></a>

## 5. From webs to the dual canonical basis

We now explain a crucial change of basis.

<a id="section-5A" name="section-5A"></a>

### 5A. Three kinds of coordinates

Fix a boundary with $3N$ positive signs and write $\mathcal D_N$ for
the dominant words of content $(N,N,N)$. A word $w$ in $\mathcal D_N$ labels
two invariant tensors: the non-elliptic (ne) web $W_w$ and the dual canonical (dc) vector $b_w$.
For any state word $s\in\{A,B,C\}^{3N}$, the state tensor (s) $e_s$
is a third object; it is usually not invariant. The word $s$ need not be dominant. 
For clarity, the three bases and their uses are

| Basis | Space | Use in the proof |
| --- | --- | --- |
| $\{e_s\}$, all state words | $V^{\otimes3N}$ | Tensor coefficients |
| $\{W_w:w\in\mathcal D_N\}$ | $\operatorname{Inv}(V^{\otimes3N})$ | Planar construction |
| $\{b_w:w\in\mathcal D_N\}$ | $\operatorname{Inv}(V^{\otimes3N})$ | FKK and KL coefficients |

.

Order state strings lexicographically with $C\prec B\prec A$; write
$z\prec w$ when the state string for $z$ is smaller. This is the
reverse of lexicographic order on words with $A<B<C$. Then \[[FKK98](#bib-FKK), proof of Proposition $2.4'$\], \[[KT02](#bib-KashiwaraTanisaki), Corollary 4.5\],
\[[KK99](#bib-KK), Theorem 2\], 
and \[[Tub14](#bib-TubbenhauerCrystal), Corollary 3.7\] give

$$
\begin{gathered}
\begin{aligned}
W_w&=e_w+\sum_{s\prec w}\mathcal M_{s,w}(v)e_s,
&&\mathcal M_{s,w}(v)\in\mathbb{Z}_{\geq 0}[v,v^{-1}],\text{(ne in s coordinates)}\\
b_w&=e_w+\sum_{s\prec w}\mathcal N_{s,w}(v)e_s,
&&\mathcal N_{s,w}(v)\in v\mathbb{Z}_{\geq 0}[v],\text{(dc in s coordinates)}\\
b_w&=W_w+\sum_{z\prec w}\mathcal K_{z,w}(v)W_z,
&&\mathcal K_{z,w}(v)\in\mathbb{Z}[v,v^{-1}],\text{(dc in ne coordinates)}.
\end{aligned}
\end{gathered}
$$

In the first two sums $s$ ranges over all tensor state words;
in the last, $z$ ranges over dominant words.

<a id="lem:bar-symmetric-coefficients" name="lem:bar-symmetric-coefficients"></a>

**Lemma 5A.1.** Suppose
$b_w=\sum_z \mathcal K_{z,w}(v)W_z$.
Then
$\mathcal K_{z,w}(v)=\mathcal K_{z,w}(v^{-1})$
for all $z,w$.

*Proof.* 
Both $b_w$ and every web $W_z$ are fixed by the tensor bar, cf. [Lemma 3D.1](#lem:web-bar)
and [Proposition 3D.2](#thm:canonical). Applying the bar to the expansion above therefore gives
$b_w=\sum_z \mathcal K_{z,w}(v^{-1})W_z$.
Since the $W_z$ form a basis, uniqueness of the expansion implies
$\mathcal K_{z,w}(v)=\mathcal K_{z,w}(v^{-1})$. ∎

Write $\mathcal M$ for the matrix from ne coordinates to s coordinates,
$\mathcal N$ for the matrix from dc coordinates to s,
and $\mathcal K$ for the change-of-basis matrix from dc to
ne. Thus $\mathcal N=\mathcal M\mathcal K$, with

$$
[e_a]b_w=[e_a]W_w+\sum_{z\prec w}\mathcal K_{z,w}(v)[e_a]W_z.
$$

The coefficient used by FKK is an entry of $\mathcal N$, and the correction
from $W_w$ to $b_w$ is an entry of $\mathcal K$.

<a id="section-5B" name="section-5B"></a>

### 5B. What the correction removes

The following is the usual intermediate-basis-calculation as e.g. in
\[[LT00](#bib-LeclercToffin), Section 4.2\] or \[[Tub14](#bib-TubbenhauerCrystal)\].

<a id="lem:elimination" name="lem:elimination"></a>

**Lemma 5B.1.** Let $w\in\mathcal D_N$. Process the lower dominant labels
$z\prec w$ from largest to smallest. If the current coefficient at
$e_z$ has constant and negative part
$\alpha_0+\sum_{k>0}\alpha_{-k}v^{-k}$, subtract
$(\alpha_0+\sum_{k>0}\alpha_{-k}(v^{-k}+v^k))b_z$.
Repeating this produces $b_w$ and stays in the invariant subspace.

*Proof.* 
The correction coefficient has the required bad part and is
bar invariant. The remaining coordinates of $b_z$ lie below $z$, so
elimination cannot spoil a coordinate already treated. To see that
dominant labels suffice, expand $W_w$ in the invariant basis
$\{b_z\mid z\in\mathcal D_N\}$. Its leading term is $b_w$, and the
lower coefficients are bar-invariant Laurent polynomials. At each
step the bad part recovers the full coefficient of the largest
remaining $b_z$, since $[e_z]b_w\in v\mathbb{Z}[v]$. Thus all lower summands
are removed, leaving $b_w$. ∎

The tensors remain invariant throughout, but the congruence in
[Proposition 3D.2](#thm:canonical) concerns all tensor coordinates, including nondominant states. For instance, at a lower
dominant label $z$, a residual coefficient $v^{-1}+3v$ is corrected by
subtracting $(v+v^{-1})b_z$, leaving $2v$ at $e_z$.

<a id="ex:oneblockchange" name="ex:oneblockchange"></a>

**Example 5B.2.** Consider $c_1=ABAAAC\,BBBAACACC\,BBCBCC$.
Put

$$
z_1=ABABACCBC(ABC)^4,\quad
z_2=ABCAABCBC(ABC)^4,\quad z_3=(ABC)^7.
$$

Each $W_{z_i}$ has no internal faces, cf.
[Figure 8](#fig:oneblockchange), and is therefore dual canonical
by the argument in \[[KK99](#bib-KK), proof of Proposition 3\]. For $i=1$ it is a nine-point web
followed by four disjoint tripods; for $i=2$ it is a tripod followed by the
six-point web in [Example 3B.1](#ex:tableau-to-web) and four further tripods;
for $i=3$ it is seven tripods.

The full nonpositive $v$-degree part of $W_{c_1}$ is

$$
e_{c_1}+e_{z_1}+e_{z_2}+e_{z_3}.
$$

The corresponding part of $W_{z_i}$ is just $e_{z_i}$. Hence

<a id="eq:oneblockchange" name="eq:oneblockchange"></a>

**Equation 5B.3.**

$$
b_{c_1}=W_{c_1}-W_{z_1}-W_{z_2}-W_{z_3}.
$$

This is an actual web-to-dual-canonical change of basis. On the
four-dimensional span of these webs, its matrix is

$$
(b_{z_1},b_{z_2},b_{z_3},b_{c_1})
=(W_{z_1},W_{z_2},W_{z_3},W_{c_1})
\begin{pmatrix}1&0&0&-1\\0&1&0&-1\\0&0&1&-1\\0&0&0&1\end{pmatrix}.
$$

For $a_1=(ABC)^7$, direct tensor contraction gives

$$
\begin{aligned}
[e_{a_1}]W_{c_1}&=1+10v^2+30v^4+24v^6+3v^8,\\
[e_{a_1}](W_{z_1}+W_{z_2}+W_{z_3})&=1+2v^2,\\
[e_{a_1}]b_{c_1}&=8v^2+30v^4+24v^6+3v^8.
\end{aligned}
$$

The correction removes the extra constant coefficient.

<a id="fig:oneblockchange" name="fig:oneblockchange"></a>

![Figure 8. One-block correction](figures/figure-08.png)

**Figure 8.** The four webs in [Equation 5B.3](#eq:oneblockchange). The lower webs
have isolated tripod components, which are retained at their actual
boundary positions. All four diagrams have $21$ positive boundary points. [Diagram description](diagrams.md#figure-8).

<a id="section-5C" name="section-5C"></a>

### 5C. The two-block example: the actual lower webs

For $c_2=\mathtt{S}\mathtt{M}^2\mathtt{E}$ the tensor coordinate $[e_{a_2}]W_{c_2}$ is already enough to
detect a failure of canonicality:

<a id="eq:raw-two-coordinate" name="eq:raw-two-coordinate"></a>

**Equation 5C.1.**

$$
\begin{aligned}
[e_{a_2}]W_{c_2}
&=v^{-1}+18v+125v^3+409v^5+617v^7+377v^9+77v^{11}+4v^{13},\\
[e_{a_2}]b_{c_2}
&=2v+70v^3+355v^5+607v^7+377v^9+77v^{11}+4v^{13}.
\end{aligned}
$$

The first line contains $v^{-1}$ and therefore cannot be the
coordinate of a dual canonical vector with another leading state.
The correction contributes $v^{-1}+16v+55v^3+54v^5+10v^7$.
Thus the required coefficient of $v$ is $18-16=2$.
This is $\mu(x_2,y_2)$ by [Proposition 4A.1](#thm:FKK): for the length gap $45$,
the FKK normalization sends the critical power $q^{22}$ to
$v^{45-2\cdot22}=v$.
The complete correction has $94$ lower webs. Split their indexing words
into sets $\mathcal R$ and $\mathcal F$ according to the multiplier:

<a id="eq:94correction" name="eq:94correction"></a>

**Equation 5C.2.**

$$
b_{c_2}=W_{c_2}
-\sum_{z\in\mathcal R}W_z
-(v+v^{-1})\sum_{z\in\mathcal F}W_z,
\qquad |\mathcal R|=91,\quad |\mathcal F|=3.
$$

All words in these sets have ten occurrences of each letter and are
strictly below $c_2$ in the state order. The three words in
$\mathcal F$ are particularly simple:

$$
f_1=ABABACCBC(ABC)^7,\qquad
f_2=ABCAABCBC(ABC)^7,\qquad f_3=(ABC)^{10}.
$$

Thus $W_{f_1}$ and $W_{f_2}$ have the same nine-point cores as the lower
webs in [Example 5B.2](#ex:oneblockchange), with seven tripods appended.
The web $W_{f_3}$ consists of ten tripods. Three examples from
$\mathcal R$ are

$$
\begin{aligned}
r_1&=ABAAACBBBABCACCCBC(ABC)^4,\\
r_2&=ABAAACBBBCABACCCBC(ABC)^4,\\
r_3&=ABAAACBBCBACABCCBC(ABC)^4.
\end{aligned}
$$

Their pictures are in [Figure 9](#fig:twoblocklower); the indicated
coefficients are entries of $\mathcal K$, not tensor coordinates.

<a id="fig:twoblocklower" name="fig:twoblocklower"></a>

![Figure 9. Lower webs for two blocks](figures/figure-09.png)

**Figure 9.** Six lower webs in [Equation 5C.2](#eq:94correction). The left column
contains all three Laurent corrections; the right column shows three
of the $91$ corrections with coefficient $-1$. Every diagram has
$30$ positive boundary points, numbered in the same order as $c_2$.
The first two left webs share the seven tripods at positions $10$ to $30$. [Diagram description](diagrams.md#figure-9).

In this example every one of the $94$ lower webs is itself dual
canonical: $W_z=b_z$ for $z\in\mathcal R\cup\mathcal F$.
Consequently the inverse change of basis is just

$$
W_{c_2}=b_{c_2}+\sum_{z\in\mathcal R}b_z
+(v+v^{-1})\sum_{z\in\mathcal F}b_z.
$$

The raw web therefore has one desired canonical summand and $94$ lower
ones. Removing the latter gives $b_{c_2}$. These identities and the
canonicality of the lower webs are checked in all tensor coordinates
by the accompanying script.

Here is how the pictured terms affect the coordinate at $a_2=(ABC)^{10}$.

| Web | Coefficient in $b_{c_2}$ | Tensor coordinate $[e_{a_2}]W_z$ |
| --- | --- | --- |
| $W_{f_1}$ | $-(v+v^{-1})$ | $v^2$ |
| $W_{f_2}$ | $-(v+v^{-1})$ | $v^2$ |
| $W_{f_3}$ | $-(v+v^{-1})$ | $1$ |
| $W_{r_1}$ | $-1$ | $v+5v^3+3v^5$ |
| $W_{r_2}$ | $-1$ | $v^3+4v^5+v^7$ |
| $W_{r_3}$ | $-1$ | $v+3v^3+v^5$ |

For the three Laurent terms, multiplication by $v+v^{-1}$ gives

$$
(v+v^{-1})(v^2+v^2+1)=v^{-1}+3v+2v^3.
$$

The remaining $91$ terms give

$$
[e_{a_2}]\sum_{z\in\mathcal R}W_z
=13v+53v^3+54v^5+10v^7.
$$

This accounts for every coefficient of the correction in
[Equation 5C.1](#eq:raw-two-coordinate). In particular, the three Laurent terms
remove $3v$, the other terms remove $13v$, and $18-3-13=2$ remains.
The negative power is canceled by the $f_3$ term. Its paired positive
power is forced by bar invariance, so it also changes the coefficient
we are trying to compute.

One can also see why the final check must include nondominant states.
Take $s=BAABACCBC(ABC)^7$, which starts with $B$ and is therefore
not dominant. Direct contraction gives

$$
[e_s]W_{f_1}=v,\qquad
[e_s]\bigl((v+v^{-1})W_{f_1}\bigr)=1+v^2.
$$

The raw web has constant coefficient $1$ at $e_s$, and this correction
removes it. A calculation confined to the dominant indexing words
would miss this coordinate. The raw web has $156$ nonzero coordinates
in nonpositive $v$-degree, of which $58$ are nondominant. After the
full correction, only the leading coordinate $e_{c_2}$ remains in
those degrees.

**Remark 5C.3.** The calculation above can be checked by hand, but arguably this is
neither pleasant nor a good use of time.
For a computer check, `M2Data.lean` lists all $94$ lower words,
their multipliers and their coordinates at $a_2$, and
`M2Flow.lean` provides the tensor contraction routine.
Both files are in `code/Lean/WebMu/Revised/`
in the repository \[[G+26b](#bib-GoLaTuVa-mu-code)\].

<a id="section-5D" name="section-5D"></a>

### 5D. From one column to the uniform construction

Listing such a column separately for every $m$ would not give a
uniform proof. Instead, [Section 6](#sec:construction) builds a web
combination $\beta_m$ from five fixed maps.
Here $\Psi_{\mathtt M}$ is the block map and $\Psi_{+},\Psi_{-}$ are correction maps.
Identity maps on external strands are understood in these compositions.
For two blocks it is

$$
\beta_2=\Psi_{\mathtt S}\Psi_{\mathtt M}^2\Psi_{\mathtt E}-\Psi_{\mathtt S}\Psi_{+}\Psi_{-}\Psi_{\mathtt E}-\Psi_{\mathtt S}\Psi_{\mathtt M}\Psi_{+}\tau^2+d\Psi_{\mathtt S}\Psi_{+}\tau^5=(\Psi_{\mathtt S},0)\cdot\begin{pmatrix}\Psi_{\mathtt M}&-\Psi_{+}\\\Psi_{-}&-d\tau^3\end{pmatrix}^2\cdot\binom{\Psi_{\mathtt E}}{\tau^2},
$$

where $\Psi_{\mathtt S}\Psi_{\mathtt M}^2\Psi_{\mathtt E}=W_{c_2}$ and $d=v+v^{-1}$. Similarly, we have

$$
\beta_1=\Psi_{\mathtt S}\Psi_{\mathtt M}\Psi_{\mathtt E}-\Psi_{\mathtt S}\Psi_{+}\tau^2=(\Psi_{\mathtt S},0)\cdot\begin{pmatrix}\Psi_{\mathtt M}&-\Psi_{+}\\\Psi_{-}&-d\tau^3\end{pmatrix}\cdot\binom{\Psi_{\mathtt E}}{\tau^2}.
$$

Expanding the three correction
terms of $\beta_2$ in the non-elliptic web basis gives the column above. Grouping
them by the three-strand interface produces a formula that extends
to every $m$. The local degree argument in [Section 7](#sec:canonicality)
proves that this construction indeed gives $\beta_m=b_{c_m}$.

<a id="section-5E" name="section-5E"></a>

### 5E. The categorical interpretation

For readers who prefer categorification, a web defines a projective
module over the web algebra \[[MPT14](#bib-MPT)\]. Such a projective can split.
The dual canonical basis corresponds instead to normalized
indecomposable projectives \[[Mac14](#bib-MackaayDual), Corollary 7.9\]. The
cyclotomic Hecke/KLR comparison and its canonical-basis-consequences
are developed in \[[BK09a](#bib-BrundanKleshchevBlocks), [BK09b](#bib-BrundanKleshchev)\].
Robert's red graphs detect certain splittings geometrically
\[[Rob13](#bib-RobertFamily), [Rob15](#bib-RobertCharacterization)\]. This explains why reducing
a web can reveal correction terms. The tensor calculation still has
to establish the coefficients and the leading state of the desired
canonical vector. In our proof these are supplied by the fixed maps
and their local degree bounds.

<a id="sec:construction" name="sec:construction"></a>

## 6. A corrected tensor on a fixed interface

We construct $\beta_m$ from fixed prefix (start), block (middle) and tail (end) maps, with corrections at each block. We will prove $\beta_m=b_{c_m}$ below.
The raw web has three connecting strands, with $3^3=27$
tensor states. Some correction terms have no connecting strands across
the cut; a scalar coordinate records this case. The connecting space
therefore has dimension
$27+1=28$, independently of $m$. This fixed dimension makes the computation possible: after
fixing the output state, the iteration reduces to calculations with
$28\times28$ matrices.

<a id="sec:localmaps" name="sec:localmaps"></a>

### 6A. Growth strings and local maps

The following strings specify the maps completely. They use the
KK growth operations \[[KK99](#bib-KK), Section 5\].
Recall that $c_m=\mathtt{S}\mathtt{M}^m\mathtt{E}$, with a six-letter prefix $\mathtt{S}$, a nine-letter
block $\mathtt{M}$, and a six-letter tail $\mathtt{E}$.
A downward growth string reduces the output boundary to the input
boundary. Read it from left to right, renumbering the remaining
strands from zero after each step. The signs $+,-$ specify
$V^\pm$, independently of the state labels $A,B,C$. The operation $Y_i$ merges the equal-sign
strands at positions $i,i+1$; $H_i$ applies the two-vertex web $H$ to
opposite signs; and $a_i$ removes an adjacent opposite-sign pair.
The remaining signs are the input signs of the map.

To construct the map upward, read the string in reverse, replacing
$Y_i$ by a split $y$ and $a_i$ by a cup $\sigma'$.
The operation $H_i$ uses the planar web $H$ in
[Figure 4](#fig:generators); identity maps act on the other strands.
This fixes the graph and its cyclic orders.

To compute a covector from a fixed output state, read downward
using the ordinary coordinate transposes of the upward maps.

The correction tables also use maps on three positive input strands.
Put

$$
\lambda_1=\lambda\otimes I,
\qquad \lambda_2=I\otimes\lambda,
\qquad E_1=(y\lambda)\otimes I,
\qquad E_2=I\otimes(y\lambda).
$$

Thus $\lambda_1$ acts on the first two strands and $\lambda_2$ on the
last two; the subscripts here are numbered from one. Products of maps
are composed from right to left, so $\lambda_2E_1$ first applies $E_1$.
This convention for composition is distinct from the left-to-right
reading of a downward growth string.

The prefix $\Psi_{\mathtt S}$, block $\Psi_{\mathtt M}$ and tail $\Psi_{\mathtt E}$ correspond to
$\mathtt{S},\mathtt{M},\mathtt{E}$, respectively. Together with the correction
maps $\Psi_{+},\Psi_{-}$, they have types

$$
\begin{array}{ll}
\Psi_{\mathtt S}:V^{\otimes3}\to V^{\otimes6},&
\Psi_{\mathtt M}:V^{\otimes3}\to V^{\otimes3}\otimes V^{\otimes9},\\
\Psi_{\mathtt E}:\mathbf{1}\to V^{\otimes3}\otimes V^{\otimes6},&
\Psi_{+}:\mathbf{1}\to V^{\otimes3}\otimes V^{\otimes9},\\
\Psi_{-}:V^{\otimes3}\to V^{\otimes9}.&
\end{array}
$$

For the block and tail, we have bent three negative inputs
into the first three positive outputs, preserving the boundary order.
Before bending, these pieces have types
$(V^-)^{\otimes3}\otimes V^{\otimes3}\to V^{\otimes9}$ and
$(V^-)^{\otimes3}\to V^{\otimes6}$, respectively.
The first three outputs are the connecting strands; the remaining
outputs carry $\mathtt{M}$ or $\mathtt{E}$.
The map $\Psi_{+}$ creates the three connecting strands, and
$\Psi_{-}$ removes them.
Start with $6$, $12$ and $9$ positive output strands for the
prefix, block and tail, respectively. The following strings
define $\Psi_{\mathtt S},\Psi_{\mathtt M},\Psi_{\mathtt E}$; see [Figure 10](#fig:pieces).

<a id="eq:growth" name="eq:growth"></a>

**Equation 6A.1.**

$$
\begin{aligned}
\Psi_{\mathtt S} &:Y_0Y_3H_2H_1Y_0,\\
\Psi_{\mathtt M} &:Y_2Y_6Y_7H_2Y_1H_2H_1Y_0H_3Y_2H_3Y_4H_2Y_1H_2H_1Y_0,\\
\Psi_{\mathtt E} &:Y_2Y_3Y_2Y_1Y_2Y_1Y_0a_0.
\end{aligned}
$$

With one-based numbering, the prefix string is precisely
$Y_1Y_4H_3H_2Y_1$. In particular, its first operation merges the first
two positive strands, whose leading state labels are $A,B$.

<a id="fig:pieces" name="fig:pieces"></a>

![Figure 10. The three raw pieces](figures/figure-10.png)

**Figure 10.** The three pieces of the raw web. The inputs $i_1,i_2,i_3$
of $\Psi_{\mathtt S}$ and $\Psi_{\mathtt M}$ are joined to outputs $1,2,3$ of the next piece.
Squares mark the three-strand interfaces.
All labels refer to the local piece, before gluing. [Diagram description](diagrams.md#figure-10).

These strings reduce the leading states as
$\mathtt{S}\to AAA$, $AAA\,\mathtt{M}\to AAA$, and $AAA\,\mathtt{E}\to\varnothing$.
For the tail, the first three merges give
$AAA\,\mathtt{E}\to AAABCBCC\to AAACBCC\to AABBCC$.
The remaining steps reduce $AABBCC$ to the empty boundary using only
$Y$ and $a$; no $H$ is needed.
For the longer strings, abbreviate
$\mathsf R_i=H_{i+1}Y_i$ and $\mathsf S=H_2H_1Y_0$.

To define $\Psi_{+}$, let $O$ be the map with twelve positive outputs and
downward string $Y_2Y_6Y_7\mathsf R_1$. Its eight surviving input
signs are $+--++--+$. Pair these inputs consecutively by four cups,
and denote the resulting tensor by $\kappa_8$. Then $\Psi_{+}=O\kappa_8$.
The resulting web is shown in [Figure 11](#fig:correction).
It gives the correction in [Example 5B.2](#ex:oneblockchange):

$$
\Psi_{\mathtt S}\Psi_{+}\tau^2=W_{z_1}+W_{z_2}+W_{z_3}.
$$

<a id="fig:correction" name="fig:correction"></a>

![Figure 11. Creating three strands](figures/figure-11.png)

**Figure 11.** The correction map
$\Psi_{+}=W_{ABACBC}\otimes\tau^2$.
Squares mark outputs $1,2,3$, which are reserved for the next attachment. [Diagram description](diagrams.md#figure-11).

The second correction is $\Psi_{-}=\sum_{i=1}^8D_i$. Each term is
$D_i=P_i h_i$, where $P_i$ has nine positive outputs and the downward
string in the table. The last column gives the input signs of $P_i$;
they agree with the output signs of the small map $h_i$.

| Map | Downward growth of $P_i$ | $h_i$ | Input signs of $P_i$ |
| --- | --- | --- | --- |
| $D_1$ | $Y_0Y_3Y_4a_4\mathsf S$ | $I$ | $+++$ |
| $D_2$ | $Y_0Y_3Y_4Y_3Y_2\mathsf R_0$ | $I$ | $+++$ |
| $D_3$ | $Y_0Y_2a_2Y_2\mathsf R_0Y_1$ | $\lambda_2$ | $+-$ |
| $D_4$ | $Y_0Y_1Y_2Y_1Y_2\mathsf R_0Y_1$ | $\lambda_2E_1$ | $+-$ |
| $D_5$ | $Y_0Y_1Y_0Y_1Y_2Y_1Y_1$ | $\lambda_2$ | $+-$ |
| $D_6$ | $Y_0a_0Y_1Y_2Y_1Y_1$ | $\lambda_2E_1$ | $+-$ |
| $D_7$ | $Y_0a_0Y_0a_0Y_0$ | $\lambda_1$ | $-+$ |
| $D_8$ | $Y_0a_0Y_0a_0Y_0a_0$ | $\eta$ | $\varnothing$ |

All eight terms have coefficient $1$. The signs of the correction
are specified in [Equation 6C.2](#eq:maps). See also [Figure 40](#fig:atlas-term4) for the corresponding webs.

<a id="section-6B" name="section-6B"></a>

### 6B. Gluing the basic pieces

Start with $\Psi_{\mathtt E}$, leaving its last six outputs external. At each
of the $m$ steps, join the first three outputs to the inputs of
$\Psi_{\mathtt M}$, in order. Keep the block's first three outputs for the next
attachment and leave its other nine outputs external. Finally
attach $\Psi_{\mathtt S}$, whose six outputs complete the prefix.

**Lemma 6B.1.** For every $m\ge0$, this gluing gives

$$
W_{c_m}=\Psi_{\mathtt S}\Psi_{\mathtt M}^m\Psi_{\mathtt E},\qquad
6+9m+6=12+9m\text{ external outputs}.
$$

*Proof.* 
The strings in [Equation 6A.1](#eq:growth) are admissible growth
steps on $\mathtt{S}$, $AAA\,\mathtt{M}$ and $AAA\,\mathtt{E}$. Applying them
successively from the prefix to the tail reduces $c_m$ to the empty
boundary. The growth algorithm therefore identifies the assembled
web with $W_{c_m}$ \[[KK99](#bib-KK), Section 5, Lemmas 1–3\]. ∎

The main proof identifies $\beta_m$ directly by its tensor congruence
and does not depend on this raw web identification. 
In the notation $\Psi_{\mathtt S}\Psi_{\mathtt M}^m\Psi_{\mathtt E}$, each new block acts only on
the three reserved strands; identity maps on the external strands
are understood.

<a id="ex:assembly" name="ex:assembly"></a>

**Example 6B.2.** Start with $\Psi_{\mathtt E}$, attach one copy of $\Psi_{\mathtt M}$, attach a second copy, and
close the three reserved outputs with $\Psi_{\mathtt S}$; see [Figure 12](#fig:assembly).
The blocks are attached from the tail towards the prefix.
The intermediate diagrams have $9,18,27$ outputs, of which three
are still reserved. The final diagram has $30$ external outputs.
Their order is

$$
\underbrace{1,\ldots,6}_{\mathtt{S}}\quad
\underbrace{7,\ldots,15}_{\mathtt{M}}\quad
\underbrace{16,\ldots,24}_{\mathtt{M}}\quad
\underbrace{25,\ldots,30}_{\mathtt{E}}.
$$

This constructs $W_{c_2}$. The tensor giving
$\mu=2$ is obtained by adding the correction in
[Definition 6C.1](#def:corrected); the raw web still has the forbidden
$v^{-1}$ coordinate in [Equation 5C.1](#eq:raw-two-coordinate).

<a id="fig:assembly" name="fig:assembly"></a>

![Figure 12. Assembly of two blocks](figures/figure-12.png)

**Figure 12.** The assembly $\Psi_{\mathtt E}\longmapsto \Psi_{\mathtt M}\Psi_{\mathtt E}\longmapsto \Psi_{\mathtt M}^2\Psi_{\mathtt E} \longmapsto \Psi_{\mathtt S}\Psi_{\mathtt M}^2\Psi_{\mathtt E}$. The boundary arcs group the external outputs.
Thicker edges are the three-strand joins; they are ordinary web edges.
Square boundary markers denote the three outputs still to be joined. [Diagram description](diagrams.md#figure-12).

<a id="section-6C" name="section-6C"></a>

### 6C. Iteration

The iteration is shown in [Figure 13](#fig:interface).

<a id="def:corrected" name="def:corrected"></a>

**Definition 6C.1.** Let $\mathcal E=V^{\otimes3}\oplus\mathbf{1}$. Its standard basis consists
of the $27$ three-letter states and a scalar state $e_*=(0,1)$.
With the maps just defined, put

<a id="eq:maps" name="eq:maps"></a>

**Equation 6C.2.**

$$
\mathsf{p}=(\Psi_{\mathtt S},0),\qquad
T=\begin{pmatrix}\Psi_{\mathtt M}&-\Psi_{+}\\\Psi_{-}&-d\tau^3\end{pmatrix},\qquad
\boldsymbol{\rho}=\binom{\Psi_{\mathtt E}}{\tau^2}.
$$

Their types are

$$
\mathsf{p}:\mathcal E\to V^{\otimes6},\quad
T:\mathcal E\to\mathcal E\otimes V^{\otimes9},\quad
\boldsymbol{\rho}:\mathbf{1}\to\mathcal E\otimes V^{\otimes6}.
$$

Define $\boldsymbol{\rho}_0=\boldsymbol{\rho}$ and, with $I_j$ the identity on $V^{\otimes j}$,

<a id="eq:iterate" name="eq:iterate"></a>

**Equation 6C.3.**

$$
\boldsymbol{\rho}_{k+1}=(T\otimes I_{9k+6})\boldsymbol{\rho}_k\quad(k\ge0),
\qquad \beta_m=(\mathsf{p}\otimes I_{9m+6})\boldsymbol{\rho}_m.
$$

Thus $\beta_m:\mathbf{1}\to V^{\otimes(12+9m)}$ is an invariant tensor.

<a id="fig:interface" name="fig:interface"></a>

![Figure 13. The corrected block](figures/figure-13.png)

**Figure 13.** Composition through the $28$-dimensional connecting
space $\mathcal E$. Attachments run from the tail on the right to the
prefix on the left; external outputs are ordered from left to right.
The table shows the four transitions in $T$. Each transition creates
nine external outputs. The no-strand case is the scalar summand
$\mathbf{1}$, which adds no boundary point. [Diagram description](diagrams.md#figure-13).

| $T$ | input: three strands | input: no strands |
| --- | --- | --- |
| output: three strands | $\Psi_{\mathtt M}$ | $-\Psi_{+}$ |
| output: no strands | $\Psi_{-}$ | $-d\tau^3$ |

The map $\Psi_{-}$ takes the three connecting strands to nine external
outputs, reserving no strands for the next attachment. The map $-\Psi_{+}$
starts with no connecting strands and creates three reserved and nine
external outputs. The map $-d\tau^3$ keeps the no-strand state and adds
nine external outputs. Every term of the final tensor still has
the same $12+9m$ positive boundary points.
The maps $\mathsf{p}$ and $\boldsymbol{\rho}$ supply the prefix and tail.

We abbreviate the composition in [Equation 6C.3](#eq:iterate) by
$\mathsf{p} T^m\boldsymbol{\rho}$, with identity maps on previously created external
strands understood. Its output order is the six-strand prefix,
$m$ nine-strand blocks, and the six-strand tail. All coordinates
are integral Laurent polynomials.

We next prove that these correction maps remove all unwanted constant
and negative powers of $v$, so that $\beta_m=b_{c_m}$.

<a id="sec:canonicality" name="sec:canonicality"></a>

## 7. Canonicality from local degree bounds

By [Proposition 3D.2](#thm:canonical), we must show that $\beta_m$ is bar invariant
and congruent to $e_{c_m}$ modulo $v$ in the standard tensor lattice.
The main work is to control the degrees of all tensor coordinates
at once.

We change coordinates on $\mathcal E$ to replace the prefix $\mathsf{p}$,
block $T$ and tail $\boldsymbol{\rho}$ by $\widehat p,\widehat T,\widehat\rho$,
defined in [Section 7B](#loc:gauge). The final tensor is unchanged:

$$
\widehat p\,\widehat T^{\,m}\widehat\rho=\mathsf{p} T^m\boldsymbol{\rho}=\beta_m.
$$

We will show that these transformed maps have coefficients in $R=\mathbb{Z}[v]$.
In degree zero, $\widehat\rho$ gives $AAA\otimes e_{\mathtt{E}}$,
each $\widehat T$ preserves $AAA$ and adds $\mathtt{M}$, and
$\widehat p$ replaces $AAA$ by $\mathtt{S}$. Composing these terms gives
$e_{c_m}$ for every $m$.

<a id="section-7A" name="section-7A"></a>

### 7A. The local paths

We begin with the degree estimates for the small pieces of a block.
For the local bounds here and in [Section 8](#sec:readout), degree means
degree in ${v^{-1}}$. In particular,

$$
\deg_{{v^{-1}}}(v^k)=-k,\qquad \deg_{{v^{-1}}}0=-\infty.
$$

An integral Laurent polynomial lies in $R$ exactly when its degree
is at most zero; it lies in $v R$ when that degree is strictly negative.
For a map with entries in $R$, write $M[0]$ for its matrix of constant coefficients.

Words in the local tables abbreviate standard tensors. We also write
$|s\rangle=e_s$ and use $\langle s|$ for the corresponding coordinate
functional, and $[a<b]=\delta_{a<b}$ for indicators.

Keep $\mathsf R_i=H_{i+1}Y_i$ and $\mathsf S=H_2H_1Y_0$ from
[Section 6A](#sec:localmaps), and put $\mathsf L_i=H_iY_{i+1}$.
We also use these growth abbreviations for their upward tensor maps;
then $Y_i$ is a split and $a_i$ is a cup. A path 
chooses one monomial from each local coefficient; its
degree is the sum of their degrees. The elementary tables show that
all coefficients of an individual web are nonnegative and that the
only branch of positive ${v^{-1}}$-degree of $H$ is $AC\mapsto v^{-1} AC$.
Thus the degree of a nonzero web coordinate is the largest
degree of its compatible paths.

<a id="loc:nonpositive" name="loc:nonpositive"></a>

**Lemma 7A.1.** Every path through $y$, a cup, $\mathsf R_i$, or $\mathsf L_i$ has degree at most
zero. In $\mathsf S$, the only path of positive ${v^{-1}}$-degree is

$$
ABC\xrightarrow{Y_0,0}ABBC
 \xrightarrow{H_1,0}ACAC\xrightarrow{H_2,1}ACAC.
$$

Its degree and multiplicity are one. Furthermore

<a id="loc:Srow" name="loc:Srow"></a>

**Equation 7A.2.**

$$
\langle ACAC|\mathsf S=v^{-1}\langle ABC|+\langle ACB|+\langle BAC|,
 \qquad \mathsf S(AAA)=AAAB+v BAAA.
$$

*Proof.* 
The assertions for $y$ and a cup follow from their tables. In
$\mathsf R$, a degree-one branch of $H$ requires the right output of
the preceding $y$ to be $A$. That branch of $y$ has degree $-1$, so
the total is at most zero. In $\mathsf L$, the same argument uses the
left output $C$ of $y$.

A path of positive degree through $\mathsf S$ must use the degree-one term
of the last $H$ and a degree-zero path through the preceding
$\mathsf R$. Thus the first $H$ must output $A$ on its right.
The possibilities are $AA\to AA$, $AB\to BA$, $BB\to CA$ and
$CA\to CA$. The first two require a preceding split of degree $-1$;
the last already has degree $-1$. Hence only $BB\to CA$ remains.
Its preceding split is $A\to AB$, and the last $H$ forces the third
input to be $C$. This is the displayed path.

For output $ACAC$, the complete three paths are

$$
\begin{array}{c|ccc|r}
 &\text{after }Y_0&\text{after }H_1&\text{after }H_2&\deg_{{v^{-1}}}\\\hline
ABC&ABBC&ACAC&ACAC&1\\
ACB&ABCB&ACBB&ACAC&0\\
BAC&ACAC&ACAC&ACAC&0
\end{array}.
$$

They exhaust the choices in the $H$ table. The formula at $AAA$
follows by applying that table to the two terms of $y(A)$. ∎

In the notation above, the block in [Equation 6A.1](#eq:growth) has downward string
$\Psi_{\mathtt M}:Y_2Y_6Y_7\mathsf R_1\mathsf S \mathsf R_2\mathsf L_3\mathsf R_1\mathsf S$.
The only possible degree increases in $\Psi_{\mathtt M}$ therefore come from its two
occurrences of $\mathsf S$. To study the part between them, put

$$
X_4=V^-\otimes V^+\otimes V^+\otimes V^-,\qquad
X_7=V^{---+--+},\qquad X_8=V^{+--++--+}.
$$

Here $V^S$ denotes the signed tensor product defined in
[Section 3](#sec:webs).
Let $M_{\mathrm{loc}}:X_4\to X_7$ have downward string
$\mathsf R_2\mathsf L_3\mathsf R_1$, and set

$$
N_{\mathrm{loc}}=(\mathsf S\otimes I_{V^{+--+}})
M_{\mathrm{loc}}\mathsf S:V^{\otimes3}\to X_8.
$$

The rightmost $\mathsf S$ has positive inputs and the leftmost has
negative inputs. The map $O:X_8\to V^{\otimes12}$ already defined in
[Section 6A](#sec:localmaps) has string $Y_2Y_6Y_7\mathsf R_1$.
Expanding the growth strings gives
$\Psi_{\mathtt M}=ON_{\mathrm{loc}}$ and $\Psi_{+}=O\kappa_8$. This factorization lets us locate
the term canceled by the correction $\Psi_{+}$.

<a id="loc:gauge" name="loc:gauge"></a>

### 7B. An integral coordinate system

The block $T$ has some positive ${v^{-1}}$-degrees, so reducing it
modulo $v$ is not yet possible. We change coordinates on $\mathcal E$
so that the prefix $\mathsf{p}$, block $T$ and tail $\boldsymbol{\rho}$ become maps
$\widehat p,\widehat T,\widehat\rho$ with entries in $R$.

For a three-letter state $s$, define

$$
h_s=[s\in\{ABC,ACB,BAC\}],\quad
\Delta=\operatorname{diag}(v^{-h_s}),\quad
\mathsf J=\begin{pmatrix}I&0\\-v\eta&1\end{pmatrix},\quad
G=\operatorname{diag}(\Delta,-1)\mathsf J.
$$

Put $\widehat T=(G\otimes I_9)TG^{-1}$,
$\widehat p=\mathsf{p} G^{-1}$, and
$\widehat\rho=(G\otimes I_6)\boldsymbol{\rho}$.
With the identity maps on exterior strands understood, adjacent factors
$G^{-1}G$ cancel in $\widehat p\,\widehat T^{\,m}\widehat\rho$, giving $\beta_m$ as above.
We use $G$ only to estimate coordinates.

Here is the reason for the choice of $G$. The map $N_{\mathrm{loc}}$
has one degree-two term, at input $ABC$ and output $(AC)^4$.
The tensor $\kappa_8$ has coefficient $1$ at $(AC)^4$, and
$\eta(ABC)=v^{-3}$. Hence $v\kappa_8\eta$ has exactly the same degree-two
term. The triangular matrix $\mathsf J$ introduces this cancellation, while
$\Delta$ rescales the three states $ABC,ACB,BAC$ to compensate for
the remaining positive degrees. Negating the scalar 
coordinate makes the two constant transitions in
[Section 8](#sec:readout) positive.

<a id="loc:outer" name="loc:outer"></a>

**Lemma 7B.1.** Every coefficient of $(\Delta\otimes I_9)O$ belongs to $R$.

*Proof.* 
Only the first three output letters determine the shift $h_s$.
The two splits at positions six and seven have nonpositive degree
and do not affect those letters.
The relevant local piece is $\mathsf R$ followed by $y$ on its second
output, with an unchanged letter $a$ on the left. Write the first three
final letters as $apr$. If this is $ABC$ or $BAC$, then $r=C$ is the
left output of $y$, forcing degree $-1$ at that $y$;
the preceding $\mathsf R$ has degree at most zero by
[Lemma 7A.1](#loc:nonpositive). If it is $ACB$,
then $p=C$ forces degree $-1$ at the first $y$ inside $\mathsf R$.
An $H$ of degree one could cancel this only via $AC\to AC$;
the last $y$ then has input $A$, and producing $r=B$ forces its
degree $-1$ branch. Thus every output with $h_s=1$ has degree at most $-1$ before
rescaling. For outputs with $h_s=0$, [Lemma 7A.1](#loc:nonpositive)
applies directly. ∎

<a id="loc:offender" name="loc:offender"></a>

**Lemma 7B.2.** The only monomial of $N_{\mathrm{loc}}$ with degree exceeding $h_s$ at input $s$
is

$$
v^{-2}\,|ACACACAC\rangle\langle ABC|,
$$

with coefficient one.

*Proof.* 
Work backwards along a degree-zero path through $M_{\mathrm{loc}}$
whose output starts with $ABC$. This forces

<a id="loc:middlepath" name="loc:middlepath"></a>

**Equation 7B.3.**

$$
ACAC\xrightarrow{\mathsf R_1}ABBBC
\xrightarrow{\mathsf L_3}ABBCAC
\xrightarrow{\mathsf R_2}ABCACAC.
$$

Indeed, the last $\mathsf R$ must have its first output $C$. Its $y$ has
degree $-1$ and its $H$ must be $AC\to v^{-1} AC$, forcing input $BC$
and output $CAC$. The preceding $\mathsf L$ must have first output $C$;
in degree zero this forces input $BC$, $y(C)=BC$ and $H(BB)=CA$,
again giving $CAC$. The first $\mathsf R$ must now output $BBB$;
its only degree-zero route starts at $CA$ and uses $y(C)=BC$,
$H(CA)=BB$. The unchanged first letter is $A$.

Both copies of $\mathsf S$ have degree at most one. A degree-two path
must use their positive branches and the degree-zero middle path,
which gives exactly the stated term. For $s\notin\{ABC,ACB,BAC\}$,
a positive path would have to use degree zero in the first $\mathsf S$
and in $M_{\mathrm{loc}}$, followed by the positive second $\mathsf S$.
[Equation 7B.3](#loc:middlepath) then requires the first $\mathsf S$ to end at
$ACAC$ in degree zero, excluded by [Equation 7A.2](#loc:Srow). For $ACB,BAC$, a degree-one term does not exceed $h_s$. For $ABC$,
only degree two exceeds $h_s$. These cases cover all input states. ∎

<a id="loc:upper" name="loc:upper"></a>

**Lemma 7B.4.** Every entry of

$$
\bigl(\Delta(\Psi_{\mathtt M}-v\Psi_{+}\eta)\Delta^{-1},\Delta \Psi_{+}\bigr)
$$

belongs to $R$.

*Proof.* 
The unique constant monomial of the four-cup tensor $\kappa_8$ is
$(AC)^4$. On a permutation $s$ of $ABC$, the tripod evaluation $\eta$ has coefficient
$v^{\operatorname{inv}(s)-3}$. The largest degree of $v\kappa_8\eta$ at input $s$ is
$2-\operatorname{inv}(s)$, which is at most $h_s$ except at $s=ABC$.
There its unique degree-two monomial is precisely the one in
[Lemma 7B.2](#loc:offender). Thus

$$
(N_{\mathrm{loc}}-v\kappa_8\eta)\Delta^{-1}\in\operatorname{Mat}(R).
$$

The coefficient of the canceled term is $1$ in both maps. Since
$\Psi_{\mathtt M}=ON_{\mathrm{loc}}$, $\Psi_{+}=O \kappa_8$, and $\Delta O$ has entries in $R$
by [Lemma 7B.1](#loc:outer), multiplication proves both assertions. ∎

<a id="loc:lower" name="loc:lower"></a>

### 7C. The lower row and a capping identity

We next estimate the lower row of $\widehat T$. For this we use a
web identity obtained by capping the first three outputs of $\Psi_{\mathtt M}$. Its square resolutions produce $d\Psi_{-}$ and eleven further
web maps. Define their sum by $\mathcal H=\sum_{j=1}^{11}\mathcal H_j$, where
$\mathcal H_j=P_j'h_j'$ and $P_j'$ has nine positive outputs. As in the table
for $\Psi_{-}$, the last column gives the input signs of the prefix map.

|  | Downward string for $P_j'$ | $h_j'$ | Input of $P_j'$ |
| --- | --- | --- | --- |
| $\mathcal H_1$ | $Y_1Y_3Y_4a_4\mathsf R_1$ | $I$ | $+++$ |
| $\mathcal H_2$ | $Y_1Y_3Y_4Y_3Y_2Y_1$ | $I$ | $+++$ |
| $\mathcal H_3$ | $Y_1Y_2a_2Y_2Y_1Y_1$ | $\lambda_2$ | $+-$ |
| $\mathcal H_4$ | $Y_1Y_3Y_4\mathsf R_0Y_1\mathsf R_0Y_1$ | $\lambda_2E_1$ | $+-$ |
| $\mathcal H_5$ | $Y_1a_1Y_1Y_2Y_1Y_1$ | $\lambda_2$ | $+-$ |
| $\mathcal H_6$ | $Y_0Y_3Y_4Y_3Y_3\mathsf S$ | $I$ | $+++$ |
| $\mathcal H_7$ | $Y_0Y_2a_2Y_2a_2$ | $\lambda_1E_2$ | $-+$ |
| $\mathcal H_8$ | $Y_0Y_2a_2Y_2\mathsf R_0$ | $I$ | $+++$ |
| $\mathcal H_9$ | $Y_0Y_1Y_2Y_1Y_2a_2$ | $\lambda_1$ | $-+$ |
| $\mathcal H_{10}$ | $Y_0Y_1Y_2Y_1Y_2\mathsf R_0Y_1$ | $\lambda_2$ | $+-$ |
| $\mathcal H_{11}$ | $Y_0Y_1Y_2Y_1Y_1a_1$ | $\lambda_1$ | $-+$ |

The last row of the table for $\Psi_{-}$ gives $D_8=\tau^3\eta$.
Set $D_0=\Psi_{-}-D_8$, and write
$\operatorname{asc}(abc)=[a<b]+[b<c]$ for the number of adjacent
ascents in a three-letter input. We first bound the degrees of
$D_0$ and $\mathcal H$, then prove the capping identities.

<a id="loc:ascent" name="loc:ascent"></a>

**Lemma 7C.1.** At every exterior state $\omega$ and input $s$,

$$
\deg_{{v^{-1}}}(D_0)_{\omega,s},\ \deg_{{v^{-1}}}\mathcal H_{\omega,s}\le\operatorname{asc}(s)\le1+h_s.
$$

*Proof.* 
Except for $P_1$ in $D_1$ and $P_6'$ in $\mathcal H_6$, all prefix strings
use only nonpositive $y$, cup, and $\mathsf R$ pieces. In those two
exceptions, $\mathsf S$ acts first on the original three-strand input and
the remaining pieces are nonpositive; their bound is $[s=ABC]$.
Their attached maps $h_1$ and $h'_6$ are identities, so this bound
is at most $\operatorname{asc}(s)$.

It remains to bound the small maps attached to the nonpositive
prefixes. The maps $I,\lambda_1,\lambda_2$ have degree at most
$\operatorname{asc}(abc)$ from [Equation 3C.1](#eq:localmaps). For $\lambda_2E_1$, when $a\ne b$,
the two possible degrees are

$$
\epsilon(a,b)+[b<c],\qquad [a<c],\quad
\epsilon(a,b)=\begin{cases}1&a<b,\\-1&a>b.\end{cases}
$$

The first is at most $\operatorname{asc}(abc)$; the second is too, since no adjacent
ascent implies $a\ge b\ge c$. When $a=b$, the map is zero.
For $\lambda_1E_2$ the degrees are $[a<b]+\epsilon(b,c)$ and $[a<c]$,
with the same proof. Composition and summation preserve the bounds.
Finally, two strict ascents force $s=ABC$, so $\operatorname{asc}(s)\le1+h_s$. ∎

<a id="loc:openidentity" name="loc:openidentity"></a>

**Lemma 7C.2.** With all boundary positions fixed,

<a id="loc:openidentities" name="loc:openidentities"></a>

**Equation 7C.3.**

$$
\eta \Psi_{\mathtt M}=d\Psi_{-}+\mathcal H,\qquad \eta \Psi_{+}=d^2\tau^3.
$$

(The equation $\eta \Psi_{+}=d^2\tau^3$ is displayed in [Figure 14](#loc:fun).)

<a id="loc:fun" name="loc:fun"></a>

![Figure 14. Two successive digons](figures/figure-14.png)

**Figure 14.** The identity $\eta \Psi_{+}=d^2\tau^3$, with the two common
tripods suppressed. The six-output core has string
$Y_0H_0a_1Y_0a_0$. Its first three outputs are capped. Each
highlighted digon removes two vertices and contributes $d$. [Diagram description](diagrams.md#figure-14).

*Proof.* 
For the first identity, cap the first three outputs of $\Psi_{\mathtt M}$.
Resolve the indicated square in [Figure 15](#loc:firstsquare). Its branches
are $R_1$ and $R_{22}$. A digon removal in the second branch gives
$R_{22}=dR_{23}$. The complete square-reduction tree is

$$
\begin{array}{rcl@{\qquad}rcl}
R_1&=&R_2+R_{11}&R_{23}&=&R_{24}+R_{31}\\
R_2&=&R_3+\mathcal H_4&R_{24}&=&R_{25}+D_4\\
R_3&=&R_4+R_7&R_{25}&=&R_{26}+D_6\\
R_4&=&\mathcal H_3+\mathcal H_5&R_{26}&=&D_8+D_7\\
R_7&=&\mathcal H_2+\mathcal H_1&R_{31}&=&R_{32}+R_{35}\\
R_{11}&=&R_{12}+R_{17}&R_{32}&=&D_3+D_5\\
R_{12}&=&R_{13}+\mathcal H_{10}&R_{35}&=&D_2+D_1\\
R_{13}&=&\mathcal H_{11}+\mathcal H_9&&&\\
R_{17}&=&R_{18}+\mathcal H_6&&&\\
R_{18}&=&\mathcal H_7+\mathcal H_8.&&&
\end{array}
$$

[Appendix B](#loc:atlasappendix) displays every local relation and every
terminal beside the corresponding defining map. Each square has
coefficient one in both resolutions. Summing the left column gives
$\mathcal H$, and summing the right column gives $\Psi_{-}$.

The morphism $\Psi_{+}$ consists of its core with six boundary vertices, with leading word
$ABACBC$, followed by two tripods; this follows by reading its
displayed growth string. Capping the first three legs of that core
exposes a digon and then a second digon. Their removals leave a tripod.
The other two tripods are unchanged, giving the second identity. ∎

<a id="loc:firstsquare" name="loc:firstsquare"></a>

![Figure 15. First square after capping](figures/figure-15.png)

**Figure 15.** First square in $\eta \Psi_{\mathtt M}$. Boundary $1,\ldots,9$ consists of
the outputs; $12,11,10$ are the inputs in their linear order.
Hollow vertices are sources and filled vertices are sinks, as in
[Figure 3](#fig:relations).
The highlighted face is replaced by its two non-crossing smoothings.
Subsequent relations are included in [Appendix B](#loc:atlasappendix). [Diagram description](diagrams.md#figure-15).

<a id="loc:lowerrow" name="loc:lowerrow"></a>

**Lemma 7C.4.** Every entry in the lower row of $\widehat T$ belongs to $R$.
Its constant column at input $AAA$ is zero.

*Proof.* 
Multiplying $(G\otimes I_9)TG^{-1}$, its lower row is

$$
\left(
\bigl(v\eta \Psi_{\mathtt M}-\Psi_{-}-v(v\eta \Psi_{+}-d\tau^3)\eta\bigr)\Delta^{-1},
v\eta \Psi_{+}-d\tau^3
\right).
$$

Now use [Equation 7C.3](#loc:openidentities), $v d-1=v^2$ and
$\Psi_{-}=D_0+\tau^3\eta$. The lower row becomes

<a id="loc:lowerformula" name="loc:lowerformula"></a>

**Equation 7C.5.**

$$
\left((v^2D_0+v\mathcal H-v^4\tau^3\eta)\Delta^{-1},v^2d\tau^3\right).
$$

After the input shift $-h_s$, the first two terms have degrees
at most $-1$ and $0$, respectively,
by [Lemma 7C.1](#loc:ascent). The term containing $\eta$ has degree at most $-2$: its evaluation degrees on $ABC,ACB,BAC,BCA,CAB,CBA$ are $3,2,2,1,1,0$, and the shift is $-4-h_s$. The last term has degree at most $-1$.
At input $AAA$, $\operatorname{asc}(AAA)=0$ and $\eta(AAA)=0$, so the first two terms have
degrees at most $-2$ and $-1$. Thus that column has zero constant. ∎

<a id="loc:ends" name="loc:ends"></a>

### 7D. The constant state and the two ends

Both rows of $\widehat T$ now have entries in $R$. To identify its
constant action, we need only the input state $AAA$. The following
three lemmas track it through the block, prefix and tail.

<a id="loc:constantblock" name="loc:constantblock"></a>

**Lemma 7D.1.** The constant part of $\widehat T$ at input $AAA$ is exactly
$AAA\otimes e_{\mathtt{M}}$, with coefficient one.

*Proof.* 
The tripod evaluation $\eta$ vanishes at $AAA$, so there is no
upper-row correction.
By [Equation 7A.2](#loc:Srow), $\mathsf S(AAA)=AAAB+v BAAA$.
A degree increase at the second $\mathsf S$ requires the middle
map to output a word beginning with $ABC$. The map
$M_{\mathrm{loc}}$ fixes the first letter, so this is impossible
from $BAAA$. From $AAAB$, producing the second letter $B$ forces
the first $\mathsf R$, at input $AA$, to use its degree $-1$
output $BAA$. The first input of the last $\mathsf R$ is then $A$,
whose split cannot have first output $C$. Thus the second
$\mathsf S$ cannot increase the degree.

Only the $AAAB$ term can contribute degree zero. The unique
degree-zero branches of $\mathsf R$ at $AA$ and $\mathsf L$ at $BB$ force

$$
M_{\mathrm{loc}}(AAAB)[0]=AAAABBC,\qquad N_{\mathrm{loc}}(AAA)[0]=AAABABBC.
$$

All other terms have negative degree and remain negative under
$\Delta O$ by [Lemma 7B.1](#loc:outer). On the remaining term, the upward
operations $\mathsf R_1,Y_7,Y_6,Y_2$ give the sole constant path

$$
\begin{aligned}
AAABABBC&\to AAABBABBC\to AAABBABACC\\
&\to AAABBAACACC\to AAABBBAACACC=AAA\,\mathtt{M}.
\end{aligned}
$$

Other branches here have first three letters among $AAA,AAB,ABA,ABB$.
They all have $h_s=0$, so the rescaling adds no further constant term.
The lower-row assertion is [Lemma 7C.4](#loc:lowerrow). ∎

<a id="loc:initial" name="loc:initial"></a>

**Lemma 7D.2.** The coefficients of $\widehat p$ belong to $R$, and
$\widehat p[0](AAA)=e_{\mathtt{S}}$.

*Proof.* 
Since the scalar entry of $\mathsf{p}$ is zero,
$\widehat p=(\Psi_{\mathtt S}\Delta^{-1},0)$. In $\Psi_{\mathtt S}=Y_0Y_3\mathsf S$, the two $Y$'s
are nonpositive and [Lemma 7A.1](#loc:nonpositive) gives

$$
\deg_{{v^{-1}}} (\Psi_{\mathtt S})_{w,s}\le[s=ABC]\le h_s.
$$

For $AAA$, the constant path is
$AAA\to AAAB\to AAAAC\to ABAAAC$; the other branch in
[Equation 7A.2](#loc:Srow) has negative degree and stays negative through the remaining splits. ∎

<a id="loc:terminal" name="loc:terminal"></a>

**Lemma 7D.3.** All coefficients of $\widehat\rho$ belong to $R$, and

$$
\widehat\rho[0]=AAA\otimes e_{\mathtt{E}}.
$$

*Proof.* 
Cap the first three outputs of $\Psi_{\mathtt E}$ with $\eta$.
A square resolution and a digon removal give the relation in
[Figure 16](#fig:moresquares):

<a id="loc:tailidentity" name="loc:tailidentity"></a>

**Equation 7D.4.**

$$
\eta \Psi_{\mathtt E}=d\tau^2+W_{AABBCC}.
$$

<a id="fig:moresquares" name="fig:moresquares"></a>

![Figure 16. Terminal square](figures/figure-16.png)

**Figure 16.** The terminal square relation [Equation 7D.4](#loc:tailidentity). The second
branch is the tree with word $AABBCC$; the first becomes two tripods
after one digon removal. Boundary positions are fixed. [Diagram description](diagrams.md#figure-16).

The tree has downward string
$Y_1Y_2Y_1Y_0a_0$. Thus

$$
\widehat\rho=\binom{\Delta \Psi_{\mathtt E}}{v^2\tau^2+v W_{AABBCC}}.
$$

The scalar entry is strictly negative in ${v^{-1}}$-degree. The tree and
$\tau^2$ contain only nonpositive $Y$ and cup factors.

The upward tail string is $a_0,Y_0,Y_1,Y_2,Y_1,Y_2,Y_3,Y_2$.
It has one degree-zero path and eight paths of degree $-1$: choose
one $-1$ branch and zero branches elsewhere. They give

$$
\begin{array}{c|l}
\text{changed upward step}&\text{complete output word}\\\hline
\text{none}&AAABBCBCC\\
0&AAACBCBCB\\
1&BAABBCACC\\
2&ABACBCABC\\
3&AAABBCCBC\\
4&ABABACBCC\\
5&AABCABBCC\\
6&AAABCBBCC\\
7&AABABCBCC.
\end{array}
$$

None starts with $ABC,ACB,BAC$. The coordinates with these first
three letters therefore have degree at most $-2$ before the shift
by $\Delta$, and remain strictly negative afterwards. All other
coordinates are unshifted. This leaves the single constant state
$AAA\,\mathtt{E}$. ∎

<a id="section-7E" name="section-7E"></a>

### 7E. Identifying the dual canonical vector

We have the following.

<a id="prop:canonical" name="prop:canonical"></a>

**Lemma 7E.1.** For every integer $m\ge0$, the tensor in [Equation 6C.3](#eq:iterate) satisfies

$$
\beta_m=b_{c_m}.
$$

*Proof.* 
The transformed maps have entries in $R$ by
[Lemma 7B.4](#loc:upper), [Lemma 7C.4](#loc:lowerrow), [Lemma 7D.2](#loc:initial)
and [Lemma 7D.3](#loc:terminal). Their constant terms are

$$
\widehat\rho[0]=AAA\otimes e_{\mathtt{E}},\quad
\widehat T[0](AAA)=AAA\otimes e_{\mathtt{M}},\quad
\widehat p[0](AAA)=e_{\mathtt{S}}.
$$

Since the maps have entries in $R$, the constant term of a
composition is the composition of their constant terms.
Only the $AAA$ column of $\widehat T[0]$ is reached in this
induction. Induction therefore gives

$$
\beta_m=\widehat p\,\widehat T^{\,m}\widehat\rho
\equiv e_{\mathtt{S}}\otimes e_{\mathtt{M}}^{\otimes m}\otimes e_{\mathtt{E}}
=e_{c_m}\pmod {v\sum_w R e_w}.
$$

Thus every nonleading tensor coordinate belongs to $v R$.
Give $\mathcal E=V^{\otimes3}\oplus\mathbf{1}$ the componentwise
tensor bar. Each entry in [Equation 6C.2](#eq:maps) is a web map or a sum of
web maps, and the only nonconstant scalar is $-d$, with
$\overline d=d$. By [Lemma 3D.1](#lem:web-bar), the three maps commute
with the corresponding bars, so their composite $\beta_m$ is fixed
by the tensor bar. Together with the congruence above,
[Proposition 3D.2](#thm:canonical) identifies it uniquely with $b_{c_m}$. ∎

We now compute the coordinate required for the KL coefficient.

<a id="sec:readout" name="sec:readout"></a>

## 8. A two-state calculation of the coefficient

Fixing the boundary state $a_m$ turns the tensor construction into
a matrix calculation on the interface.

<a id="section-8A" name="section-8A"></a>

### 8A. The selected rows

We have identified $\beta_m$ with $b_{c_m}$. By [Proposition 4A.1](#thm:FKK),
it remains to extract the coefficient of $v$ in its coordinate at
$a_m=(ABC)^{N_m}$.

Fix the six external outputs of $\widehat p$ and $\widehat\rho$ to
$ABCABC$, and the nine external outputs of $\widehat T$ to $(ABC)^3$.
Denote the resulting row, $28\times28$ matrix and column by $p_a$,
$\mathsf A$ and $\rho_a$, respectively. Then

$$
[e_{a_m}]\beta_m=p_a \mathsf A^m \rho_a.
$$

All entries lie in $R$. To find the coefficient of $v$, we need the
leading terms of the ends and two rows of $\mathsf A[0]$.
The local tables in [Section 3C](#sec:elementarytensors) give the exact end vectors

<a id="loc:selectedends" name="loc:selectedends"></a>

**Equation 8A.1.**

$$
p_a=\langle ABC|+v\langle ACB|+v\langle BAC|,
\qquad
\rho_a=v\,ABC+v^2(ACB+BAC+2e_*).
$$

Here $e_*$ is the scalar interface state from [Definition 6C.1](#def:corrected).
For the prefix, the covector before multiplication by $\Delta^{-1}$ is
$v^{-1}\langle ABC|+\langle ACB|+\langle BAC|$ by [Equation 7A.2](#loc:Srow).
For the tail, the only nonzero unshifted coordinates are
$(\Psi_{\mathtt E})_{ABC,ABCABC}=v^2$, $(\Psi_{\mathtt E})_{ACB,ABCABC}=(\Psi_{\mathtt E})_{BAC,ABCABC}=v^3$. Multiplication by $G$ gives
[Equation 8A.1](#loc:selectedends), including $[e_{ABCABC}](v\eta \Psi_{\mathtt E}-\tau^2)=2v^2$ in the scalar
coordinate.

<a id="loc:tworows" name="loc:tworows"></a>

**Lemma 8A.2.** The rows of $\mathsf A[0]$ indexed by $ABC$ and $*$ vanish outside
the columns indexed by these same two states. In the order $ABC,*$,
their restriction is

$$
K=\begin{pmatrix}0&1\\2&0\end{pmatrix}.
$$

*Proof.* 
Both selected output states and the external state $(ABC)^3$ have
weight zero. Since the rescaling and tripod evaluation in $G$
preserve weights, only inputs of weight zero can contribute.
These are the six permutations of $ABC$ and the scalar state.
The table gives the complete rows; we need only their constant terms.

| input $s$ | $\mathsf A_{ABC,s}$ | $\mathsf A_{*,s}$ |
| --- | --- | --- |
| $ABC$ | $6v+6v^3$ | $2+12v^2+6v^4$ |
| $ACB$ | $5v^2+2v^4$ | $2v+8v^3+2v^5$ |
| $BAC$ | $5v^2+3v^4$ | $2v+10v^3+3v^5$ |
| $BCA$ | $2v^2$ | $2v+2v^3$ |
| $CAB$ | $v^2$ | $v+2v^3$ |
| $CBA$ | $0$ | $v^2$ |
| $*$ | $1$ | $v+v^3$ |

.

We derive the table from the elementary maps. Put $\omega=(ABC)^3$.
In the following formulas, a word $s$ denotes $\langle s|$.
Starting with the fixed output $ABC\omega$, the factorization
$\Psi_{\mathtt M}=ON_{\mathrm{loc}}$ gives the following covectors as we work
downward:

$$
\begin{aligned}
\langle ABC\omega|O={}&v^2 AACCACAC+v ACACACAC,\\
\langle ABC\omega|O\mathsf S={}&(1+v^2)ABCACAC+v BACACAC+v ACBACAC,\\
\langle ABC\omega|O\mathsf S M_{\mathrm{loc}}={}&(v+v^3)AACC+(1+3v^2+v^4)ACAC\\
&+(v+2v^3)ACBB+(v+v^3)BBAC\\
&+v^2(BBBB+BABC+ABCB).
\end{aligned}
$$

Applying the remaining $\mathsf S$ gives the raw $\Psi_{\mathtt M}$ row.
Pairing the first covector with $\kappa_8$ gives ${(\Psi_{+})_{ABC,\omega}}= v$.
For $D_0$ and $\mathcal H$, use the prefix covectors listed in
[Appendix A](#loc:covectorappendix) and then apply the small maps from
their defining tables. In the input order

$$
ABC,\ ACB,\ BAC,\ BCA,\ CAB,\ CBA,
$$

their sums are

$$
\begin{aligned}
(D_0)_{\omega,\bullet}
&=(5v^{-1}+3v,\ 4+v^2,\ 5+2v^2,\ 2v,\ 2v,\ v^2),\\
\mathcal H_{\omega,\bullet}
&=(2v^{-2}+8+3v^2,\ 2v^{-1}+5v+v^3,\ 2v^{-1}+6v+v^3,\ 2+v^2,\ 1+v^2,\ v).
\end{aligned}
$$

Substitute these rows and [Equation 3C.3](#eq:tripod) into the upper-row
formula in [Lemma 7B.4](#loc:upper) and the lower-row formula
[Equation 7C.5](#loc:lowerformula). This gives the displayed table. Its only
constant entries are $\mathsf A_{ABC,*}[0]=1$ and
$\mathsf A_{*,ABC}[0]=2$, which proves the lemma.

The constant $2$ comes from $\mathcal H_4$ and $\mathcal H_7$ in $\mathcal H$. Their coefficients at $(\omega,ABC)$ are
$v^{-2}+2$ and $v^{-2}$. Indeed,
$\lambda_2E_1(ABC)=\lambda_1E_2(ABC)=v^{-2}AC+v^{-1} BB$; the respective
prefix covectors are $(1+v^2)\langle AC|+v\langle BB|$ and
$\langle AC|$. The factor $v$ in the lower row and the input factor $v$ from
$\Delta^{-1}$ turn each $v^{-2}$ term into $1$.
All other $\mathcal H_j$ have degree at most zero there. ∎

<a id="section-8B" name="section-8B"></a>

### 8B. The coefficient

The two constant rows now give the coefficient for every block count.

<a id="loc:coefficient" name="loc:coefficient"></a>

**Lemma 8B.1.** For every $m\ge0$,

$$
[v][e_{a_m}]b_{c_m}=
\begin{cases}2^{m/2}&m\text{ even},\\0&m\text{ odd}.\end{cases}
$$

*Proof.* 
The three maps have entries in $R$, and [Equation 8A.1](#loc:selectedends)
gives $\rho_a[0]=0$ and $[v]\rho_a=e_{ABC}$. Thus the factor $\rho_a$ supplies
the single power of $v$; all other factors must contribute their
constant terms. Since $p_a[0]=\langle ABC|$, we obtain

$$
[v](p_a \mathsf A^m \rho_a)=e_{ABC}^{\mathsf T}\mathsf A[0]^m e_{ABC}
=(1,0)K^m(1,0)^{\mathsf T}.
$$

By [Lemma 8A.2](#loc:tworows), multiplying a row supported on $ABC,*$
by $\mathsf A[0]$ keeps it supported on those two coordinates. This
justifies the reduction to $K$. Finally, $K^2=2I$, so the expression
is $2^{m/2}$ for even $m$ and zero for odd $m$.
The identification with $b_{c_m}$ is [Lemma 7E.1](#prop:canonical). ∎

<a id="loc:smallreadout" name="loc:smallreadout"></a>

**Example 8B.2.** For $m=0$, [Equation 8A.1](#loc:selectedends) gives

$$
[e_{a_0}]b_{c_0}=p_a\rho_a=v+2v^3.
$$

Here the gap is $11$, and [Equation 4A.3](#eq:FKK) yields
$P^{J,+}_{x_0,y_0}(q)=2q^4+q^5$.
Its critical coefficient, and hence $\mu(x_0,y_0)$, is $1$.
For $m=2$, the first-order-calculation already suffices:

$$
[v][e_{a_2}]b_{c_2}=(1,0)K^2(1,0)^{\mathsf T}=2.
$$

This is the coefficient of $q^{22}$ in the ordinary polynomial.
The local argument proves the value without computing that polynomial.

<a id="S:Wrap" name="S:Wrap"></a>

### 8C. Wrap up

We are ready to prove the final results.

*Proof of [Theorem 1B.1](#thm:main).* 
By [Lemma 7E.1](#prop:canonical) and [Lemma 8B.1](#loc:coefficient),
$[v]([e_{a_{2r}}]b_{c_{2r}})=2^r$. The FKK identification in
[Proposition 4A.1](#thm:FKK) therefore gives $\mu(x_{2r},y_{2r})=2^r$. ∎

<a id="thm:rankbound" name="thm:rankbound"></a>

**Corollary 8C.1.** For $n\ge12$, we have

$$
\max_{x,y\in S_n}\mu(x,y)\ge2^{\lfloor(n-12)/18\rfloor}.
$$

The same holds, mutatis mutandis, in finite and affine types ABCD.

*Proof.* 
Take $r=\lfloor(n-12)/18\rfloor$ in [Theorem 1B.1](#thm:main) and use
$S_{12+18r}\subseteq S_n$. KL polynomials are unchanged under this
standard parabolic embedding. ∎

**Remark 8C.2.** The following are consequences of [Corollary 8C.1](#thm:rankbound)
in conjunction with the cited references.

1. First extension dimensions between simple modules for algebraic
groups and finite groups of Lie type can grow at least exponentially
with the rank, in sufficiently large characteristic. This follows from
\[[PS11](#bib-ParshallScott), [SX10](#bib-SX)\].

2. Indecomposables of composition length two in three-block parabolic
category $\mathcal O$ of type A occur in projective families of
dimension growing at least exponentially with the rank. This follows from
\[[BGS96](#bib-BGS), [KMM21](#bib-KoMazorchukMrden)\].

3. Every complex projective variety occurs as a submodule variety
in a fixed such category, already for objects of Loewy length at
most two with composition factors drawn from two fixed simples. This follows from
\[[KMM21](#bib-KoMazorchukMrden), [Rin18](#bib-RingelGrassmannians)\].

4. Schubert normal slices with no nontrivial product decomposition
can have local intersection cohomology in the highest permitted
degree growing at least exponentially with the slice dimension. This follows from
\[[dCM09](#bib-deCataldoMigliorini), [KL80](#bib-KLPositivity)\].

5. Tensoring an indecomposable Soergel bimodule with a single
generating bimodule can yield summand multiplicities growing
at least exponentially with the rank. This follows from \[[EW14](#bib-EliasWilliamson), [KL79](#bib-KL)\];
see also \[[COT26](#bib-GrowthAffineHecke)\] for related tensor power growth.

<a id="sec:methods" name="sec:methods"></a>

## 9. Methods, AI assistance and AI declaration

We record how we found the family and how we used AI assistance.

<a id="section-9A" name="section-9A"></a>

### 9A. Human experience (personal account)

One lesson we have learned over our careers is that if things get
bad, they get very bad (see, e.g., \[[BT26](#bib-TorsionProliferation), [K+25](#bib-LinkDetection)\] 
for examples from our works). Looking at Warrington's tables \[[War11](#bib-Warrington)\],
we found it hard to believe that $\mu$-coefficients could be bounded.

Our experience with webs pointed in the same direction. The move
from $\mathfrak{sl}_2$ to $\mathfrak{sl}_3$ is a serious jump: often, $\mathfrak{sl}_2$ is nice, while
$\mathfrak{sl}_3$ seems to contain all the complexity.
And, at least in type A, KL theory and webs are essentially the
same thing. The familiar hexagon-in-hexagons picture in \[[KK99](#bib-KK)\] therefore gave us a natural starting
point. We expected unboundedness to come from pictures of this kind. (The contrast is: 
for $\mathfrak{sl}_2$, the web basis consists of Temperley–Lieb
diagrams without internal faces, and the corresponding
$\mu$-coefficients lie in $\{0,1\}$; even stronger, the corresponding parabolic 
KL polynomials themselves are monomials.)

**Remark 9A.1.** Our intuition that $\mathfrak{sl}_3$ contains all the complexity
goes further. Polo's theorem \[[Pol99](#bib-Polo99)\] says that all polynomials
occur as KL polynomials for symmetric groups, subject to the obvious
restrictions.
We believe that an appropriate version of this statement already
holds for permutations whose RSK shapes have at most three rows.
We also suspect that the largest $\mu$-coefficients in $S_n$ can grow
as fast as $2^{O(n^2)}$, already in three rows
(cf. \[[Lüb20](#bib-Luebeck), Lemma 2.8\]). The family in [Figure 17](#fig:mu19-candidate)
gives $19$ in $S_{27}$ and $2446$ in $S_{36}$ after the canonical
correction. For the computations and two variants, see
`mu19-candidates-and-results.pdf` in our repository \[[G+26b](#bib-GoLaTuVa-mu-code)\].
A second candidate family ([Figure 18](#fig:linear-mu)) would give $\mu=n$
in $S_{3n}$ for every $n\ge4$. Together with the known small examples,
this would realize every nonnegative integer as a $\mu$-coefficient.
For the geometric argument, which we have yet to check, see
`linear_mu_and_webs_summary.pdf` in the same repository.

<a id="fig:mu19-candidate" name="fig:mu19-candidate"></a>

![Figure 17. Candidate family of three-row webs](figures/figure-17.png)

**Figure 17.** A candidate family of shape $(N,N,N)$; see \[[G+26b](#bib-GoLaTuVa-mu-code)\] for details. [Diagram description](diagrams.md#figure-17).

<a id="fig:linear-mu" name="fig:linear-mu"></a>

![Figure 18. Candidate linear family of permutation pairs](figures/figure-18.png)

**Figure 18.** The first two pairs in the proposed family, with predicted
$\mu$-coefficients $4$ and $5$, respectively. Each dot marks $(i,w(i))$. [Diagram description](diagrams.md#figure-18).

$x=(3,2,1,9,8,7,6,5,4,12,11,10)$ in $S_{12}$, $y=(9,3,2,12,7,8,5,6,1,11,10,4)$ in $S_{12}$.

$x=(3,2,1,11,10,9,8,7,6,5,4,15,14,13,12)$ in $S_{15}$, $y=(11,3,2,15,9,10,7,8,5,6,1,14,13,12,4)$ in $S_{15}$.

The difficult part was turning that intuition into a proof.
We knew from the start that the necessary calculations would be
very hard by hand, but they seemed amenable to a machine.
That is where AI (mid-2026 models) came in: to help us get the calculations and
details straight, e.g. it found the correct 
family to look at as ours was a bit off.

We now give a few more details.

<a id="sec:origin" name="sec:origin"></a>

### 9B. The starting point

We began by computing KL left cell representations with an
implementation of Nguyen's method \[[Ngu20](#bib-Nguyen)\]. We generated the
cell $W$-graphs through $S_{19}$ and for selected larger partitions.
The larger weights led us to three-row tableaux and their webs.
We then looked for a boundary coefficient that we could compute
after correcting a web to its dual canonical vector.

**Remark 9B.1.** Our preliminary computational results were obtained with a Rust program which can be found 
on our associated page \[[G+26b](#bib-GoLaTuVa-mu-code)\].

Our starting example was the following pair of shape $(9,7,7)$,
with computed $W$-graph weight $2$:

$$
S^\circ=\begin{array}{rrrrrrrrr}
1&2&5&8&11&14&17&20&23\\
3&6&9&12&15&18&21&&\\
4&7&10&13&16&19&22&&
\end{array},\qquad
T^\circ=\begin{array}{rrrrrrrrr}
1&2&3&5&8&9&11&18&20\\
4&6&7&14&15&16&17&&\\
10&12&13&19&21&22&23&&
\end{array}.
$$

We completed both tableaux to shape $(9,9,9)$ by adding $24,26$ to
row two and $25,27$ to row three, obtaining $S^+,T^+$, see [Figure 19](#fig:cores1). Deleting the
added entries in reverse order removes the same corner from both
tableaux at each step. By \[[GY22](#bib-GossowYacobi), Proposition 3.3\], this
preserves the symmetrized $\mu$-coefficient, that is, the $W$-graph
weight of the unordered pair.

<a id="fig:cores1" name="fig:cores1"></a>

![Figure 19. Completing the seed tableaux](figures/figure-19.png)

**Figure 19.** The webs for $S^+,T^+$ and their
tableaux. Bold entries are the four added boxes. [Diagram description](diagrams.md#figure-19).

Rotate both webs by one boundary position, moving boundary vertex
$1$ to position $27$ and each vertex $i>1$ to position $i-1$.
With the boundary labels fixed, this gives the tableaux
$\operatorname{pr}(S^+),\operatorname{pr}(T^+)$, where
$\operatorname{pr}$ is promotion \[[PPR09](#bib-PPR), Theorem 2.5\].
Simultaneous promotion preserves the symmetrized $\mu$-coefficient
for rectangular tableaux \[[Rho10](#bib-Rhoades), Proposition 3.2\], so the
rotated pair still has $W$-graph weight $2$.

Motivated by the KK counterexample \[[KK99](#bib-KK)\], we
extended the hexagonal strip in the rotated target, with overlap at
boundary positions $13,22,31,\ldots$. This suggested the row words

$$
(ABC)^{6+3k},\qquad R_{\mathrm{seed}}\mathtt{M}^k\mathtt{E},\qquad
R_{\mathrm{seed}}=AABABBAACACC,\quad k\ge0,
$$

with $\mathtt{M},\mathtt{E}$ as in [Equation 2C.7](#eq:words). The case $k=1$ is the promoted pair just described, shown on the
left in [Figure 20](#fig:cores2). We computed its canonical correction, but did not find
a correction that worked for this whole family. We therefore looked
for a simpler start piece.

<a id="fig:cores2" name="fig:cores2"></a>

![Figure 20. Rotated seed and two-block target](figures/figure-20.png)

**Figure 20.** Left: the rotated seed
$R_{\mathrm{seed}}\mathtt{M}\mathtt{E}$. Right: the member $\mathtt{S}\mathtt{M}^2\mathtt{E}$.
Both source webs are products of consecutive tripods. [Diagram description](diagrams.md#figure-20).

<a id="section-9C" name="section-9C"></a>

### 9C. Choosing the start piece

Now we explain how the right web in [Figure 20](#fig:cores2) came about.
Robert's red-graph-reductions \[[Rob13](#bib-RobertFamily), [Rob15](#bib-RobertCharacterization)\]
suggested local correction terms. Such a reduction removes edges
bounding selected faces and reconnects the remaining half-edges by
specified pairings, preserving the ordered boundary
\[[Rob15](#bib-RobertCharacterization), Definition 4.1\]. For an exact paired
red graph in a non-elliptic web, the reduced web's projective module
is a direct summand of the original web module
\[[Rob15](#bib-RobertCharacterization), Theorem 3.12 and Proposition 4.4\].

In the seed, the six hexagons surrounding an endpoint hexagon form
such a red graph. Reducing at that end and applying the square and
digon relations suggested the six-letter prefix $\mathtt{S}$. Keeping $\mathtt{M}$
and $\mathtt{E}$ gave the family in [Equation 2C.7](#eq:words). The two families
are compared below; their indices $k$ and $m$ count blocks in their
respective constructions.

| Family | Source word | Target word | Block count |
| --- | --- | --- | --- |
| Seed | $(ABC)^{6+3k}$ | $R_{\mathrm{seed}}\mathtt{M}^k\mathtt{E}$ | $k\ge0$ |
| Theorem | $(ABC)^{4+3m}$ | $\mathtt{S}\mathtt{M}^m\mathtt{E}$ | $m\ge0$ |

See also [Figure 20](#fig:cores2).
Robert's theorem concerns module summands. The values of $\mu$ for
the modified start piece follow from [Section 7](#sec:canonicality) and
[Section 8](#sec:readout). Its base member has $\mu=1$, whereas the
initial seed has $W$-graph weight $2$.

<a id="section-9D" name="section-9D"></a>

### 9D. From a seed calculation to a uniform argument

For our family with two blocks, the complete canonical
correction has $94$ lower webs, as in [Equation 5C.2](#eq:94correction).
At the selected boundary state, the raw critical coefficient is $18$
and the correction contributes $16$, leaving $2$. Grouping the
correction terms by their behavior across a three-strand cut splits
this calculation into $18-10-6=2$: $\Psi_{\mathtt S}\Psi_{\mathtt M}\Psi_{+}\tau^2$ contributes
$10v$, and $\Psi_{\mathtt S}\Psi_{+}\Psi_{-}\Psi_{\mathtt E}-d\Psi_{\mathtt S}\Psi_{+}\tau^5$ contributes $6v$ to the amount
subtracted. These are the same terms grouped by their web-basis
coefficients as $18-3-13$ in [Section 5](#sec:basischange).

This grouping suggested adding the scalar coordinate to the
three-strand interface in [Section 6](#sec:construction). It allows one
fixed block to incorporate the correction for every $m$.

<a id="section-9E" name="section-9E"></a>

### 9E. AI assistance and verification

We did the usual back-and-forth dance with AI (classic 2026).
We supplied the computational program, the selected $W$-graph
edges, their web interpretation and the first conjectural family.
We first used AI assistance for figures. Later models accessed
through Claude, ChatGPT and Codex helped with code, the modified
start piece, correction terms, the repeated block, Lean formalization and the proof draft.
AI-assisted symbolic calculations also produced the interface basis
change and the square-reduction tree.

We checked the local formulas by the calculations in the paper and
by independent tensor computations. The code is available in \[[G+26b](#bib-GoLaTuVa-mu-code)\], and the scope of
the Lean formalization is described in [Remark 1E.1](#rem:verification).
We are responsible for the mathematical statements and for verifying
the theoretical and computational inputs.

<a id="loc:covectorappendix" name="loc:covectorappendix"></a>

## Appendix A. Details for Lemma 8A.2

Fix the nine outputs of each prefix $P_i$ or $P_j'$ to
$\omega=(ABC)^3$, and work downward through its growth string.
The tables give the resulting covector and the small map attached
to that prefix. Thus
$\langle\omega|D_i=(\langle\omega|P_i)h_i$, and similarly for $\mathcal H_j$.
Here a word $s$ denotes $\langle s|$.

The first table lists $D_1,\ldots,D_7$, whose sum is $D_0$.
The term $D_8=\tau^3\eta$ is treated separately in
[Equation 7C.5](#loc:lowerformula). The second table supplies the terms of
$\mathcal H$. All covectors follow from the elementary tables in
[Section 3](#sec:webs).

| Prefix | Covector | $h_i$ |
| --- | --- | --- |
| $P_1$ | $v^{-1} ABC+ACB+BAC$ | $I$ |
| $P_2$ | $v ABC+v^2BAC$ | $I$ |
| $P_3$ | $AC+v BB$ | $\lambda_2$ |
| $P_4$ | $v AC+v^2BB$ | $\lambda_2E_1$ |
| $P_5$ | $v^2AC$ | $\lambda_2$ |
| $P_6$ | $v AC$ | $\lambda_2E_1$ |
| $P_7$ | $AC$ | $\lambda_1$ |

| Prefix | Covector | $h_j'$ |
| --- | --- | --- |
| $P_1'$ | $ABC+v ACB$ | $I$ |
| $P_2'$ | $v^2ABC$ | $I$ |
| $P_3'$ | $v AC$ | $\lambda_2$ |
| $P_4'$ | $(1+v^2)AC+v BB$ | $\lambda_2E_1$ |
| $P_5'$ | $v^3AC$ | $\lambda_2$ |
| $P_6'$ | $ABC+v ACB+v BAC$ | $I$ |
| $P_7'$ | $AC$ | $\lambda_1E_2$ |
| $P_8'$ | $ABC+v BAC$ | $I$ |
| $P_9'$ | $v AC$ | $\lambda_1$ |
| $P_{10}'$ | $v AC+v^2BB$ | $\lambda_2$ |
| $P_{11}'$ | $v^3AC$ | $\lambda_1$ |

For example, the first four downward steps of the $P_1$ string give

$$
ABCABCABC\to ACABCABC\to ACACABC\to ACACAC\to ACAC.
$$

The coefficient along this path is $1$. Applying the remaining
$\mathsf S$ gives
$v^{-1}\langle ABC|+\langle ACB|+\langle BAC|$ by
[Equation 7A.2](#loc:Srow), the first covector in the table.
Composing the listed covectors on the right with their small maps
and summing gives the $D_0$ and $\mathcal H$ rows used in
[Lemma 8A.2](#loc:tworows).

<a id="loc:atlasappendix" name="loc:atlasappendix"></a>

## Appendix B. Details for Lemma 7C.2

The atlas proves $\eta \Psi_{\mathtt M}=d\Psi_{-}+\mathcal H$ from
[Lemma 7C.2](#loc:openidentity). The diagrams $R_i$ form a reduction
tree: at each step we resolve the highlighted square or remove the
highlighted digon. The terminal diagrams are the eight maps $D_i$
and the eleven maps $\mathcal H_j$. The tables below locate each step and
each terminal identification. Each terminal is drawn once, with
its label in the reduction tree and its defining map written above it. The symbols $\mathsf R_i,\mathsf L_i$
in the growth strings denote local operations, whereas $R_i$ denotes
a diagram in this tree.

Boundary labels are fixed. Outputs $1,\ldots,9$ are followed around
the circle by inputs $12,11,10$. Hollow vertices are sources and
filled vertices are sinks. Each square resolution has coefficient
$1$; removing the sole digon contributes $d$.

| Reduction | Figure |
| --- | --- |
| $R_{0}=R_{1}+R_{22}$ | [21](#fig:atlas-r0) |
| $R_{1}=R_{2}+R_{11}$ | [22](#fig:atlas-r1) |
| $R_{2}=R_{3}+R_{10}$ | [23](#fig:atlas-r2) |
| $R_{3}=R_{4}+R_{7}$ | [24](#fig:atlas-r3) |
| $R_{4}=R_{5}+R_{6}$ | [25](#fig:atlas-r4) |
| $R_{7}=R_{8}+R_{9}$ | [26](#fig:atlas-r7) |
| $R_{11}=R_{12}+R_{17}$ | [27](#fig:atlas-r11) |
| $R_{12}=R_{13}+R_{16}$ | [28](#fig:atlas-r12) |
| $R_{13}=R_{14}+R_{15}$ | [29](#fig:atlas-r13) |
| $R_{17}=R_{18}+R_{21}$ | [30](#fig:atlas-r17) |
| $R_{18}=R_{19}+R_{20}$ | [31](#fig:atlas-r18) |
| $R_{22}=dR_{23}$ | [32](#fig:atlas-r22) |
| $R_{23}=R_{24}+R_{31}$ | [33](#fig:atlas-r23) |
| $R_{24}=R_{25}+R_{30}$ | [34](#fig:atlas-r24) |
| $R_{25}=R_{26}+R_{29}$ | [35](#fig:atlas-r25) |
| $R_{26}=R_{27}+R_{28}$ | [36](#fig:atlas-r26) |
| $R_{31}=R_{32}+R_{35}$ | [37](#fig:atlas-r31) |
| $R_{32}=R_{33}+R_{34}$ | [38](#fig:atlas-r32) |
| $R_{35}=R_{36}+R_{37}$ | [39](#fig:atlas-r35) |

| Terminal map | Figure |
| --- | --- |
| $R_{5}=\mathcal H_{3}$ | [41](#fig:atlas-term6) |
| $R_{6}=\mathcal H_{5}$ | [41](#fig:atlas-term7) |
| $R_{8}=\mathcal H_{2}$ | [41](#fig:atlas-term5) |
| $R_{9}=\mathcal H_{1}$ | [41](#fig:atlas-term5) |
| $R_{10}=\mathcal H_{4}$ | [41](#fig:atlas-term6) |
| $R_{14}=\mathcal H_{11}$ | [41](#fig:atlas-term10) |
| $R_{15}=\mathcal H_{9}$ | [41](#fig:atlas-term9) |
| $R_{16}=\mathcal H_{10}$ | [41](#fig:atlas-term9) |
| $R_{19}=\mathcal H_{7}$ | [41](#fig:atlas-term8) |
| $R_{20}=\mathcal H_{8}$ | [41](#fig:atlas-term8) |
| $R_{21}=\mathcal H_{6}$ | [41](#fig:atlas-term7) |
| $R_{27}=D_{8}$ | [40](#fig:atlas-term4) |
| $R_{28}=D_{7}$ | [40](#fig:atlas-term4) |
| $R_{29}=D_{6}$ | [40](#fig:atlas-term3) |
| $R_{30}=D_{4}$ | [40](#fig:atlas-term2) |
| $R_{33}=D_{3}$ | [40](#fig:atlas-term2) |
| $R_{34}=D_{5}$ | [40](#fig:atlas-term3) |
| $R_{36}=D_{2}$ | [40](#fig:atlas-term1) |
| $R_{37}=D_{1}$ | [40](#fig:atlas-term1) |

<a id="fig:atlas-r0" name="fig:atlas-r0"></a>

![Figure 21. Local reduction at 0](figures/figure-21.png)

**Figure 21.** Square resolution at $R_{0}$. [Diagram description](diagrams.md#figure-21).

<a id="fig:atlas-r1" name="fig:atlas-r1"></a>

![Figure 22. Local reduction at 1](figures/figure-22.png)

**Figure 22.** Square resolution at $R_{1}$. [Diagram description](diagrams.md#figure-22).

<a id="fig:atlas-r2" name="fig:atlas-r2"></a>

![Figure 23. Local reduction at 2](figures/figure-23.png)

**Figure 23.** Square resolution at $R_{2}$. [Diagram description](diagrams.md#figure-23).

<a id="fig:atlas-r3" name="fig:atlas-r3"></a>

![Figure 24. Local reduction at 3](figures/figure-24.png)

**Figure 24.** Square resolution at $R_{3}$. [Diagram description](diagrams.md#figure-24).

<a id="fig:atlas-r4" name="fig:atlas-r4"></a>

![Figure 25. Local reduction at 4](figures/figure-25.png)

**Figure 25.** Square resolution at $R_{4}$. [Diagram description](diagrams.md#figure-25).

<a id="fig:atlas-r7" name="fig:atlas-r7"></a>

![Figure 26. Local reduction at 7](figures/figure-26.png)

**Figure 26.** Square resolution at $R_{7}$. [Diagram description](diagrams.md#figure-26).

<a id="fig:atlas-r11" name="fig:atlas-r11"></a>

![Figure 27. Local reduction at 11](figures/figure-27.png)

**Figure 27.** Square resolution at $R_{11}$. [Diagram description](diagrams.md#figure-27).

<a id="fig:atlas-r12" name="fig:atlas-r12"></a>

![Figure 28. Local reduction at 12](figures/figure-28.png)

**Figure 28.** Square resolution at $R_{12}$. [Diagram description](diagrams.md#figure-28).

<a id="fig:atlas-r13" name="fig:atlas-r13"></a>

![Figure 29. Local reduction at 13](figures/figure-29.png)

**Figure 29.** Square resolution at $R_{13}$. [Diagram description](diagrams.md#figure-29).

<a id="fig:atlas-r17" name="fig:atlas-r17"></a>

![Figure 30. Local reduction at 17](figures/figure-30.png)

**Figure 30.** Square resolution at $R_{17}$. [Diagram description](diagrams.md#figure-30).

<a id="fig:atlas-r18" name="fig:atlas-r18"></a>

![Figure 31. Local reduction at 18](figures/figure-31.png)

**Figure 31.** Square resolution at $R_{18}$. [Diagram description](diagrams.md#figure-31).

<a id="fig:atlas-r22" name="fig:atlas-r22"></a>

![Figure 32. Local reduction at 22](figures/figure-32.png)

**Figure 32.** Digon removal at $R_{22}$, with coefficient $d$. [Diagram description](diagrams.md#figure-32).

<a id="fig:atlas-r23" name="fig:atlas-r23"></a>

![Figure 33. Local reduction at 23](figures/figure-33.png)

**Figure 33.** Square resolution at $R_{23}$. [Diagram description](diagrams.md#figure-33).

<a id="fig:atlas-r24" name="fig:atlas-r24"></a>

![Figure 34. Local reduction at 24](figures/figure-34.png)

**Figure 34.** Square resolution at $R_{24}$. [Diagram description](diagrams.md#figure-34).

<a id="fig:atlas-r25" name="fig:atlas-r25"></a>

![Figure 35. Local reduction at 25](figures/figure-35.png)

**Figure 35.** Square resolution at $R_{25}$. [Diagram description](diagrams.md#figure-35).

<a id="fig:atlas-r26" name="fig:atlas-r26"></a>

![Figure 36. Local reduction at 26](figures/figure-36.png)

**Figure 36.** Square resolution at $R_{26}$. [Diagram description](diagrams.md#figure-36).

<a id="fig:atlas-r31" name="fig:atlas-r31"></a>

![Figure 37. Local reduction at 31](figures/figure-37.png)

**Figure 37.** Square resolution at $R_{31}$. [Diagram description](diagrams.md#figure-37).

<a id="fig:atlas-r32" name="fig:atlas-r32"></a>

![Figure 38. Local reduction at 32](figures/figure-38.png)

**Figure 38.** Square resolution at $R_{32}$. [Diagram description](diagrams.md#figure-38).

<a id="fig:atlas-r35" name="fig:atlas-r35"></a>

![Figure 39. Local reduction at 35](figures/figure-39.png)

**Figure 39.** Square resolution at $R_{35}$. [Diagram description](diagrams.md#figure-39).

<a id="fig:atlas-term1" name="fig:atlas-term1"></a>
<a id="fig:atlas-term2" name="fig:atlas-term2"></a>
<a id="fig:atlas-term3" name="fig:atlas-term3"></a>
<a id="fig:atlas-term4" name="fig:atlas-term4"></a>

![Figure 40. Terminal maps D](figures/figure-40.png)

**Figure 40.** The terminal maps $D_1,\ldots,D_8$.
Each diagram shows the full composite $D_i=P_i h_i$.
Outputs are labeled $1,\ldots,9$; the three inputs are labeled
$12,11,10$ in their linear order. [Diagram description](diagrams.md#figure-40).

The diagram labels are $R_{37}=D_1=P_1$, $R_{36}=D_2=P_2$, $R_{33}=D_3=P_3\lambda_2$, $R_{30}=D_4=P_4\lambda_2E_1$, $R_{34}=D_5=P_5\lambda_2$, $R_{29}=D_6=P_6\lambda_2E_1$, $R_{28}=D_7=P_7\lambda_1$, $R_{27}=D_8=P_8\eta$.

<a id="fig:atlas-term5" name="fig:atlas-term5"></a>
<a id="fig:atlas-term6" name="fig:atlas-term6"></a>
<a id="fig:atlas-term7" name="fig:atlas-term7"></a>
<a id="fig:atlas-term8" name="fig:atlas-term8"></a>
<a id="fig:atlas-term9" name="fig:atlas-term9"></a>
<a id="fig:atlas-term10" name="fig:atlas-term10"></a>

![Figure 41. Terminal maps H](figures/figure-41.png)

**Figure 41.** The terminal maps $\mathcal H_1,\ldots,\mathcal H_{11}$. [Diagram description](diagrams.md#figure-41).

The diagram labels are $R_9=\mathcal H_1=P'_1$, $R_8=\mathcal H_2=P'_2$, $R_5=\mathcal H_3=P'_3\lambda_2$, $R_{10}=\mathcal H_4=P'_4\lambda_2E_1$, $R_6=\mathcal H_5=P'_5\lambda_2$, $R_{21}=\mathcal H_6=P'_6$, $R_{19}=\mathcal H_7=P'_7\lambda_1E_2$, $R_{20}=\mathcal H_8=P'_8$, $R_{15}=\mathcal H_9=P'_9\lambda_1$, $R_{16}=\mathcal H_{10}=P'_{10}\lambda_2$, $R_{14}=\mathcal H_{11}=P'_{11}\lambda_1$.

<a id="references" name="references"></a>

## References

<a id="bib-Ariki" name="bib-Ariki"></a>

**[Ari00].** 
S. Ariki.
 Robinson–Schensted correspondence and left cells.
 In *Combinatorial Methods in Representation Theory*,
Advanced Studies in Pure Mathematics, vol. 28, pages 1–20. Kinokuniya, Tokyo, 2000.
 <https://arxiv.org/abs/math/9910117>, [doi:10.2969/aspm/02810001](https://doi.org/10.2969/aspm/02810001).

<a id="bib-TorsionProliferation" name="bib-TorsionProliferation"></a>

**[BT26].** 
J. Baine and D. Tubbenhauer.
 Torsion proliferation.
 2026.
 <https://arxiv.org/abs/2609.31781>.

<a id="bib-BGS" name="bib-BGS"></a>

**[BGS96].** 
A. Beilinson, V. Ginzburg and W. Soergel.
 Koszul duality patterns in representation theory.
 *J. Amer. Math. Soc.*, 9(2):473–527, 1996.
 [doi:10.1090/S0894-0347-96-00192-0](https://doi.org/10.1090/S0894-0347-96-00192-0).

<a id="bib-BjornerBrenti" name="bib-BjornerBrenti"></a>

**[BB05].** 
A. Björner and F. Brenti.
 *Combinatorics of Coxeter Groups*.
 Graduate Texts in Mathematics, vol. 231. Springer, Berlin, 2005.
 [doi:10.1007/3-540-27596-7](https://doi.org/10.1007/3-540-27596-7).

<a id="bib-BrundanKleshchevBlocks" name="bib-BrundanKleshchevBlocks"></a>

**[BK09a].** 
J. Brundan and A. Kleshchev.
 Blocks of cyclotomic Hecke algebras and Khovanov–Lauda algebras.
 *Invent. Math.*, 178(3):451–484, 2009.
 <https://arxiv.org/abs/0808.2032>, [doi:10.1007/s00222-009-0204-8](https://doi.org/10.1007/s00222-009-0204-8).

<a id="bib-BrundanKleshchev" name="bib-BrundanKleshchev"></a>

**[BK09b].** 
J. Brundan and A. Kleshchev.
 Graded decomposition numbers for cyclotomic Hecke algebras.
 *Adv. Math.*, 222(6):1883–1942, 2009.
 <https://arxiv.org/abs/0901.4450>, [doi:10.1016/j.aim.2009.06.018](https://doi.org/10.1016/j.aim.2009.06.018).

<a id="bib-Chen" name="bib-Chen"></a>

**[Che18].** 
P. Chen.
 Non-trivial Kazhdan–Lusztig coefficients of affine Weyl groups.
 2018.
 <https://arxiv.org/abs/1804.02353>.

<a id="bib-GrowthAffineHecke" name="bib-GrowthAffineHecke"></a>

**[COT26].** 
K. Coulembier, J. O'Sullivan and D. Tubbenhauer.
 Growth in affine Hecke categories.
 2026.
 <https://arxiv.org/abs/2608.09197>.

<a id="bib-deCataldoMigliorini" name="bib-deCataldoMigliorini"></a>

**[dCM09].** 
M. A. A. de Cataldo and L. Migliorini.
 The decomposition theorem, perverse sheaves and the
topology of algebraic maps.
 *Bull. Amer. Math. Soc. (N.S.)*,
46(4):535–633, 2009.
 <https://arxiv.org/abs/0712.0349>, [doi:10.1090/S0273-0979-09-01260-9](https://doi.org/10.1090/S0273-0979-09-01260-9).

<a id="bib-Deodhar" name="bib-Deodhar"></a>

**[Deo87].** 
V. V. Deodhar.
 On some geometric aspects of Bruhat orderings. II. The parabolic analogue of Kazhdan–Lusztig polynomials.
 *J. Algebra*, 111:483–506, 1987.
 [doi:10.1016/0021-8693(87)90232-8](https://doi.org/10.1016/0021-8693(87)90232-8).

<a id="bib-Dyer" name="bib-Dyer"></a>

**[Dye87].** 
M. J. Dyer.
 Hecke algebras and reflections in Coxeter groups.
 PhD thesis, University of Sydney, 1987.
 <https://academicweb.nd.edu/~dyer/papers/dyerthesis.pdf>.

<a id="bib-EliasWilliamson" name="bib-EliasWilliamson"></a>

**[EW14].** 
B. Elias and G. Williamson.
 The Hodge theory of Soergel bimodules.
 *Ann. of Math. (2)*, 180(3):1089–1136, 2014.
 <https://arxiv.org/abs/1212.0791>, [doi:10.4007/annals.2014.180.3.6](https://doi.org/10.4007/annals.2014.180.3.6).

<a id="bib-FKK" name="bib-FKK"></a>

**[FKK98].** 
I. B. Frenkel, M. G. Khovanov and A. A. Kirillov, Jr.
 Kazhdan–Lusztig polynomials and canonical basis.
 *Transform. Groups*, 3(4):321–336, 1998.
 <https://arxiv.org/abs/q-alg/9709042>, [doi:10.1007/BF01234531](https://doi.org/10.1007/BF01234531).

<a id="bib-GarsiaMcLarnan" name="bib-GarsiaMcLarnan"></a>

**[GM88].** 
A. M. Garsia and T. J. McLarnan.
 Relations between Young's natural and the Kazhdan–Lusztig
representations of $S_n$.
 *Adv. Math.*, 69(1):32–92, 1988.
 [doi:10.1016/0001-8708(88)90060-6](https://doi.org/10.1016/0001-8708(88)90060-6).

<a id="bib-Affine" name="bib-Affine"></a>

**[G+26a].** 
T. Goertzen, A. Lacabanne, D. Tubbenhauer and P. Vaz.
 Annular webs and Guralnick's conjecture
 2026.
 <https://arxiv.org/abs/2610.34982>.

<a id="bib-GoLaTuVa-mu-code" name="bib-GoLaTuVa-mu-code"></a>

**[G+26b].** 
T. Goertzen, A. Lacabanne, D. Tubbenhauer and P. Vaz.
 Code and more for the paper Exponentially large mu-coefficients.
 2026. Accessed 26.Oct.2026.
 <https://github.com/dtubbenhauer/mu>.

<a id="bib-GoertzenWilliamson" name="bib-GoertzenWilliamson"></a>

**[GW26].** 
T. Goertzen and G. Williamson.
 Kazhdan–Lusztig Basis and Optimization.
 2026.
 <https://arxiv.org/abs/2604.18894>.

<a id="bib-GossowYacobi" name="bib-GossowYacobi"></a>

**[GY22].** 
F. Gossow and O. Yacobi.
 On the action of the long cycle on the Kazhdan–Lusztig basis.
 *Sém. Lothar. Combin.*, 86B:Art. 11, 12 pp., 2022.
 <https://arxiv.org/abs/2111.09510>.

<a id="bib-Green" name="bib-Green"></a>

**[Gre09].** 
R. M. Green.
 Leading coefficients of Kazhdan–Lusztig polynomials and fully commutative elements.
 *J. Algebraic Combin.*, 30(2):165–171, 2009.
 <https://arxiv.org/abs/0801.1650>, [doi:10.1007/s10801-008-0156-x](https://doi.org/10.1007/s10801-008-0156-x).

<a id="bib-Jones" name="bib-Jones"></a>

**[Jon09].** 
B. C. Jones.
 Leading coefficients of Kazhdan–Lusztig polynomials for Deodhar elements.
 *J. Algebraic Combin.*, 29(2):229–260, 2009.
 <https://arxiv.org/abs/0711.1391>, [doi:10.1007/s10801-008-0131-6](https://doi.org/10.1007/s10801-008-0131-6).

<a id="bib-KashiwaraTanisaki" name="bib-KashiwaraTanisaki"></a>

**[KT02].** 
M. Kashiwara and T. Tanisaki.
 Parabolic Kazhdan–Lusztig polynomials and Schubert varieties.
 *J. Algebra*, 249(2):306–325, 2002.
 <https://arxiv.org/abs/math/9908153>, [doi:10.1006/jabr.2000.8690](https://doi.org/10.1006/jabr.2000.8690).

<a id="bib-KL" name="bib-KL"></a>

**[KL79].** 
D. Kazhdan and G. Lusztig.
 Representations of Coxeter groups and Hecke algebras.
 *Invent. Math.*, 53(2):165–184, 1979.
 [doi:10.1007/BF01390031](https://doi.org/10.1007/BF01390031).

<a id="bib-KLPositivity" name="bib-KLPositivity"></a>

**[KL80].** 
D. Kazhdan and G. Lusztig.
 Schubert varieties and Poincaré duality.
 In *Geometry of the Laplace Operator*, Proceedings of Symposia in Pure Mathematics, vol. 36, pages 185–203. American Mathematical Society, 1980.
 [doi:10.1090/pspum/036/573434](https://doi.org/10.1090/pspum/036/573434).

<a id="bib-LinkDetection" name="bib-LinkDetection"></a>

**[K+25].** 
T. Kelomäki, A. Lacabanne, D. Tubbenhauer, P. Vaz and V. L. Zhang.
 On detection probabilities of link invariants.
 2025.
 <https://arxiv.org/abs/2509.05574>.

<a id="bib-KK" name="bib-KK"></a>

**[KK99].** 
M. Khovanov and G. Kuperberg.
 Web bases for $\mathfrak{sl}(3)$ are not dual canonical.
 *Pacific J. Math.*, 188(1):129–153, 1999.
 <https://arxiv.org/abs/q-alg/9712046>, [doi:10.2140/pjm.1999.188.129](https://doi.org/10.2140/pjm.1999.188.129).

<a id="bib-KoMazorchukMrden" name="bib-KoMazorchukMrden"></a>

**[KMM21].** 
H. Ko, V. Mazorchuk and R. Mrđen.
 Bigrassmannian permutations and Verma modules.
 *Selecta Math. (N.S.)*, 27(4):Paper No. 55, 2021.
 <https://arxiv.org/abs/2008.08864>, [doi:10.1007/s00029-021-00672-z](https://doi.org/10.1007/s00029-021-00672-z).

<a id="bib-Kuperberg" name="bib-Kuperberg"></a>

**[Kup96].** 
G. Kuperberg.
 Spiders for rank 2 Lie algebras.
 *Comm. Math. Phys.*, 180(1):109–151, 1996.
 <https://arxiv.org/abs/q-alg/9712003>, [doi:10.1007/BF02101184](https://doi.org/10.1007/BF02101184).

<a id="bib-LTVBigData" name="bib-LTVBigData"></a>

**[LTV26].** 
A. Lacabanne, D. Tubbenhauer and P. Vaz.
 Big data approach to Kazhdan–Lusztig polynomials.
 *J. Exp. Math.*, 2(1):21–62, 2026.
 <https://arxiv.org/abs/2412.01283>, [doi:10.56994/JXM.002.001.002](https://doi.org/10.56994/JXM.002.001.002).

<a id="bib-LM" name="bib-LM"></a>

**[LM21].** 
M. Lanini and P. J. McNamara.
 Singularities of Schubert varieties within a right cell.
 *SIGMA*, 17:070, 9 pp., 2021.
 <https://arxiv.org/abs/2003.08616>, [doi:10.3842/SIGMA.2021.070](https://doi.org/10.3842/SIGMA.2021.070).

<a id="bib-LS" name="bib-LS"></a>

**[LS81].** 
A. Lascoux and M.-P. Schützenberger.
 Polynômes de Kazhdan \& Lusztig pour les grassmanniennes.
 *Astérisque*, 87–88:249–266, 1981.

<a id="bib-LeclercToffin" name="bib-LeclercToffin"></a>

**[LT00].** 
B. Leclerc and P. Toffin.
 A simple algorithm for computing the 
global crystal basis of an irreducible $U_q(\mathfrak{sl}_n)$-module.
 *Int. J. Algebra Comput.*, 10(2):191–208, 2000.
 [doi:10.1142/S0218196700000042](https://doi.org/10.1142/S0218196700000042).

<a id="bib-Luebeck" name="bib-Luebeck"></a>

**[Lüb20].** 
F. Lübeck.
 Computation of Kazhdan–Lusztig polynomials and some
applications to finite groups.
 *Trans. Amer. Math. Soc.*, 373(4):2331–2347, 2020.
 <https://arxiv.org/abs/1610.07055>, [doi:10.1090/tran/8037](https://doi.org/10.1090/tran/8037).

<a id="bib-Lusztig" name="bib-Lusztig"></a>

**[Lus93].** 
G. Lusztig.
 *Introduction to Quantum Groups*.
 Progress in Mathematics, vol. 110.
 Birkhäuser, Boston, 1993.
 [doi:10.1007/978-0-8176-4717-9](https://doi.org/10.1007/978-0-8176-4717-9).

<a id="bib-MackaayDual" name="bib-MackaayDual"></a>

**[Mac14].** 
M. Mackaay.
 The $\mathfrak{sl}_N$-web algebras and dual canonical bases.
 *J. Algebra*, 409:54–100, 2014.
 <https://arxiv.org/abs/1308.0566>, [doi:10.1016/j.jalgebra.2014.02.036](https://doi.org/10.1016/j.jalgebra.2014.02.036).

<a id="bib-MPT" name="bib-MPT"></a>

**[MPT14].** 
M. Mackaay, W. Pan, and D. Tubbenhauer.
 The $\mathfrak{sl}_3$ web algebra.
 *Math. Z.*, 277(1–2):401–479, 2014.
 <https://arxiv.org/abs/1206.2118>, [doi:10.1007/s00209-013-1262-6](https://doi.org/10.1007/s00209-013-1262-6).

<a id="bib-MW" name="bib-MW"></a>

**[MW03].** 
T. J. McLarnan and G. S. Warrington.
 Counterexamples to the $0$–$1$ conjecture.
 *Represent. Theory*, 7:181–195, 2003.
 <https://arxiv.org/abs/math/0209221>, [doi:10.1090/S1088-4165-03-00178-X](https://doi.org/10.1090/S1088-4165-03-00178-X).

<a id="bib-Nguyen" name="bib-Nguyen"></a>

**[Ngu20].** 
V. M. Nguyen.
 Type $A$ admissible cells are Kazhdan–Lusztig.
 *Algebr. Comb.*, 3(1):55–105, 2020.
 <https://arxiv.org/abs/1807.07457>, [doi:10.5802/alco.91](https://doi.org/10.5802/alco.91).

<a id="bib-OpenAICIC" name="bib-OpenAICIC"></a>

**[OAI26].** 
OpenAI.
 Combinatorial invariance of Kazhdan–Lusztig polynomials.
 OpenAI Math Release preprint, 2026.

[https://github.com/openai/math](https://github.com/openai/math/blob/main/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf).

<a id="bib-ParkerStewart" name="bib-ParkerStewart"></a>

**[PS14].** 
A. E. Parker and D. I. Stewart.
 First cohomology groups for finite groups of Lie type in
defining characteristic.
 *Bull. Lond. Math. Soc.*, 46(2):227–238, 2014.
 <https://arxiv.org/abs/1211.6942>, [doi:10.1112/blms/bdt087](https://doi.org/10.1112/blms/bdt087).

<a id="bib-ParshallScott" name="bib-ParshallScott"></a>

**[PS11].** 
B. J. Parshall and L. L. Scott.
 Bounding Ext for modules for algebraic groups, finite groups
and quantum groups.
 *Adv. Math.*, 226(3):2065–2088, 2011.
 <https://arxiv.org/abs/0909.5207>, [doi:10.1016/j.aim.2010.09.021](https://doi.org/10.1016/j.aim.2010.09.021).

<a id="bib-PPR" name="bib-PPR"></a>

**[PPR09].** 
T. K. Petersen, P. Pylyavskyy and B. Rhoades.
 Promotion and cyclic sieving via webs.
 *J. Algebraic Combin.*, 30(1):19–41, 2009.
 <https://arxiv.org/abs/0804.3375>, [doi:10.1007/s10801-008-0150-3](https://doi.org/10.1007/s10801-008-0150-3).

<a id="bib-Polo99" name="bib-Polo99"></a>

**[Pol99].** 
P. Polo.
 Construction of arbitrary Kazhdan–Lusztig polynomials in symmetric groups.
 *Represent. Theory*, 3:90–104, 1999.
 [doi:10.1090/S1088-4165-99-00074-6](https://doi.org/10.1090/S1088-4165-99-00074-6).

<a id="bib-Rhoades" name="bib-Rhoades"></a>

**[Rho10].** 
B. Rhoades.
 Cyclic sieving, promotion, and representation theory.
 *J. Combin. Theory Ser. A*, 117(1):38–76, 2010.
 <https://arxiv.org/abs/1005.2568>, [doi:10.1016/j.jcta.2009.03.017](https://doi.org/10.1016/j.jcta.2009.03.017).

<a id="bib-RingelGrassmannians" name="bib-RingelGrassmannians"></a>

**[Rin18].** 
C. M. Ringel.
 Quiver Grassmannians for wild acyclic quivers.
 *Proc. Amer. Math. Soc.*, 146(5):1873–1877, 2018.
 <https://arxiv.org/abs/1703.08782>, [doi:10.1090/proc/13882](https://doi.org/10.1090/proc/13882).

<a id="bib-RobertCharacterization" name="bib-RobertCharacterization"></a>

**[Rob15].** 
L.-H. Robert.
 A characterization of indecomposable web modules over Khovanov–Kuperberg algebras.
 *Algebr. Geom. Topol.*, 15(3):1303–1362, 2015.
 <https://arxiv.org/abs/1309.2793>, [doi:10.2140/agt.2015.15.1303](https://doi.org/10.2140/agt.2015.15.1303).

<a id="bib-RobertFamily" name="bib-RobertFamily"></a>

**[Rob13].** 
L.-H. Robert.
 A large family of indecomposable projective modules for the Khovanov–Kuperberg algebras of $\mathfrak{sl}_3$-webs.
 *J. Knot Theory Ramifications*, 22(11):1350062, 2013.
 <https://arxiv.org/abs/1207.6287>, [doi:10.1142/S0218216513500624](https://doi.org/10.1142/S0218216513500624).

<a id="bib-SX" name="bib-SX"></a>

**[SX10].** 
L. Scott and N. Xi.
 Some non-trivial Kazhdan–Lusztig coefficients of an affine Weyl group of type $\widetilde A_n$.
 *Sci. China Math.*, 53(8):1919–1930, 2010.
 <https://arxiv.org/abs/0909.3394>, [doi:10.1007/s11425-010-4041-4](https://doi.org/10.1007/s11425-010-4041-4).

<a id="bib-TubbenhauerGln" name="bib-TubbenhauerGln"></a>

**[Tub20].** 
D. Tubbenhauer.
 $\mathfrak{gl}_n$-webs, categorification and Khovanov–Rozansky homologies.
 *J. Knot Theory Ramifications*, 29(11):2050074, 96 pp., 2020.
 <https://arxiv.org/abs/1404.5752>, [doi:10.1142/S0218216520500741](https://doi.org/10.1142/S0218216520500741).

<a id="bib-TubbenhauerCrystal" name="bib-TubbenhauerCrystal"></a>

**[Tub14].** 
D. Tubbenhauer.
 $\mathfrak{sl}_3$-Web bases, intermediate crystal bases and categorification.
 *J. Algebraic Combin.*, 40(4):1001–1076, 2014.
 <https://arxiv.org/abs/1310.2779>, [doi:10.1007/s10801-014-0518-5](https://doi.org/10.1007/s10801-014-0518-5).

<a id="bib-Tymoczko" name="bib-Tymoczko"></a>

**[Tym12].** 
J. Tymoczko.
 A simple bijection between standard $3\times n$ tableaux and irreducible webs for $\mathfrak{sl}_3$.
 *J. Algebraic Combin.*, 35(4):611–632, 2012.
 <https://arxiv.org/abs/1005.4724>, [doi:10.1007/s10801-011-0317-1](https://doi.org/10.1007/s10801-011-0317-1).

<a id="bib-Warrington" name="bib-Warrington"></a>

**[War11].** 
G. S. Warrington.
 Equivalence classes for the $\mu$-coefficient of Kazhdan–Lusztig polynomials in $S_n$.
 *Exp. Math.*, 20(4):457–466, 2011.
 <https://arxiv.org/abs/1010.3961>, [doi:10.1080/10586458.2011.565260](https://doi.org/10.1080/10586458.2011.565260).

<a id="bib-Xi" name="bib-Xi"></a>

**[Xi05].** 
N. Xi.
 The leading coefficient of certain Kazhdan–Lusztig polynomials of the permutation group $S_n$.
 *J. Algebra*, 285(1):136–145, 2005.
 <https://arxiv.org/abs/math/0401430>, [doi:10.1016/j.jalgebra.2004.08.039](https://doi.org/10.1016/j.jalgebra.2004.08.039).

## Author information

**Tom Goertzen.** T.G.: The University of Sydney,
School of Mathematics and Statistics F07,
NSW 2006, Australia,
[profiles.sydney.edu.au/tom.goertzen](https://profiles.sydney.edu.au/tom.goertzen),
[ORCID 0009-0003-3399-3416](https://orcid.org/0009-0003-3399-3416). tom.goertzen@sydney.edu.au

**Abel Lacabanne.** A.L.: Laboratoire de Mathématiques Blaise Pascal (UMR 6620),
Université Clermont Auvergne,
Campus Universitaire des Cézeaux, 3 place Vasarely,
63178 Aubière Cedex, France,
[www.normalesup.org/~lacabanne](https://www.normalesup.org/~lacabanne/),
[ORCID 0000-0001-8691-3270](https://orcid.org/0000-0001-8691-3270). abel.lacabanne@uca.fr

**Daniel Tubbenhauer.** D.T.: The University of Sydney,
School of Mathematics and Statistics F07,
Office Carslaw 827, NSW 2006, Australia,
[www.dtubbenhauer.com](http://www.dtubbenhauer.com),
[ORCID 0000-0001-7265-5047](https://orcid.org/0000-0001-7265-5047). daniel.tubbenhauer@sydney.edu.au

**Pedro Vaz.** P.V.: Institut de Recherche en Mathématique et Physique,
Université catholique de Louvain,
Chemin du Cyclotron 2, 1348 Louvain-la-Neuve, Belgium,
[perso.uclouvain.be/pedro.vaz](https://perso.uclouvain.be/pedro.vaz/),
[ORCID 0000-0001-9422-4707](https://orcid.org/0000-0001-9422-4707). pedro.vaz@uclouvain.be
