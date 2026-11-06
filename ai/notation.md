# Notation and conventions

## Permutations, cells and words

| Symbol | Meaning in this paper |
| --- | --- |
| $S_n$, $s_i$, $\ell(w)$ | Permutations on $n$ letters, the adjacent transposition $(i,i+1)$, and inversion length. Multiplication is $(xy)(i)=x(y(i))$. The order on permutations is Bruhat order. |
| $P_{x,y}(q)$, $\mu(x,y)$ | Ordinary Kazhdan–Lusztig polynomial and its coefficient at the highest **allowed** degree $(\ell(y)-\ell(x)-1)/2$ for $x<y$ and odd length gap. Set $\mu=0$ otherwise. |
| $P(w),Q(w)$ | Insertion and recording tableaux for ordinary RSK row insertion. Fixing $Q(w)$ fixes a left cell. For the dominant words here, $P(\pi(w))$ is the tableau of $w$, and $Q(\pi(w))$ is the same row-superstandard rectangle of that shape. |
| $A,B,C$; $\mathcal D_N$ | Letters record rows one, two, three (English tableaux). $\mathcal D_N$ consists of words with $N$ copies of each letter and $\#A\ge\#B\ge\#C$ in every prefix. |
| $\pi(w)$ | List, in increasing order, the positions of the $C$'s, then of the $B$'s, then of the $A$'s. The resulting list is the permutation in one-line notation. |
| $m,r,N_m$ | $m\ge0$ counts nine-letter blocks; the exponential family takes $m=2r$. The common row width is $N_m=4+3m$ and the ambient group is $S_{3N_m}$. |
| $\mathtt S,\mathtt M,\mathtt E$ | Prefix $ABAAAC$, middle block $BBBAACACC$, tail $BBCBCC$. |
| $a_m,c_m$; $x_m,y_m$ | $a_m=(ABC)^{N_m}$ and $c_m=\mathtt S\mathtt M^m\mathtt E$; $x_m=\pi(a_m)$, $y_m=\pi(c_m)$. In the main theorem $S_r,T_r$ denote the tableaux of $a_{2r},c_{2r}$. |
| $\delta_m$ | With $m$ counting blocks, $\ell(y_m)-\ell(x_m)=17m+11$. In the theorem's index $r$, the same gap is $34r+11$. |
| $W_J$, $P^{J,+}_{x,y}(q)$ | $W_J=S_N^3$ with $N=N_m$, omitting the simple generators numbered $N,2N$. The parabolic polynomial uses the alternating sum over $h\in W_J$ with $xh\le y$. |

[KL conventions](paper.md#sec:preliminaries) · [Tableau convention](paper.md#lem:rectangular-cell) · [Words](paper.md#eq:words) · [Length gap](paper.md#lem:lengths) · [Parabolic formula](paper.md#eq:parabolic)

## Web and tensor coordinates

| Symbol | Meaning in this paper |
| --- | --- |
| $v$, $q$, $\mathbb K$, $R$ | $v$ is the web parameter, $\mathbb K=\mathbb Q(v)$ and $R=\mathbb Z[v]$. In the FKK formula evaluate the KL polynomial variable $q$ at $v^{-2}$ and multiply by $v^{\delta_m}$. The tensor degree used in local estimates is $\deg_{v^{-1}}(v^k)=-k$. |
| $V^+$, $V^-$, $V$, $\mathbf1$ | Fundamental three-dimensional $U_{v^{-1}}(\mathfrak{sl}_3)$ module, its dual, $V=V^+$, and the one-dimensional trivial module. A boundary sign chooses a module; a state letter chooses a basis vector in that module. |
| $e_s$, $[e_s]f$, $[v]f$ | $e_s$ is the standard tensor for a word $s$ in $A,B,C$. Extract its coordinate from $f$ with $[e_s]$. For a Laurent polynomial, $[v]$ takes the coefficient of $v^1$. For even $m$, $\mu(x_m,y_m)=[v][e_{a_m}]b_{c_m}$. |
| $W_w$, $b_w$ | For a dominant word $w$, the non-elliptic web and the dual canonical invariant tensor with that label. The latter is fixed by the tensor bar and agrees with $e_w$ modulo $v$ times the standard $R$-lattice. |
| $\Phi_S$ | Lusztig's tensor bar on the tensor product with sign word $S$. It sends $v$ to $v^{-1}$ and uses the quasi-$R$-matrix on a tensor product. Individual web maps intertwine it. |
| $\prec$ | Triangular order on state strings: lexicographic with $C\prec B\prec A$. In the elementary tensor tables, comparisons $a<b$ use $A<B<C$. |
| $\mathcal M,\mathcal N,\mathcal K$ | Columns of $\mathcal M$ are web vectors in standard tensor coordinates. Columns of $\mathcal N$ are dual canonical vectors in standard coordinates. Columns of $\mathcal K$ are dual canonical vectors in the web basis. Thus $\mathcal N=\mathcal M\mathcal K$ and entries of $\mathcal K$ are fixed under $v\leftrightarrow v^{-1}$. |
| $d,e$ | Web digon and circle factors $d=v+v^{-1}$ and $e=v^2+1+v^{-2}=d^2-1$. |
| $y,\lambda,\nu,\sigma',\sigma$ | Split, merge, unordered-pair label in the merge rule, cup and cap. For distinct letters $\lambda(ab)=v^{-[a<b]}\nu(a,b)$ with $\nu(AB)=A,\nu(AC)=B,\nu(BC)=C$; $\lambda(aa)=0$. |
| $H,\tau,\eta$ | Two-vertex map $H=(I\otimes\lambda)(y\otimes I)$, tripod $\tau=(I\otimes y)\sigma'$, and evaluation $\eta=\sigma(\lambda\otimes I)$. $\tau^j$ denotes $j$ juxtaposed tripods. |

[Local tensor maps](paper.md#eq:localmaps) · [Canonical condition](paper.md#thm:canonical) · [Coordinates and basis change](paper.md#sec:basischange) · [FKK dictionary](paper.md#eq:FKK)

## Corrected block and coefficient extraction

| Symbol | Meaning in this paper |
| --- | --- |
| $\Psi_{\mathtt S},\Psi_{\mathtt M},\Psi_{\mathtt E}$ | Raw prefix, repeated block, and tail maps. The raw indexing web is $\Psi_{\mathtt S}\Psi_{\mathtt M}^m\Psi_{\mathtt E}$ with the identity understood on earlier external outputs. |
| $Y_i,H_i,a_i$ in a growth string | Merge equal signs, apply $H$ at opposite signs, remove an adjacent opposite-sign pair. The downward string uses zero-based positions. Its reverse specifies the upward map. |
| $\lambda_1,\lambda_2,E_1,E_2$ | Subscripts here are one-based. $\lambda_1,\lambda_2$ merge the first or last pair of three strands. $E_i$ applies $y\lambda$ to the indicated pair. |
| $\mathsf R_i,\mathsf L_i,\mathsf S$; $R_i$ | $\mathsf R_i=H_{i+1}Y_i$, $\mathsf L_i=H_iY_{i+1}$ and $\mathsf S=H_2H_1Y_0$ abbreviate local operations. Plain $R_i$ in Appendix B numbers a diagram in the square reduction. |
| $\Psi_+,\Psi_-$; $D_i,\mathcal H_j$ | $\Psi_+$ creates three connecting strands; $\Psi_-=\sum_{i=1}^8D_i$ removes them. The eleven remaining square-resolution terms sum to $\mathcal H=\sum_{j=1}^{11}\mathcal H_j$, with $\eta\Psi_{\mathtt M}=d\Psi_-+\mathcal H$. |
| $\mathcal E,e_*$ | $\mathcal E=V^{\otimes3}\oplus\mathbf1$ has 27 three-letter states and a scalar state $e_*$. The scalar means that there are zero connecting strands. |
| $\mathsf p,T,\boldsymbol\rho$; $\beta_m$ | The corrected prefix, block and tail. The tensor $\beta_m=\mathsf pT^m\boldsymbol\rho$ has $12+9m$ positive outputs. Local bounds and the tensor bar give $\beta_m=b_{c_m}$. |
| $G$, $\widehat p,\widehat T,\widehat\rho$; $M[0]$ | A change of interface coordinates makes the three maps integral over $R$. Adjacent $G^{-1}G$ cancel in the composite. $M[0]$ takes the entrywise constant term of a matrix over $R$. |
| $p_a,\mathsf A,\rho_a$ | Fix the six external states at either end to $ABCABC$ and the nine at each block to $(ABC)^3$. The selected coordinate is $p_a\mathsf A^m\rho_a$; $\mathsf A$ has 28 rows and columns. |
| $K$ | On rows $ABC,*$, the constant matrix $\mathsf A[0]$ vanishes outside columns $ABC,*$. In that order its two-by-two part is $\left(\begin{smallmatrix}0&1\\2&0\end{smallmatrix}\right)$. Since $K^2=2I$, the requested coefficient doubles every two blocks. $\mathcal K$ above is a different, much larger change-of-basis matrix. |

[Raw pieces](paper.md#eq:growth) · [Corrected maps](paper.md#eq:maps) · [Integral coordinates](paper.md#loc:gauge) · [Two constant rows](paper.md#loc:tworows)

[AI reading guide](../AI_README.md) · [Diagram descriptions](diagrams.md)
