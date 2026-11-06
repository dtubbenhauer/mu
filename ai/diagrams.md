# Reading the diagrams

Figure numbers follow the [manuscript source](source.tex). The links open the corresponding figures in the [paper](paper.md). For a calculation, keep the boundary positions fixed. Even two isomorphic tripod components can give different tensor coordinates when attached to different boundary points.

## Conventions and inline pictures

- **Permutation diagrams (§1B).** The strand from bottom position $i$ ends at top position $w(i)$. For the tableau with rows $(1,2),(3,5),(4,6)$, reading rows from bottom to top gives $w=(4,6,3,5,1,2)$. The row word is $AABCBC$. [Tableau-to-permutation convention](paper.md#def:words)
- **Planar webs (§3A).** A hollow internal vertex is a source and a filled one is a sink. Orient edges from source to sink. At a positive output the edge points into the diagram, and at a positive input it points out. Reverse the boundary directions for a negative sign. In rectangles, inputs are below and outputs above. Stack to compose, and place side by side to take a tensor product. [Web definition](paper.md#def:web)
- **From a tableau to a web (§3B).** For each entry of row two, in increasing order, draw an arc to the nearest unused smaller entry of row one. Repeat between rows three and two. Put a trivalent vertex at each row-two junction. Replace each arc crossing with two trivalent vertices joined by an edge, choosing the resolution that preserves bipartiteness. For $AABCBC$ the two tripods meet boundary triples $(2,3,4)$ and $(1,5,6)$. For $ABACBC$ the arcs $(2,4)$ and $(3,5)$ cross; the resolved web is one tree with boundary pairs $(1,2),(3,4),(5,6)$. [Worked drawings](paper.md#ex:tableau-to-web)
- **Reading a growth string (§6A).** Read the displayed string left to right to reduce the output boundary, numbering strands from zero again after each move. For the upward map, read in reverse and undo the moves using splits and cups. Products of linear maps are composed right to left. [Growth strings](paper.md#eq:growth)
- **Finite and affine proof comparison (§1D).** The left column repeats a planar block at fixed web rank, corrects it on a 28-dimensional interface, and reads the tensor coordinate on two states. The right column keeps one annular graph, varies the thicknesses and rank, and counts flags. The two conclusions are respectively a single coefficient $2^r$ and a sum $m(m+1)/2$. [Finite readout](paper.md#loc:coefficient)

## Figures 1–20

| Figure | What to read from the picture | Image |
| --- | --- | --- |
| <a id="figure-1" name="figure-1"></a>[1. Permutations](paper.md#fig:permutation-pair) | The two strand diagrams encode $x_2,y_2$ in $S_{30}$, the first member with $\mu=2$. Colors separate the tableau rows. Each endpoint pair specifies one entry in one-line notation. | [View](figures/figure-01.png) |
| <a id="figure-2" name="figure-2"></a>[2. Repeating patch](paper.md#fig:intro-hexagons) | Three patches each contain a shaded hexagon surrounded by six hexagons. Three strands indicate a join between neighbors. Figure 10 gives the exact boundary and attachments. | [View](figures/figure-02.png) |
| <a id="figure-3" name="figure-3"></a>[3. Planar relations](paper.md#fig:relations) | Erase a circle with factor $e=v^2+1+v^{-2}$. Replace a digon by one edge with factor $d=v+v^{-1}$. A square is the sum of its two planar smoothings, both with coefficient one. Apply each replacement inside the indicated disk. | [View](figures/figure-03.png) |
| <a id="figure-4" name="figure-4"></a>[4. Generators](paper.md#fig:generators) | The split $y$, merge $\lambda$, cup $\sigma'$, and cap $\sigma$ appear alongside the two-vertex map $H$, the tripod $\tau$, and its evaluation $\eta$. Boundary signs specify modules. The [local formulas](paper.md#eq:localmaps) give all tensor entries. | [View](figures/figure-04.png) |
| <a id="figure-5" name="figure-5"></a>[5. Six-point webs](paper.md#fig:six) | Read boundary points clockwise from the left. The five diagrams correspond, in order, to $AABBCC$, $AABCBC$, $ABABCC$, $ABACBC$, $ABCABC$. They index the columns of the [tensor-coordinate matrix](paper.md#eq:sixcoordinates). | [View](figures/figure-05.png) |
| <a id="figure-6" name="figure-6"></a>[6. Zero and one block](paper.md#fig:family01) | Each pair shows the web for $a_m$ and that for $c_m$, with their tableaux below. The source is a product of consecutive tripods. The pairs have 12 and 21 positive boundary points and give $\mu=1$ and $0$. | [View](figures/figure-06.png) |
| <a id="figure-7" name="figure-7"></a>[7. Two and four blocks](paper.md#fig:family24) | The target strip lengthens; the tableau widths increase to 10 and 16. The corrected vectors give $\mu=2$ and $4$. The diagrams themselves depict the indexing webs $W_{a_m},W_{c_m}$. | [View](figures/figure-07.png) |
| <a id="figure-8" name="figure-8"></a>[8. One-block correction](paper.md#fig:oneblockchange) | The raw 21-point web and three lower webs give $b_{c_1}=W_{c_1}-W_{z_1}-W_{z_2}-W_{z_3}$. The last lower web consists entirely of seven tripods. | [View](figures/figure-08.png) |
| <a id="figure-9" name="figure-9"></a>[9. Two-block correction](paper.md#fig:twoblocklower) | At the 30-point boundary the left column gives the three lower webs with multiplier $-(v+v^{-1})$. The right column gives three of the 91 with multiplier $-1$. Together the 94 corrections change the selected coefficient of $v$ from 18 to 2. | [View](figures/figure-09.png) |
| <a id="figure-10" name="figure-10"></a>[10. Raw pieces](paper.md#fig:pieces) | Start, middle, and end pieces are drawn with local labels. Join the three inputs of a start or middle piece to outputs 1, 2, 3 of the piece on its right, in that order. | [View](figures/figure-10.png) |
| <a id="figure-11" name="figure-11"></a>[11. Creating three strands](paper.md#fig:correction) | The correction $\Psi_+=W_{ABACBC}\otimes\tau^2$ has twelve outputs. Squares distinguish the first three, kept for the next attachment. | [View](figures/figure-11.png) |
| <a id="figure-12" name="figure-12"></a>[12. Assembly](paper.md#fig:assembly) | Beginning at the end piece, attach two middle pieces, then the start. The thick edges mark ordinary strands at the joins. The final web has successive external groups of sizes $6,9,9,6$. | [View](figures/figure-12.png) |
| <a id="figure-13" name="figure-13"></a>[13. Corrected block](paper.md#fig:interface) | A cut has three strands or zero strands. From three to three use $\Psi_{\mathtt M}$, from three to zero use $\Psi_-$, from zero to three use $-\Psi_+$, and from zero to zero use $-d\tau^3$. Each transition adds nine external outputs. | [View](figures/figure-13.png) |
| <a id="figure-14" name="figure-14"></a>[14. Two digons](paper.md#loc:fun) | Cap the first three outputs of the six-point core in $\Psi_+$. Removing two successive digons gives $d^2$ times one tripod. Restoring the other two tripods yields $\eta\Psi_+=d^2\tau^3$. | [View](figures/figure-14.png) |
| <a id="figure-15" name="figure-15"></a>[15. First square](paper.md#loc:firstsquare) | Cap the first three outputs of $\Psi_{\mathtt M}$. Resolving the marked square gives $R_1+R_{22}$; the second branch has a digon. Appendix B follows both branches with the same numbered boundary. | [View](figures/figure-15.png) |
| <a id="figure-16" name="figure-16"></a>[16. Terminal square](paper.md#fig:moresquares) | Cap the first three outputs of the end piece. One square smoothing leads, via a digon, to two tripods. The other gives the six-point tree. Thus $\eta\Psi_{\mathtt E}=d\tau^2+W_{AABBCC}$. | [View](figures/figure-16.png) |
| <a id="figure-17" name="figure-17"></a>[17. A second three-row family](paper.md#fig:mu19-candidate) | The two web pairs have widths 9 and 12. The computed coefficients after correction are 19 and 2446. The proposed growth of this family is separate from the proved doubling family. | [View](figures/figure-17.png) |
| <a id="figure-18" name="figure-18"></a>[18. Candidate linear family](paper.md#fig:linear-mu) | Four dot plots encode the first two permutation pairs, each point at $(i,w(i))$. Left to right they are $x,y$ in $S_{12}$, then $x,y$ in $S_{15}$. The predicted coefficients are 4 and 5. Remark 9A.1 records that the authors have yet to check the geometric argument. | [View](figures/figure-18.png) |
| <a id="figure-19" name="figure-19"></a>[19. Completing the seed](paper.md#fig:cores1) | Four bold entries extend both tableaux from $(9,7,7)$ to $(9,9,9)$. Add $24,26$ in row two and $25,27$ in row three. The webs correspond to these completed tableaux $S^+,T^+$. | [View](figures/figure-19.png) |
| <a id="figure-20" name="figure-20"></a>[20. Seed and theorem family](paper.md#fig:cores2) | Left is the rotated seed with target word $R_{\rm seed}\mathtt M\mathtt E$. Right is the theorem's two-block target $\mathtt S\mathtt M^2\mathtt E$. Compare the start pieces. Both source webs consist of consecutive tripods. | [View](figures/figure-20.png) |

## Appendix B. Figures 21–41

The pictures prove $\eta\Psi_{\mathtt M}=d\Psi_-+\mathcal H$. Vertex labels $1,\ldots,9$ are outputs, and $12,11,10$ are inputs in their linear order. Each row below names the replacement of the highlighted face; all other edges and their cyclic orders are fixed. [Reduction atlas](paper.md#loc:atlasappendix)

| Figure | Local equality | Figure | Local equality |
| --- | --- | --- | --- |
| <a id="figure-21" name="figure-21"></a>[21](paper.md#fig:atlas-r0) | $R_{0}=R_{1}+R_{22}$ | <a id="figure-31" name="figure-31"></a>[31](paper.md#fig:atlas-r18) | $R_{18}=R_{19}+R_{20}$ |
| <a id="figure-22" name="figure-22"></a>[22](paper.md#fig:atlas-r1) | $R_{1}=R_{2}+R_{11}$ | <a id="figure-32" name="figure-32"></a>[32](paper.md#fig:atlas-r22) | $R_{22}=dR_{23}$ |
| <a id="figure-23" name="figure-23"></a>[23](paper.md#fig:atlas-r2) | $R_{2}=R_{3}+R_{10}$ | <a id="figure-33" name="figure-33"></a>[33](paper.md#fig:atlas-r23) | $R_{23}=R_{24}+R_{31}$ |
| <a id="figure-24" name="figure-24"></a>[24](paper.md#fig:atlas-r3) | $R_{3}=R_{4}+R_{7}$ | <a id="figure-34" name="figure-34"></a>[34](paper.md#fig:atlas-r24) | $R_{24}=R_{25}+R_{30}$ |
| <a id="figure-25" name="figure-25"></a>[25](paper.md#fig:atlas-r4) | $R_{4}=R_{5}+R_{6}$ | <a id="figure-35" name="figure-35"></a>[35](paper.md#fig:atlas-r25) | $R_{25}=R_{26}+R_{29}$ |
| <a id="figure-26" name="figure-26"></a>[26](paper.md#fig:atlas-r7) | $R_{7}=R_{8}+R_{9}$ | <a id="figure-36" name="figure-36"></a>[36](paper.md#fig:atlas-r26) | $R_{26}=R_{27}+R_{28}$ |
| <a id="figure-27" name="figure-27"></a>[27](paper.md#fig:atlas-r11) | $R_{11}=R_{12}+R_{17}$ | <a id="figure-37" name="figure-37"></a>[37](paper.md#fig:atlas-r31) | $R_{31}=R_{32}+R_{35}$ |
| <a id="figure-28" name="figure-28"></a>[28](paper.md#fig:atlas-r12) | $R_{12}=R_{13}+R_{16}$ | <a id="figure-38" name="figure-38"></a>[38](paper.md#fig:atlas-r32) | $R_{32}=R_{33}+R_{34}$ |
| <a id="figure-29" name="figure-29"></a>[29](paper.md#fig:atlas-r13) | $R_{13}=R_{14}+R_{15}$ | <a id="figure-39" name="figure-39"></a>[39](paper.md#fig:atlas-r35) | $R_{35}=R_{36}+R_{37}$ |
| <a id="figure-30" name="figure-30"></a>[30](paper.md#fig:atlas-r17) | $R_{17}=R_{18}+R_{21}$ |  |  |

Figure 32 is the sole digon removal. Its factor $d$ multiplies all eight terminal $D_i$ in that subtree. The other eleven terminal maps each have coefficient one.

| Figure | Terminal diagrams in the order drawn |
| --- | --- |
| <a id="figure-40" name="figure-40"></a>[40. The eight $D_i$](paper.md#fig:atlas-term1) | $D_1,\ldots,D_8$ are $R_{37},R_{36},R_{33},R_{30},R_{34},R_{29},R_{28},R_{27}$. Each picture includes both pieces in $D_i=P_i h_i$. |
| <a id="figure-41" name="figure-41"></a>[41. The eleven $\mathcal H_j$](paper.md#fig:atlas-term5) | $\mathcal H_1,\ldots,\mathcal H_{11}$ are $R_9,R_8,R_5,R_{10},R_6,R_{21},R_{19},R_{20},R_{15},R_{16},R_{14}$. |

[AI reading guide](../AI_README.md) · [Notation](notation.md)
