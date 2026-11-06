<a id="loc:covectorappendix" name="loc:covectorappendix"></a>

# Appendix A. Details for Lemma 8A.2

[Section index](README.md) · [Complete paper](../paper.md) · [AI reading guide](../../AI_README.md)

Fix the nine outputs of each prefix $P_i$ or $P_j'$ to
$\omega=(ABC)^3$, and work downward through its growth string.
The tables give the resulting covector and the small map attached
to that prefix. Thus
$\langle\omega|D_i=(\langle\omega|P_i)h_i$, and similarly for $\mathcal H_j$.
Here a word $s$ denotes $\langle s|$.

The first table lists $D_1,\ldots,D_7$, whose sum is $D_0$.
The term $D_8=\tau^3\eta$ is treated separately in
[Equation 7C.5](07.md#loc:lowerformula). The second table supplies the terms of
$\mathcal H$. All covectors follow from the elementary tables in
[Section 3](03.md#sec:webs).

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
[Equation 7A.2](07.md#loc:Srow), the first covector in the table.
Composing the listed covectors on the right with their small maps
and summing gives the $D_0$ and $\mathcal H$ rows used in
[Lemma 8A.2](08.md#loc:tworows).
