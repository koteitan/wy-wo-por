[← Back](README.md) | [English](10-official-descent.md) | [Japanese](../10-official-descent.md)

# Descent of the official expansion

Prerequisites

| Note | Words used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinals, the coefficient of degree $`k`$ $`c_k(\alpha)`$, degree, the sum $`\alpha + \omega^e`$, regularity of $`\omega_1`$ |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded, keys and their order, $`\top`$, termination by bounds on labels |
| [05 The official ω-Y sequence and its mountain](05-omegay-mountain.md) | expressions, columns, rows, jumps, $`B(\alpha, \beta)`$, the mountain, nodes, values, the parent $`\pi(u)`$, $`u^+`$, edges, the jump of an edge, parent search, the parent within the row, the degree bound $`D`$, regions, the regions $`L_{k,j}`$ of the lower part, $`S[j]`$, $`h_S`$, $`\mathrm{top}_S`$, $`t`$, $`\tau`$, the root $`r`$, $`c_r`$, $`w`$, $`x_0`$, $`\mu_i`$, blocks, pairs $`(\alpha', \ell)`$, items, ascends, the reference row, copies of the root row, gap copies, the upper part, $`s[n]`$, $`\prec`$, the final theorem |
| [06 The combinatorial layer and leg atoms](06-combinatorial-layer.md) | templates, the key evaluated at column numbers, the scale root $`\rho_k`$, edge keys, representations, atom systems, the border column, reservoirs $`F, T`$, the control $`K_c`$, classification (base, reservoir, seam), the descent theorem (Theorem 6), the leg $`\ell(u)`$, the leg end $`p_u`$, virtual keys, the leg atom $`\mathrm{at}(u)`$, $`E_D(M)`$, the classification lemma |
| [09 Proof of the three theorems](09-obligations.md) | the three theorems of [06](06-combinatorial-layer.md) §5 hold |

This note explains the proof of the classification lemma of [06](06-combinatorial-layer.md) §11 and derives the final theorem of [05](05-omegay-mountain.md) §8. The proof is large. Here we write the statements, the route of the proof and its main points. We do not write the detailed case analysis.

We use the symbols of [05](05-omegay-mountain.md) and [06](06-combinatorial-layer.md). Let $`s`$ be a nonempty expression and $`n \ge 1`$ with $`s_{x_0} \gt 1`$, and assume that $`s[n]`$ is defined. Let $`D`$ be a degree bound of $`M(s)`$. A column $`X \ge x_0`$ is called a **new column**. The key (template) of a leg atom $`\mathrm{at}(u)`$ is written $`\kappa(\mathrm{at}(u))`$. Templates are compared by their keys evaluated at column numbers ([06](06-combinatorial-layer.md) §1). A column map $`\mu_j`$ is applied to a template by applying it to the column number of each coordinate and leaving $`\top`$ as it is.

## 1. Origins

The rule of [05](05-omegay-mountain.md) §5 makes each node of a new column from one pair $`(\alpha', \ell)`$. The node of $`M(s)`$ that the rule read when it emitted that pair is called the **source node** of the new node. By the way the pair is emitted, the **origin** is of 4 kinds.

| Origin | What emitted the pair | Source node |
|---|---|---|
| plain copy | an item of level 1 with $`C = \bot`$ | the node $`(x, \alpha)`$ ($`S = \{\alpha\}`$) |
| copy of the root row | an item of level 1 with $`C \ne \bot`$, $`\varepsilon = 0`$ | the node $`(x, C)`$ |
| gap copy | an item of level 1 with $`C \ne \bot`$, $`\varepsilon = 1`$ | the node $`(x, C)`$ |
| copy of the upper part | the upper part ([05](05-omegay-mountain.md) §5.5) | a node of column $`x'`$ (row $`\ge \tau`$) |

If the source node is not a bottom node, the $`\ell`$ of the pair is the leg of the source node. For copies of the root row and gap copies with $`C = 0`$, $`\ell = x - 1`$, which is again the leg $`x - 1`$ of the source node $`(x, 0)`$. For a plain copy with $`\alpha = 0`$, $`\ell`$ is none and the node put is a bottom node.

**Example ($`(1,3,3)[2]`$, computed with Python).** The origins of the nodes of the output columns 2 to 5 of [05](05-omegay-mountain.md) §6.1 are as follows. Nodes are written as (column, row).

| Column | row 0 | row 1 | row 2 | row 3 | row $`\omega`$ |
|---|---|---|---|---|---|
| 2 | copy of the root row (source $`(2,0)`$) | plain copy (source $`(2,1)`$) | | | |
| 3 | copy of the root row (source $`(1,0)`$) | gap copy (source $`(1,0)`$) | plain copy (source $`(1,1)`$) | | copy of the upper part (source $`(1,\omega)`$) |
| 4 | copy of the root row (source $`(2,0)`$) | gap copy (source $`(2,0)`$) | plain copy (source $`(2,1)`$) | | |
| 5 | copy of the root row (source $`(1,0)`$) | gap copy (source $`(1,0)`$) | gap copy (source $`(1,0)`$) | plain copy (source $`(1,1)`$) | copy of the upper part (source $`(1,\omega)`$) |

## 2. Splitting the classification lemma into six statements

We split the classification lemma of [06](06-combinatorial-layer.md) §11 into the following six statements.

- (i) **Output length.** $`s[n]`$ has length $`x_0 + n \cdot w`$.
- (ii) **Output mountain.** $`M(s[n])`$ can be built.
- (iii) **Preservation of degree.** $`D`$ is a degree bound of $`M(s[n])`$.
- (iv) **Reconstruction.** The mountain built by the rule (the rows and parents of the nodes of each column) equals the mountain $`M(s[n])`$ of the output values.
- (v) **Key bound.** The leg atom of a new node is bounded above by the mapped leg atom of its source node (stated precisely below).
- (vi) **The control is the strongest.** For a node $`v`$ of column $`x_0`$ of $`M(s)`$ below $`t`$, $`\kappa(\mathrm{at}(v)) \lt K_c`$.

If $`s_{x_0} = 1`$ or $`n = 0`$, $`s[n]`$ is $`s`$ with its last entry deleted, and its mountain is the part of $`M(s)`$ made of the first columns. The leg atoms are the same, so all of them are classified by (base). If the rule fails ([05](05-omegay-mountain.md) §5.6), $`s[n]`$ is not defined and there is nothing to show.

**The precise form of (v).** Take a node $`u`$ of a new column $`X`$ and its source node $`v`$. Take the number $`j`$ with $`\mu_j(\mathrm{col}\,v) = X`$. It is as follows, and it is unique.

- If $`u`$ comes from a pair of the lower part, $`j`$ is the block number of $`X`$. The source column is $`x`$ and $`X = x + j \cdot w`$.
- If $`u`$ is a copy of the upper part and $`X`$ is a copy of $`x \lt x_0`$, $`j`$ is the block number of $`X`$.
- If $`u`$ is a copy of the upper part and $`X = x_0 + b \cdot w`$ (a copy of $`x = x_0`$), the source column is $`c_r`$ and $`j = b + 1`$, because $`\mu_{b+1}(c_r) = c_r + (b+1) \cdot w = x_0 + b \cdot w`$.

Then the following two hold.

```math
\ell(u) = \mu_j\bigl(\ell(v)\bigr), \qquad \kappa(\mathrm{at}(u)) \le \mu_j\bigl(\kappa(\mathrm{at}(v))\bigr)
```

**Assembling the classification.** From (iv)–(vi) we get the classification of each atom $`(P, X, K)`$ of $`E_D(M(s[n]))`$.

- If $`X \lt x_0`$: by (iv), the output columns $`0, \ldots, x_0 - 1`$ are the columns of $`M(s)`$ themselves. A leg atom is determined by its column and the columns to its left only ([06](06-combinatorial-layer.md) §4). So the atom is in $`E_D(M(s))`$ and is classified by (base).
- If $`x_0 + i \cdot w \le X \lt x_0 + (i+1) \cdot w`$ and the $`j`$ of $`u`$ is $`i + 1`$ (the columns other than the border column $`x_0 + i \cdot w`$, and the copies of the upper part in the border column): the column of the source $`v`$ is $`c_r + X - (x_0 + i \cdot w)`$, which is below $`x_0`$. So $`\mathrm{at}(v)`$ is in $`F`$. If $`\ell(v) \lt c_r`$ then $`P = \ell(v) \lt c_r`$; otherwise $`P = \ell(v) + (i+1) \cdot w \ge x_0 + i \cdot w`$. In both cases $`P' = \ell(v)`$, and the key inequality of (v) is exactly the condition of (reservoir).
- If $`X = x_0 + i \cdot w`$ and $`u`$ is not a copy of the upper part ($`j = i`$): the source $`v`$ is a node of column $`x_0`$ whose row is below $`\tau`$, so it is below $`t`$. $`\mathrm{at}(v)`$ is in $`T`$ and $`\mu_i(\ell(v)) = P`$. By (v) and (vi), $`K \le \mu_i(\kappa(\mathrm{at}(v))) \lt \mu_i(K_c)`$. Since $`\mu_i`$ is strictly increasing on columns, it preserves $`\lt`$ of templates (for the same reason as Theorem 1 of [06](06-combinatorial-layer.md) §1). So the atom is classified by (seam).

(i)–(iii) and the classification give all of items 1–4 of the classification lemma.

**Example ($`(1,3,3)[2]`$, computed with Python).** $`D = 1`$, $`c_r = 0`$, $`w = 2`$, $`x_0 = 2`$, $`K_c = (\top, \top)`$. Leg atoms are written as (leg, column, template).

| Node $`u`$ | Origin | Source $`v`$ | $`\mathrm{at}(u)`$ | $`\mathrm{at}(v)`$ | $`j`$ | $`\mu_j(\kappa(\mathrm{at}(v)))`$ | Classification |
|---|---|---|---|---|---|---|---|
| $`(2,0)`$ | copy of the root row | $`(2,0)`$ | $`(1, 2, (0,0))`$ | $`(1, 2, (0,0))`$ | 0 | $`(0,0)`$ | seam |
| $`(2,1)`$ | plain copy | $`(2,1)`$ | $`(0, 2, (0,\top))`$ | $`(0, 2, (0,\top))`$ | 0 | $`(0,\top)`$ | seam |
| $`(3,0)`$ | copy of the root row | $`(1,0)`$ | $`(2, 3, (0,0))`$ | $`(0, 1, (0,0))`$ | 1 | $`(2,2)`$ | reservoir |
| $`(3,1)`$ | gap copy | $`(1,0)`$ | $`(2, 3, (2,2))`$ | $`(0, 1, (0,0))`$ | 1 | $`(2,2)`$ | reservoir |
| $`(3,2)`$ | plain copy | $`(1,1)`$ | $`(2, 3, (2,\top))`$ | $`(0, 1, (0,\top))`$ | 1 | $`(2,\top)`$ | reservoir |
| $`(3,\omega)`$ | copy of the upper part | $`(1,\omega)`$ | $`(2, 3, (\top,\top))`$ | $`(0, 1, (\top,\top))`$ | 1 | $`(\top,\top)`$ | reservoir |
| $`(4,0)`$ | copy of the root row | $`(2,0)`$ | $`(3, 4, (0,0))`$ | $`(1, 2, (0,0))`$ | 1 | $`(2,2)`$ | seam |
| $`(4,1)`$ | gap copy | $`(2,0)`$ | $`(3, 4, (2,2))`$ | $`(1, 2, (0,0))`$ | 1 | $`(2,2)`$ | seam |
| $`(4,2)`$ | plain copy | $`(2,1)`$ | $`(2, 4, (2,\top))`$ | $`(0, 2, (0,\top))`$ | 1 | $`(2,\top)`$ | seam |
| $`(5,0)`$ | copy of the root row | $`(1,0)`$ | $`(4, 5, (0,0))`$ | $`(0, 1, (0,0))`$ | 2 | $`(4,4)`$ | reservoir |
| $`(5,1)`$ | gap copy | $`(1,0)`$ | $`(4, 5, (2,2))`$ | $`(0, 1, (0,0))`$ | 2 | $`(4,4)`$ | reservoir |
| $`(5,2)`$ | gap copy | $`(1,0)`$ | $`(4, 5, (4,4))`$ | $`(0, 1, (0,0))`$ | 2 | $`(4,4)`$ | reservoir |
| $`(5,3)`$ | plain copy | $`(1,1)`$ | $`(4, 5, (4,\top))`$ | $`(0, 1, (0,\top))`$ | 2 | $`(4,\top)`$ | reservoir |
| $`(5,\omega)`$ | copy of the upper part | $`(1,\omega)`$ | $`(4, 5, (\top,\top))`$ | $`(0, 1, (\top,\top))`$ | 2 | $`(\top,\top)`$ | reservoir |

In every row, the leg of $`\mathrm{at}(u)`$ is the leg of $`\mathrm{at}(v)`$ mapped by $`\mu_j`$, and the template of $`\mathrm{at}(u)`$ is at most $`\mu_j(\kappa(\mathrm{at}(v)))`$. For example, the template of row 1 of column 3 (a gap copy) is $`(2,2)`$, equal to the template $`(0,0)`$ of the source $`(1,0)`$ mapped by $`\mu_1`$, which is $`(2,2)`$. The template of row 2 of column 5 (a gap copy) is $`(4,4)`$, equal to the one mapped by $`\mu_2`$, $`(4,4)`$.

## 3. (vi) The control is the strongest

(vi) is a statement about $`M(s)`$ only. It follows from the next theorem.

**Theorem 1 (leg keys increase within a column).** For two nodes $`u`$ and $`u^+`$ of the same column of a mountain, $`\kappa(\mathrm{at}(u)) \lt \kappa(\mathrm{at}(u^+))`$.

The top node of column $`x_0`$ is $`t`$, and $`K_c = \kappa(\mathrm{at}(t))`$. Using Theorem 1 repeatedly, $`\kappa(\mathrm{at}(v)) \lt K_c`$ for every node $`v`$ below $`t`$. This is (vi).

**Example (computed with Python).** The templates of the leg atoms of column 2 of $`(1,3,5)`$ are, from the bottom, $`(0,0) \lt (0,1) \lt (\top,\top)`$ (Example 1 of [06](06-combinatorial-layer.md) §10).

**Idea of the proof.** The leg end $`p_u`$ is the first candidate in the search for the parent of $`u^+`$. The first round of the parent search of [05](05-omegay-mountain.md) §3 moves to the parent of $`u`$ (to the bottom node of column $`\mathrm{col}(u) - 1`$ if $`u`$ is a bottom node) and climbs as long as the row is at most $`\mathrm{row}(u)`$. So we compare $`\mathrm{at}(u)`$ and $`\mathrm{at}(u^+)`$ through the parent $`\pi(u^+)`$ of $`u^+`$. If $`\pi(u^+) = p_u`$, the template of $`\mathrm{at}(u)`$ equals the key of the edge $`(u, u^+)`$. The proof splits into cases by the positions of $`\pi(u^+)`$ and the leg end of $`u^+`$. We do not write the case analysis here.

We checked with Python that Theorem 1 holds in every column of the mountains of the 624 expressions of length at most 5 with values at most 5 (excluding those whose last entry is 1).

## 4. (i), (ii), (iii)

**(i) Output length.** The output columns are the columns $`0, \ldots, x_0 - 1`$, one column of block 0, $`w`$ columns for each of the blocks $`1, \ldots, n-1`$, and $`w - 1`$ columns of block $`n`$ ([05](05-omegay-mountain.md) §5.1). In total there are $`x_0 + 1 + (n-1) \cdot w + (w - 1) = x_0 + n \cdot w`$ columns.

**(ii) Output mountain.** The values fixed by the rule are positive integers: the value of a top node is 1, and every other value is a sum of positive numbers. Column 0 does not change, so the first entry of $`s[n]`$ is $`s_0 = 1`$. So $`s[n]`$ is an expression and its mountain can be built ([05](05-omegay-mountain.md) §3).

**(iii) Preservation of degree.** Every row put by the rule is one of the following.

- The rows of the columns $`0, \ldots, x_0 - 1`$ and of the upper part: these are rows of $`M(s)`$, so their degree is at most $`D`$.
- The rows of the lower part: each lies in a region $`L_{k,j}`$, so it is below $`\tau`$. If $`\alpha \lt \tau`$ then $`\deg \alpha \le \deg \tau \le D`$.

So the degree of the mountain built by the rule is at most $`D`$. By (iv) this is also the degree of $`M(s[n])`$.

## 5. (iv) Reconstruction

We show that each column of the mountain built by the rule is the column that the construction of [05](05-omegay-mountain.md) §3 produces when it builds the same column of $`M(s[n])`$. For a new column $`X`$ it suffices to show the following three things, from the bottom up. By induction within the column, the construction of $`M(s[n])`$ puts the same nodes in the same order as the rule. The values agree, since in both the top value is 1 and the values are fixed by $`v(u) = v(u^+) + v(\pi(u^+))`$.

**(a) The bottom node.** The bottom node of a column of the rule is at row 0 and has no parent. Its value is an entry of $`s[n]`$. This is the same as the bottom node of $`M(s[n])`$.

**(b) The row law.** For adjacent nodes $`u`$, $`u^+`$ of a column of the rule, let $`\pi(u^+)`$ be the recorded parent of $`u^+`$ (the parent fixed in [05](05-omegay-mountain.md) §5.2). We show:

```math
\mathrm{row}(u^+) = B\bigl(\mathrm{row}(u),\ \mathrm{row}(\pi(u^+))\bigr)
```

We split this into two parts.

1. $`\mathrm{row}(u^+) = \mathrm{row}(u) + \omega^e`$ for some $`e`$. This is shown directly from the cases of the rule.
2. **The jump law**: this $`e`$ equals $`\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\pi(u^+)))`$.

The jump law is shown in 4 cases by where $`u`$ and $`u^+`$ are.

- Block 0 (column $`x_0`$).
- $`u`$ and $`u^+`$ are both in the upper part.
- $`u`$ is in the lower part and $`u^+`$ is in the upper part.
- In a column of block $`i \ge 1`$, $`u`$ and $`u^+`$ are both in the lower part.

In the last case, the column $`\mu_i(\ell)`$ of the recorded parent is a column of the same block, the previous border column $`c_r + i \cdot w`$, or a column left of $`c_r`$. For a column of the same block, we use that the trees of items of the two columns follow the trees of items of the two source columns in the same way. For the previous border column, we use the next fact. The case of a column left of $`c_r`$ is shown separately.

**Fact (coefficient of the border column).** Let $`S`$ be a region of level 2 or more in which column $`x_0`$ ascends. For $`0 \le i \lt n`$, the $`h_S`$ of $`\mathrm{top}_S`$ of the output column $`x_0 + i \cdot w`$ is:

```math
h_0 + (h_0 - h_r) \cdot i
```

$`h_0, h_r`$ are the symbols of [05](05-omegay-mountain.md) §5.4. We also checked this with Python for the regions of the initial items ($`L_{k,j}`$), in 1608 cases from the expressions of length at most 5 with values at most 5 and $`n = 1, 2, 3`$.

Example: in the region $`L_{1,0}`$ of $`(1,3,3)[2]`$, $`h_0 = 1`$ and $`h_r = 0`$. The top coefficient of output column 2 is 1, and that of column 4 is 2 ([05](05-omegay-mountain.md) §6.1).

**(c) The parent chain.** When the construction of $`M(s[n])`$ searches for the parent of $`u^+`$, it reaches the recorded parent $`\pi(u^+)`$. We split this into two parts.

1. The row of the recorded parent is at most $`\mathrm{row}(u)`$.
2. When the first candidate of the parent search is not in the parent's column, the candidates reach the recorded parent, and the search does not stop at any candidate on the way.

When the first candidate is in the parent's column, the first candidate is the highest node of that column whose row is at most $`\mathrm{row}(u)`$. By 1, it is the recorded parent.

Part 2 is shown by the 4 kinds of origin of $`u^+`$.

- Gap copies: the node $`u`$ just below $`u^+`$ is a copy of the root row or a gap copy from the same source node. The two pairs have the same $`\ell`$, so the first candidate is in the parent's column.
- Plain copies, copies of the root row, copies of the upper part: we use the correspondence through top copies of §6.

## 6. (v) The key bound

The leg column of $`\mathrm{at}(u)`$ is $`\ell(u)`$, and the coordinates of its template are the columns of the scale roots of the leg end $`p_u`$ ([06](06-combinatorial-layer.md) §10). So to show (v), it suffices to make $`p_u`$ and its scale-root chains in the output mountain correspond to $`p_v`$ and its scale-root chains in $`M(s)`$, and to show that the columns of corresponding nodes are mapped by $`\mu_j`$.

**Shape of a copied column.** In the lower part of a new column $`X`$ the following hold.

1. Each node of the source column whose row is below $`\tau`$ is the source of exactly one copy that is not a gap copy (a plain copy or a copy of the root row).
2. The output nodes with the same source node are consecutive in the column. The first is a copy that is not a gap copy, and the rest are gap copies only.
3. The rows of the copies that are not gap copies increase strictly in the order of the source rows.

We also checked 1–3 with Python in 7614 new columns, from the expressions of length at most 5 with values at most 5 and $`n = 1, 2, 3`$.

**Definition (top copy).** In a new column, the highest of the nodes whose source is $`v`$ is called the **top copy** of $`v`$. By 2, it is the last gap copy if there are gap copies, and otherwise the copy that is not a gap copy.

**Route of the proof.**

- One step of a scale-root chain: a step to the scale-$`k`$ parent in the output mountain is matched with a step of the chain in $`M(s)`$ through top copies.
- The start of a chain: the leg end $`p_u`$ in the output mountain is matched with the leg end $`p_v`$ in $`M(s)`$. At the start, a correspondence through top copies alone does not hold. We use the weaker form "a copy or a top copy".
- From this correspondence, each coordinate of the template of $`\mathrm{at}(u)`$ is compared with the coordinate of the same scale of the template of $`\mathrm{at}(v)`$ mapped by $`\mu_j`$. Columns left of $`c_r`$ are not moved by $`\mu_j`$.
- Nodes that are gap copies are shown separately, using item 2 of the shape of a copied column (the run of gap copies). There the templates are compared lexicographically, starting from the coordinate of scale $`D`$.
- Nodes of the upper part whose leg is left of $`c_r`$ are shown separately.

## 7. A statement found false on the way

While the proof was being built, some statements that had passed the tests turned out to be false. We give one as an example.

**False statement.** For a node $`u`$ of column $`c`$ ($`c_r \lt c \le x_0`$) of $`M(s)`$ with $`\mathrm{row}(u) \lt \tau`$, $`\ell(u) \ge c_r`$.

**Counterexample (computed with Python).** $`s = (1,2,4,8,10,8)`$, with $`c_r = 2`$ and $`\tau = 3`$. The mountain is as follows (written as in the tables of [05](05-omegay-mountain.md) §3).

- Column 0: `0:1`
- Column 1: `0:2, 1:1←c0@0`
- Column 2: `0:4, 1:2←c1@0, 2:1←c1@1`
- Column 3: `0:8, 1:4←c2@0, 2:2←c2@1, 3:1←c2@2`
- Column 4: `0:10, 1:2←c3@0, 2:1←c1@1`
- Column 5: `0:8, 1:4←c2@0, 2:2←c2@1, 3:1←c2@2`

The parent of the node at row 2 of column 4 is $`(1, 1)`$, so its leg is column 1, left of $`c_r = 2`$. There is also a counterexample of length 5: for $`s = (1,3,9,11,9)`$, $`c_r = 1`$, $`\tau = \omega + 1`$, and the node at row $`\omega`$ of column 3 has leg column 0.

The statement does not fail on the 66429 sequences of positive integers starting with 1 of length 2 to 6 with values at most 9 (checked with Python). So tests on sequences with small values alone did not find it. The proof was changed to treat the case of a leg left of $`c_r`$ separately.

The other false statements and how they were fixed are in [notes/04-official-design.md](../../notes/04-official-design.md) §6.1 and [notes/05-large-value-audit.md](../../notes/05-large-value-audit.md) (Japanese).

## 8. The final theorem

**Theorem (final theorem).** $`\prec`$ is well-founded on the set of all finite sequences. Expansion cannot go on forever.

**Proof.** By §2–§6, the classification lemma ([06](06-combinatorial-layer.md) §11) holds. It is the assumption of Theorem 6 (descent) of [06](06-combinatorial-layer.md) §8. Theorem 6 uses the three theorems of [06](06-combinatorial-layer.md) §5, which were shown in [09](09-obligations.md). Applying the theorem of [02](02-well-founded.md) §6 as in [06](06-combinatorial-layer.md) §8, $`\prec`$ is well-founded. $`\square`$

This theorem has been proved without assumptions. The proof is carried out in ordinary set theory with the axiom of choice, and uses the regularity of $`\omega_1`$ ([01](01-ordinals.md) §5).

## 9. Numerical checks (not a proof)

On the 1872 expansions of the 624 expressions of length at most 5 with values at most 5 (excluding those whose last entry is 1) and $`n = 1, 2, 3`$, we checked the following with Python. Every check had 0 failures. One run takes a few seconds.

| Statement | Counted objects | Count |
|---|---|---:|
| (iv) reconstruction | expansions | 1872 |
| (iii) preservation of degree, (i) output length | expansions | 1872 |
| the leg column in (v), $`\ell(u) = \mu_j(\ell(v))`$ | new nodes | 31324 |
| the template inequality in (v) | new nodes | 31324 |
| Theorem 1 (leg keys increase within a column) | mountains | 624 |
| classification (item 4 of [06](06-combinatorial-layer.md) §11) | expansions | 1872 |

Of the 31324 nodes of (v), 1416 are copies of the upper part whose leg is left of $`c_r`$.

## 10. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Status" | the final theorem (§8) |
| [notes/04-official-design.md](../../notes/04-official-design.md) §5, §6 (Japanese) | well-foundedness assuming the classification, and the lemma that remained (§2) |
| [notes/04-official-design.md](../../notes/04-official-design.md) §6.1 (Japanese) | the course of the proofs of reconstruction, the key bound and the strongest control (§3–§7) |
| [notes/05-large-value-audit.md](../../notes/05-large-value-audit.md) §1 (Japanese) | false statements found on sequences with large values (§7) |
| [notes/06-final-assembly.md](../../notes/06-final-assembly.md) (Japanese) | the final assembly (§8) |
