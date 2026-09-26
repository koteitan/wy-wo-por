[← Back](README.md) | [English](05-omegay-mountain.md) | [Japanese](../05-omegay-mountain.md)

# The official ω-Y sequence and its mountain

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinals, Cantor normal form of ordinals below $`\omega^\omega`$, the coefficient of degree $`k`$ $`c_k(\alpha)`$, the degree $`\deg \alpha`$, the sum $`\alpha + \omega^e`$ |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded, the lexicographic order on finite sequences |

This note defines the expressions, the mountain and the expansion rule of the official ω-Y sequence. The rule is the transcription of [notes/03-official-rule.md](../../notes/03-official-rule.md) (Japanese), rewritten in the symbols of this note.

The example values were computed with a Python program that implements this rule. This program gives the same results as the implementation of this repository, [reference/official/omegay.cjs](../../reference/official/omegay.cjs), on 3897 expansions. They are the expansions $`s[n]`$ ($`n = 1, 2, 3`$, §5) of the expressions of length at most 5 with values at most 6, and of the expressions that appear in this note.

## 1. Expressions

**Definition (expression).** An **expression** is a finite sequence $`s = (s_0, \ldots, s_{x_0})`$ of positive integers that is empty or has $`s_0 = 1`$.

- The index $`c`$ of the term $`s_c`$ is called a **column**. Columns are counted from 0.
- The last column is written $`x_0`$.
- Expressions are ordered by the lexicographic order on finite sequences of [02](02-well-founded.md) §1. This order is not well-founded on the set of all expressions (the example $`(1,2) \gt (1,1,2) \gt (1,1,1,2) \gt \cdots`$ of [02](02-well-founded.md) §1).

**Source.** Yukito published the ω-Y sequence in 2021. On 2021-09-01 Yukito declared it complete and made Naruyoko's program [Study and Expand Sequence(仮)](https://naruyoko.github.io/StudyAndExpandSequence/) its definition. There is no definition in words. The rule of this note was transcribed by comparing with the outputs of that program ([notes/00-survey.md](../../notes/00-survey.md) §1.1, §1.2, [notes/03-official-rule.md](../../notes/03-official-rule.md) §6, Japanese).

## 2. Rows

A **row** of a mountain is an ordinal below $`\omega^\omega`$. The lowest row is 0. Rows are written $`\alpha, \beta`$. The coefficients $`c_k(\alpha)`$, the degree $`\deg \alpha`$ and the sum $`\alpha + \omega^e`$ are as in [01](01-ordinals.md) §1.

**Definition (jump).** The **jump** of two rows $`\alpha, \beta`$ is defined as follows.

```math
\mathrm{jump}(\alpha, \beta) = \begin{cases} 0 & (\alpha = \beta) \cr 1 + \max\{\, k \mid c_k(\alpha) \ne c_k(\beta) \,\} & (\alpha \ne \beta) \end{cases}
```

By definition $`\mathrm{jump}(\alpha, \beta) = \mathrm{jump}(\beta, \alpha)`$.

**Definition (next row).** $`B(\alpha, \beta) = \alpha + \omega^{\mathrm{jump}(\alpha, \beta)}`$.

**Example (computed with Python).**

| $`\alpha`$ | $`\beta`$ | $`\mathrm{jump}(\alpha, \beta)`$ | $`B(\alpha, \beta)`$ |
|---|---|---|---|
| $`0`$ | $`0`$ | 0 | $`1`$ |
| $`1`$ | $`1`$ | 0 | $`2`$ |
| $`1`$ | $`0`$ | 1 | $`1 + \omega = \omega`$ |
| $`\omega`$ | $`0`$ | 2 | $`\omega + \omega^2 = \omega^2`$ |
| $`\omega`$ | $`\omega`$ | 0 | $`\omega + 1`$ |
| $`\omega + 1`$ | $`\omega`$ | 1 | $`\omega \cdot 2`$ |

- If $`\alpha = \beta`$, the row goes up by 1. This is how rows behave in the mountain of the 1-Y sequence (the sequence treated by [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por)).
- If $`\alpha \ne \beta`$, the row goes up by a power of $`\omega`$. In the sum $`\alpha + \omega^e`$ the coefficients below degree $`e`$ vanish ([01](01-ordinals.md) §1).

## 3. The mountain

**Definition (mountain).** The **mountain** $`M(s)`$ of an expression $`s`$ is a set of nodes. A **node** is determined by a pair (column, row) and has a positive integer **value**. For a node $`u`$ we write $`\mathrm{col}(u)`$ for its column, $`\mathrm{row}(u)`$ for its row and $`v(u)`$ for its value. The columns $`c = 0, 1, \ldots, x_0`$ are built from left to right.

1. Put the **bottom node** of column $`c`$ at row 0 with value $`s_c`$.
2. While the top node $`u`$ of column $`c`$ has a value greater than 1, repeat the following. Find a node $`p`$ by the parent search below. Put a new node above $`u`$. Its row is $`B(\mathrm{row}(u), \mathrm{row}(p))`$ and its value is $`v(u) - v(p)`$. The node $`p`$ is called the **parent** of the new node.
3. When a node of value 1 has been put, column $`c`$ ends.

**Definition (parent search).** Let $`u`$ be the top node of column $`c`$ and $`v`$ its value. Start with the candidate $`q = u`$ and repeat the following.

1. Let the ceiling be $`\mathrm{row}(q)`$.
2. Move left. If $`q`$ is a bottom node, move to the bottom node of column $`\mathrm{col}(q) - 1`$. Otherwise move to the parent of $`q`$.
3. In the column reached, climb up as long as the row of the next node above is at most the ceiling. The node reached is the new candidate $`q`$.
4. If $`v(q) \lt v`$, stop. This $`q`$ is the parent.

For an expression a parent is always found. Each round moves the candidate to a column further left. Column 0 has only its bottom node, of value 1, and $`1 \lt v`$.

**Definition (parent, $`u^+`$, edge).** For a node $`u`$ that is not a bottom node, write $`\pi(u)`$ for the parent found when $`u`$ was put. The column of $`\pi(u)`$ is to the left of the column of $`u`$. Write $`u^+`$ for the node just above $`u`$. The pair $`(u, u^+)`$ is called an **edge**. $`\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\pi(u^+)))`$ is called the **jump of the edge**. By construction, every edge $`(u, u^+)`$ satisfies:

```math
\mathrm{row}(u^+) = B\bigl(\mathrm{row}(u),\ \mathrm{row}(\pi(u^+))\bigr), \qquad v(u) = v(u^+) + v(\pi(u^+))
```

In every column the top node has value 1.

**Definition (parent within the row).** If a node $`u`$ has $`u^+`$ and $`\mathrm{row}(\pi(u^+)) = \mathrm{row}(u)`$, write $`P(u) = \pi(u^+)`$ and call it the **parent within the row** of $`u`$. Then the jump of the edge is 0 and $`\mathrm{row}(u^+) = \mathrm{row}(u) + 1`$. Otherwise $`P(u)`$ does not exist. $`P(u)`$ is in the same row as $`u`$ and in a column to the left of $`u`$. Following $`P`$ inside one row corresponds to the parent of the 1-Y mountain.

**Definition (degree bound).** If the row of every node of a mountain has degree at most $`D`$, $`D`$ is called a **degree bound** of the mountain.

**How columns are written.** The nodes of a column are listed from the bottom as `row:value←c<column>@<row of parent>`. For example `1:16←c1@0` is the node at row 1 whose value is 16 and whose parent is the node of column 1 at row 0. A bottom node has no parent and is written like `0:20`.

**Example 1 ($`M(1,4,20)`$, computed with Python).**

- Column 0: `0:1`
- Column 1: `0:4, 1:3←c0@0, ω:2←c0@0, ω²:1←c0@0`
- Column 2: `0:20, 1:16←c1@0, 2:13←c1@1, ω:10←c1@1, ω+1:8←c1@ω, ω·2:6←c1@ω, ω²:4←c1@ω, ω²+1:3←c1@ω², ω²+ω:2←c1@ω², ω²·2:1←c1@ω²`

In column 1 every parent is $`(0, 0)`$ (column 0, row 0). The rows go $`B(0,0) = 1`$, $`B(1, 0) = \omega`$ (jump 1), $`B(\omega, 0) = \omega^2`$ (jump 2).

The parent search of column 2, from the bottom node up. At every node, the first candidate was the parent.

| Node (row, value) | Search | Parent (value) | Jump | Next row | Next value |
|---|---|---|---|---|---|
| $`0`$, 20 | bottom node, so move to the bottom node of column 1 | $`(1, 0)`$ (4) | 0 | $`1`$ | 16 |
| $`1`$, 16 | move to the parent $`(1, 0)`$; row $`1 \le 1`$, so climb to $`(1, 1)`$ | $`(1, 1)`$ (3) | 0 | $`2`$ | 13 |
| $`2`$, 13 | move to the parent $`(1, 1)`$; the row $`\omega`$ above is greater than 2, so no climb | $`(1, 1)`$ (3) | 1 | $`\omega`$ | 10 |
| $`\omega`$, 10 | move to the parent $`(1, 1)`$; row $`\omega \le \omega`$, so climb to $`(1, \omega)`$ | $`(1, \omega)`$ (2) | 0 | $`\omega + 1`$ | 8 |
| $`\omega + 1`$, 8 | move to the parent $`(1, \omega)`$; no climb | $`(1, \omega)`$ (2) | 1 | $`\omega \cdot 2`$ | 6 |
| $`\omega \cdot 2`$, 6 | the same | $`(1, \omega)`$ (2) | 2 | $`\omega^2`$ | 4 |
| $`\omega^2`$, 4 | move to the parent $`(1, \omega)`$ and climb to $`(1, \omega^2)`$ | $`(1, \omega^2)`$ (1) | 0 | $`\omega^2 + 1`$ | 3 |
| $`\omega^2 + 1`$, 3 | move to the parent $`(1, \omega^2)`$ | $`(1, \omega^2)`$ (1) | 1 | $`\omega^2 + \omega`$ | 2 |
| $`\omega^2 + \omega`$, 2 | the same | $`(1, \omega^2)`$ (1) | 2 | $`\omega^2 \cdot 2`$ | 1 |

When the new row reaches the row of the next node of column 1 ($`\omega`$, $`\omega^2`$), the candidate climbs to that node and the parent changes. Parents within the row are, for example, $`P((2, 0)) = (1, 0)`$ and $`P((2, 1)) = (1, 1)`$.

**Example 2 ($`M(1,3,3)`$, computed with Python).**

- Column 0: `0:1`
- Column 1: `0:3, 1:2←c0@0, ω:1←c0@0`
- Column 2: `0:3, 1:2←c0@0, ω:1←c0@0`

For the bottom node of column 2 (value 3), the first candidate $`(1, 0)`$ has value 3, which is not smaller than 3. The next candidate is the bottom node of column 0, of value 1, and it is the parent. $`P((2, 0)) = (0, 0)`$.

## 4. Regions

**Definition (region).** For $`d \ge 1`$ and a row $`\beta`$, the following set of rows is called "the **region** of level $`d`$ containing $`\beta`$".

```math
\{\, \alpha \mid c_k(\alpha) = c_k(\beta)\ \ (k \ge d - 1) \,\}
```

Regions are written $`S, T`$ (the letter $`B`$ is used for the next row of §2, so it is not used for regions).

- A region of level 1 is a set $`\{\beta\}`$ of one row.
- A region of level 2 is a set of rows that differ only in $`c_0`$. It corresponds to the rows of one 1-Y mountain.
- For a row $`\alpha`$ of a region $`S`$ of level $`d \ge 2`$, let $`h_S(\alpha) = c_{d-2}(\alpha)`$.
- $`S[j]`$ is the set of rows of $`S`$ whose coefficient of degree $`d - 2`$ is $`j`$. $`S[j]`$ is a region of level $`d - 1`$. If $`j \lt j'`$, every row of $`S[j]`$ is smaller than every row of $`S[j']`$.
- $`\mathrm{top}_S(c)`$ is the highest node of column $`c`$ whose row is in $`S`$. It may not exist.

**Example.** The region of level 2 containing 0 is $`\{\alpha \mid \alpha \lt \omega\}`$, with $`S[j] = \{j\}`$ and $`h_S(\alpha) = \alpha`$. The region of level 3 containing 0 is $`\{\alpha \mid \alpha \lt \omega^2\}`$, with $`S[j] = \{\alpha \mid \omega \cdot j \le \alpha \lt \omega \cdot (j+1)\}`$ and $`h_S(\alpha) = c_1(\alpha)`$. In column 2 of $`M(1,4,20)`$, the $`\mathrm{top}`$ in the region of level 3 containing 0 is the node at row $`\omega \cdot 2`$, with $`h_S = 2`$. The $`\mathrm{top}`$ in the region of level 2 containing 0 is the node at row 2, with $`h_S = 2`$.

## 5. The expansion rule

For a nonempty expression $`s`$ and a natural number $`n`$ (the number of copies) we define the expansion $`s[n]`$.

### 5.1 The root and blocks

- Let $`t`$ be the top node of column $`x_0`$ and $`\tau = \mathrm{row}(t)`$.
- If $`s_{x_0} = 1`$ ($`t`$ is a bottom node and has no parent) or $`n = 0`$, let $`s[n] = (s_0, \ldots, s_{x_0 - 1})`$. This only deletes the last term. From now on assume $`s_{x_0} \gt 1`$ and $`n \ge 1`$.
- Let the **root** be $`r = \pi(t)`$, the **root column** $`c_r = \mathrm{col}(r)`$, and the **width** $`w = x_0 - c_r`$.

The **column map** $`\mu_i`$ is defined as follows.

```math
\mu_i(c) = \begin{cases} c & (c \lt c_r) \cr c + i \cdot w & (c \ge c_r) \end{cases}
```

The output columns $`0, \ldots, x_0 - 1`$ are the columns of $`M(s)`$ themselves.

Next, the output columns $`X = x + i \cdot w`$ are built in the order $`i = 0, 1, \ldots, n`$, and for the same $`i`$ in increasing $`x`$. The range of $`x`$ is:

```math
x \in \begin{cases} \{x_0\} & (i = 0) \cr \{c_r + 1, \ldots, x_0\} & (1 \le i \lt n) \cr \{c_r + 1, \ldots, x_0 - 1\} & (i = n) \end{cases}
```

- The columns built with the number $`i`$ together are called **block** $`i`$. Block 0 is column $`x_0`$ alone. $`i`$ is called the **block number**.
- When column $`X`$ is built, the nodes read are always nodes of the original mountain $`M(s)`$. The one exception is $`u_q`$ of §5.4, which is read from an output column.
- $`s[n]`$ is the sequence of the values of the bottom nodes of the output columns. Its length is $`x_0 + n \cdot w`$.

### 5.2 Building a column

Column $`X = x + i \cdot w`$ is built from a list of pairs $`(\alpha', \ell)`$. $`\alpha'`$ is a row and $`\ell`$ is a column of $`M(s)`$ or "none". The pairs come from the lower part (§5.3, §5.4) and then the upper part (§5.5). The rows $`\alpha'`$ increase strictly.

- A pair $`(\alpha', \ell)`$ puts a node $`u`$ at row $`\alpha'`$ of column $`X`$.
- If $`\ell`$ is none, $`u`$ has no parent.
- Otherwise the parent of $`u`$ is the highest node of the output column $`\mu_i(\ell)`$ whose row is smaller than $`\alpha'`$. If there is no such node, $`u`$ has no parent. Since $`\mu_i(\ell) \lt X`$, this column is already built.
- Values are set from the top. The top node has value 1, and the others have $`v(u) = v(u^+) + v(\pi(u^+))`$.

### 5.3 The lower part and items

The rows below $`\tau`$ are split into regions. For $`k \ge 0`$ and $`j \lt c_k(\tau)`$, the following set is a region of level $`k + 1`$.

```math
L_{k,j} = \{\, \alpha \mid c_m(\alpha) = c_m(\tau)\ \ (m \gt k),\ \ c_k(\alpha) = j \,\}
```

These regions partition $`\{\alpha \mid \alpha \lt \tau\}`$. Ordered by decreasing $`k`$, and for the same $`k`$ by increasing $`j`$, they are in the order of rows. For example, if $`\tau = \omega`$ there is only $`L_{1,0} = \{\alpha \mid \alpha \lt \omega\}`$. If $`\tau = \omega + 2`$ there are $`L_{1,0}`$, $`L_{0,0} = \{\omega\}`$ and $`L_{0,1} = \{\omega + 1\}`$.

**Definition (item).** An **item** is a 5-tuple $`(S, T, C, o, \varepsilon)`$.

- $`S`$ is the source region (a region of rows of $`M(s)`$) and $`T`$ the target region. $`S`$ and $`T`$ have the same level.
- $`C`$ is, when a row of a node of the root column is copied, that row. When nothing is copied, write $`C = \bot`$.
- $`o`$ is a natural number (an offset).
- $`\varepsilon \in \{0, 1\}`$ tells whether the lower part of the region is skipped.

The initial list of items is $`(L_{k,j}, L_{k,j}, \bot, 0, 0)`$ in the order of rows. Items are processed from the front. An item of level 1 emits one pair or nothing. An item of level 2 or more is replaced in place by the list of its child items (in increasing $`j`$). So the processing is depth first.

**Items of level 1.** Let $`S = \{\alpha\}`$ and $`T = \{\alpha'\}`$.

- If column $`x`$ has no node at row $`\alpha`$, emit nothing.
- If $`C = \bot`$, emit the pair $`(\alpha', \ell)`$, where $`\ell`$ is the column of the parent of the node $`(x, \alpha)`$. If $`\alpha = 0`$, $`\ell`$ is none.
- If $`C \ne \bot`$, emit the pair $`(\alpha', \ell)`$, where $`\ell`$ is the column of the parent of the node $`(x, C)`$. If $`C = 0`$, let $`\ell = x - 1`$.

A pair from an item with $`C \ne \bot`$ uses the column of the parent of the node at row $`C`$ instead of the column of the parent of the node at row $`\alpha`$. Row $`C`$ is the row of a node of the root column. Such a pair from an item with $`\varepsilon = 0`$ is called a **copy of the root row**, and one from an item with $`\varepsilon = 1`$ a **gap copy**.

### 5.4 Items of level 2 or more

Let $`d \ge 2`$ be the level of $`S`$. Take the following nodes in $`M(s)`$.

- $`u_x = \mathrm{top}_S(x)`$. If it does not exist, emit nothing (there are no child items).
- $`u_0 = \mathrm{top}_S(x_0)`$ and $`u_r = \mathrm{top}_S(c_r)`$.
- $`h_x, h_0, h_r`$ are $`h_S`$ of the rows of $`u_x, u_0, u_r`$. If a node does not exist, the value is 0.

**Definition (ascends).** When all three of the following hold, we say "column $`x`$ **ascends** in region $`S`$".

1. $`u_r`$ exists.
2. Let the **reference row** $`Z`$ be $`\mathrm{row}(u_r) - 1`$ (the row with $`c_0`$ decreased by 1) if $`c_0(\mathrm{row}(u_r)) \gt 0`$, and $`\mathrm{row}(u_r)`$ otherwise. The node $`(x, Z)`$ exists.
3. Follow the parents within the row, $`(x, Z), P(x, Z), P^2(x, Z), \ldots`$. There is a first node whose column is at most $`c_r`$, and its column is exactly $`c_r`$.

This is the 1-Y test for ascending columns, done region by region.

**Symbols.**

- The **lift** $`\Delta = (h_0 - h_r) \cdot i`$.
- $`\delta = 1`$ (if $`d = 2`$) and $`\delta = 0`$ (if $`d \ge 3`$).
- $`u_q = \mathrm{top}_T(c_r + i \cdot w)`$ is taken from the **output** column $`c_r + i \cdot w`$. For $`i = 0`$ this is column $`c_r`$, and for $`i \ge 1`$ it is the last column of the previous block. $`h_q`$ is $`h_T`$ of the row of $`u_q`$ (0 if it does not exist).
- The **number of generations** $`g`$ (used only in case 4): if $`C \ne 0`$, it is the number of times of the step "from column $`c`$, move to the column of the parent of the node $`(c, C)`$", starting at column $`x`$, until the column is at most $`c_r`$. If $`C = 0`$, let $`g = x - c_r`$.

The child items are made in four cases. $`[\,\cdot\,]`$ is 1 if the condition holds and 0 otherwise.

**Case 1: column $`x`$ does not ascend in region $`S`$.** Copy as it is: for $`j = 0, \ldots, h_x`$, the child $`(S[j], T[j], \bot, 0, 0)`$.

**Case 2: it ascends, $`C = \bot`$ and $`\varepsilon = 0`$.** For $`j = 0, \ldots, h_x + \Delta`$, make the following children.

| Range | Child item |
|---|---|
| $`j \lt h_r`$ | $`(S[j], T[j], \bot, 0, 0)`$ |
| $`h_r \le j \lt h_r + \Delta + \delta`$ | $`(S[h_r], T[j], \mathrm{row}(u_r), 0, [j \gt h_r])`$ |
| $`j \ge h_r + \Delta + \delta`$ | $`(S[j - \Delta], T[j], \bot, 0, [i \ne 0 \wedge j = h_r + \Delta])`$ |

$`S[j]`$ ($`j \lt h_r`$) is copied as it is. $`S[j]`$ ($`j \ge h_r + \delta`$) is lifted to $`T[j + \Delta]`$. The $`T[j]`$ in between ($`h_r \le j \lt h_r + \Delta + \delta`$) receive copies of the root row $`\mathrm{row}(u_r)`$.

**Case 3: it ascends, $`C = \bot`$ and $`\varepsilon = 1`$.** Let $`H = h_q + h_x`$ ($`H = h_x`$ if $`i = 0`$). For $`j = h_r, \ldots, H`$, make the following children.

| Range | Child item |
|---|---|
| $`j \lt h_r + h_q + \delta`$ | $`(S[h_r], T[j - h_r], \mathrm{row}(u_r), 0, 1)`$ |
| otherwise | $`(S[j - h_q], T[j - h_r], \bot, 0, [j = h_r + h_q])`$ |

**Case 4: it ascends and $`C \ne \bot`$.** The root row is being copied. Let $`H = h_q + g - o`$ ($`H = h_x`$ if $`i = 0`$). For $`j = 0, \ldots, H`$, let $`o_j = \max(j - h_q + o,\ 0)`$ and make the following children.

| Condition | Child item |
|---|---|
| $`\varepsilon = 1`$ | $`(S[h_r], T[j], C, o_j, 1)`$ |
| $`\varepsilon = 0`$, $`j \lt h_r`$ | $`(S[j], T[j], \bot, 0, 0)`$ |
| $`\varepsilon = 0`$, $`j \ge h_r`$ | $`(S[h_r], T[j], C, o_j, [j \gt h_r])`$ |

### 5.5 The upper part

Let $`x' = x`$ (if $`x \lt x_0`$) and $`x' = c_r`$ (if $`x = x_0`$). For the nodes $`u`$ of column $`x'`$ of $`M(s)`$ whose row is at least $`\tau`$, emit the pairs $`(\mathrm{row}(u), \ell)`$ from the bottom up, where $`\ell`$ is the column of $`\pi(u)`$. Rows at least $`\tau`$ are not lifted.

### 5.6 Cases that do not occur

In the following cases the rule has no meaning. In this note the expansion fails in these cases.

- A column does not ascend, but $`C \ne \bot`$, $`o \ne 0`$ or $`\varepsilon = 1`$.
- In case 4 with $`\varepsilon = 0`$, $`u_q`$ does not exist or $`o \ne 0`$.
- In case 4 or in an item of level 1, the node $`(x, C)`$ does not exist. While counting generations, a node at row $`C`$ does not exist.
- In one column the rows do not increase strictly.

None of them occurred in the tests against the official program ([notes/03-official-rule.md](../../notes/03-official-rule.md) §6, Japanese).

## 6. Examples

### 6.1 $`(1,3,3)[2]`$

$`M(1,3,3)`$ is Example 2 of §3. $`t = (2, \omega)`$, $`\tau = \omega`$, $`r = (0, 0)`$, $`c_r = 0`$, $`w = 2`$. The output columns 0 and 1 are those of $`M(s)`$. Block 0 is column 2 ($`x = 2`$), block 1 is column 3 ($`x = 1`$) and column 4 ($`x = 2`$), and block 2 is column 5 ($`x = 1`$). Since $`\tau = \omega`$, the only region of the lower part is $`L_{1,0} = \{\alpha \mid \alpha \lt \omega\}`$ (level 2).

**Column 4 ($`i = 1`$, $`x = 2`$), step by step.**

1. Item $`(L_{1,0}, L_{1,0}, \bot, 0, 0)`$ (level 2). $`S[j] = \{j\}`$. $`u_x = u_0 = (2, 1)`$ and $`u_r = (0, 0)`$, so $`h_x = h_0 = 1`$ and $`h_r = 0`$. $`\Delta = (1 - 0) \cdot 1 = 1`$ and $`\delta = 1`$.
2. Does it ascend? $`c_0(\mathrm{row}(u_r)) = 0`$, so $`Z = 0`$. $`P((2, 0)) = (0, 0)`$, and its column 0 is exactly $`c_r`$. Column 2 ascends.
3. Case 2 makes the children for $`j = 0, 1, 2`$. $`j = 0, 1`$ satisfy $`h_r \le j \lt 2`$ and give $`(S[0], T[0], 0, 0, 0)`$ and $`(S[0], T[1], 0, 0, 1)`$. $`j = 2`$ gives $`(S[1], T[2], \bot, 0, 0)`$.
4. $`(S[0], T[0], 0, 0, 0)`$: since $`C = 0`$, $`\ell = x - 1 = 1`$, and the pair $`(0, 1)`$ is emitted. At row 0 there is no parent. This is a copy of the root row.
5. $`(S[0], T[1], 0, 0, 1)`$: the pair $`(1, 1)`$ is emitted. $`\mu_1(1) = 3`$, so the parent is the node of output column 3 at row 0. This is a gap copy.
6. $`(S[1], T[2], \bot, 0, 0)`$: the parent of the node $`(2, 1)`$ is in column 0, and the pair $`(2, 0)`$ is emitted. $`\mu_1(0) = 2`$, so the parent is the highest node of output column 2 below row 2, namely the node at row 1.
7. Upper part: $`x = x_0`$, so column $`c_r = 0`$ is read. Column 0 has no node at a row $`\omega`$ or more.
8. The result is `0, 1←c3@0, 2←c2@1`. The values from the top are 1, $`1 + 1 = 2`$, $`2 + 5 = 7`$ (the node of output column 2 at row 1 has value 1, the node of column 3 at row 0 has value 5).

**Output columns 2 to 5 (computed with Python).**

- Column 2: `0:2, 1:1←c0@0`
- Column 3: `0:5, 1:3←c2@0, 2:2←c2@1, ω:1←c2@1`
- Column 4: `0:7, 1:2←c3@0, 2:1←c2@1`
- Column 5: `0:12, 1:5←c4@0, 2:3←c4@1, 3:2←c4@2, ω:1←c4@2`

Hence $`s[2] = (1, 3, 2, 5, 7, 12)`$.

### 6.2 Column 4 of $`(1,4,4)[2]`$ (an example of case 4)

Columns 1 and 2 of $`M(1,4,4)`$ are both `0:4, 1:3←c0@0, ω:2←c0@0, ω²:1←c0@0` (computed with Python). $`t = (2, \omega^2)`$, $`\tau = \omega^2`$, $`c_r = 0`$, $`w = 2`$, and the only region of the lower part is $`L_{2,0} = \{\alpha \mid \alpha \lt \omega^2\}`$ (level 3). Column 4 has $`i = 1`$ and $`x = 2`$.

1. The item of level 3: $`h_S = c_1`$. $`u_x = u_0 = (2, \omega)`$ and $`u_r = (0, 0)`$, so $`h_x = h_0 = 1`$, $`h_r = 0`$, $`\Delta = 1`$ and $`\delta = 0`$. Column 2 ascends ($`Z = 0`$, $`P((2,0)) = (0,0)`$). In case 2 the children are $`(S[0], T[0], 0, 0, 0)`$, $`(S[0], T[1], \bot, 0, 1)`$ and $`(S[1], T[2], \bot, 0, 0)`$.
2. The first child (level 2, case 4): $`C = 0`$, so $`g = x - c_r = 2`$. $`u_q`$ is the top node below $`\omega`$ of output column 2 (`0:3, 1:2←c0@0, ω:1←c0@0`), so $`h_q = 1`$. $`H = 1 + 2 - 0 = 3`$, and the root row is copied to rows 0 to 3. The parent column is $`\mu_1(x - 1) = 3`$.
3. The second child (level 2, case 3): $`T = \{\alpha \mid \omega \le \alpha \lt \omega \cdot 2\}`$. The top of this region in output column 2 is row $`\omega`$, so $`h_q = 0`$. $`H = 0 + 1 = 1`$. A gap copy is put at row $`\omega`$ (parent column 3), and a copy of the node $`(2, 1)`$ at row $`\omega + 1`$ (parent column $`\mu_1(0) = 2`$).
4. The third child (level 2): the source region $`\{\alpha \mid \omega \le \alpha \lt \omega \cdot 2\}`$ has no node of column $`c_r = 0`$, so the column does not ascend (case 1). A copy of the node $`(2, \omega)`$ is put at row $`\omega \cdot 2`$ (parent column 2).
5. The result (computed with Python) is `0:34, 1:23←c3@0, 2:15←c3@1, 3:9←c3@2, ω:3←c3@2, ω+1:2←c2@ω, ω·2:1←c2@ω`.

The gap copies are the three nodes at rows 1, 2, 3. This number 3 is the sum of the number of generations $`g = 2`$ and $`h_q = 1`$.

### 6.3 Table of expansions (computed with Python)

| Expression $`s`$ | $`n`$ | $`s[n]`$ |
|---|---|---|
| $`(1,2)`$ | 3 | $`(1,1,1,1)`$ |
| $`(1,2,2)`$ | 2 | $`(1,2,1,2,1,2)`$ |
| $`(1,2,3)`$ | 2 | $`(1,2,2,2)`$ |
| $`(1,2,4)`$ | 2 | $`(1,2,3,4)`$ |
| $`(1,3)`$ | 2 | $`(1,2,4)`$ |
| $`(1,3)`$ | 3 | $`(1,2,4,8)`$ |
| $`(1,3,3)`$ | 0 | $`(1,3)`$ |
| $`(1,3,3)`$ | 1 | $`(1,3,2,5)`$ |
| $`(1,3,3)`$ | 2 | $`(1,3,2,5,7,12)`$ |
| $`(1,3,3)`$ | 3 | $`(1,3,2,5,7,12,19,31)`$ |
| $`(1,3,4)`$ | 1 | $`(1,3,3)`$ |
| $`(1,3,4)`$ | 2 | $`(1,3,3,3)`$ |
| $`(1,4)`$ | 1 | $`(1,3)`$ |
| $`(1,4)`$ | 2 | $`(1,3,10)`$ |
| $`(1,4)`$ | 3 | $`(1,3,10,37)`$ |
| $`(1,4,4)`$ | 2 | $`(1,4,3,11,34,101)`$ |
| $`(1,3,2,5,5)`$ | 3 | $`(1,3,2,5,4,9,8,17,16,33)`$ |

## 7. The difference from weak-magma ω-Y

Weak-magma ω-Y, whose termination Phyrion proved, is a different sequence whose expansion rule differs from the official one. Its rule is in note 05 of [study/ of koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por/tree/main/study). The rules differ in three places ([notes/03-official-rule.md](../../notes/03-official-rule.md) §4, Japanese).

| Part | weak-magma ω-Y | official (§5) |
|---|---|---|
| which nodes are lifted | the nodes connected to a node of the root column by a chain of parents within the row are chosen, and the nodes above them are lifted | for each region, the reference row $`Z`$ decides whether a column ascends. An ascending column lifts all $`S[j]`$ ($`j \ge h_r`$) together |
| how much is lifted | counted from the rows of the last column of the previous block | the difference of coefficients in the region, $`\Delta = (h_0 - h_r) \cdot i`$ |
| how the gap is filled | the parents of the gap nodes are all taken from one column | copies of the root row. The parent column is the image of the column of the parent of the node at row $`C`$ (for $`C = 0`$, the image of the column one to the left) |

Values from [notes/00-survey.md](../../notes/00-survey.md) §1.6 (Japanese): in weak-magma ω-Y, $`(1,3,3)[2] = (1,3,2,5,4,9)`$ and $`(1,4,4)[2] = (1,4,3,11,10,38)`$. In the official system they are $`(1,3,2,5,7,12)`$ and $`(1,4,3,11,34,101)`$ as in §6.3. This note does not compute values of weak-magma ω-Y.

In the official system, the supremum of the sequence $`(1,3,2,5,4,9,8,17,\ldots)`$ is $`(1,3,2,5,5)`$. Indeed $`(1,3,2,5,5)[n]`$ is as follows (computed with Python).

```math
(1,3,2,5,5)[1] = (1,3,2,5,4,9), \quad (1,3,2,5,5)[2] = (1,3,2,5,4,9,8,17), \quad (1,3,2,5,5)[3] = (1,3,2,5,4,9,8,17,16,33)
```

This agrees with the statement of the [Googology Wiki (Miraheze) article](https://googology.miraheze.org/wiki/%5C(%5Comega%5C)-Y_sequence). The official $`(1,3,3)`$ is larger, and $`(1,3,3)[n]`$ is $`(1,3,2,5,7,12,\ldots)`$. In weak-magma ω-Y, $`(1,3,3)[n]`$ is $`(1,3,2,5,4,9,\ldots)`$.

## 8. One-step expansion and the final theorem

**Definition (one-step expansion).** For finite sequences $`s, t`$, $`t \prec s`$ means that $`s`$ is nonempty and, for some $`n`$, $`s[n]`$ is defined and $`t = s[n]`$.

For a sequence that is not an expression (for example one containing 0), the mountain cannot be built, so the expansion fails. The cases of §5.6 are failures too. There is no $`\prec`$-step from a sequence whose expansion fails.

**Final theorem.** $`\prec`$ is well-founded on the set of all finite sequences. In other words, expansion cannot go on forever: there is no infinite sequence $`s_0 \succ s_1 \succ s_2 \succ \cdots`$.

The proof is in [06](06-combinatorial-layer.md) to [10](10-official-descent.md).

In the tested range, $`s[n]`$ was always lexicographically smaller than $`s`$. We checked it on the 1872 expansions of the expressions of length at most 5 with values at most 5 (except those with last term 1) with $`n = 1, 2, 3`$ (Python). But the lexicographic order is not well-founded on the set of all expressions (§1), so the final theorem does not follow from this.

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) introduction | the definition of the official ω-Y (Naruyoko's program), the difference from weak-magma ω-Y |
| [README](../../README-en.md) "Status" | the final theorem (§8) |
| [notes/00-survey.md](../../notes/00-survey.md) §1.1–§1.3, §1.6 (Japanese) | sources, the shape of the mountain, the comparison experiment with weak-magma ω-Y |
| [notes/01-feasibility.md](../../notes/01-feasibility.md) §1.1, §2 (Japanese) | notation, the difference in filling the gap |
| [notes/03-official-rule.md](../../notes/03-official-rule.md) §1–§6 (Japanese) | the whole expansion rule, examples, the differential test against the official program |
