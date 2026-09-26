[← Back](README.md) | [English](06-combinatorial-layer.md) | [Japanese](../06-combinatorial-layer.md)

# The combinatorial layer and leg atoms

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | labels, $`\omega_1`$, $`\{0, \ldots, n-1\}`$ |
| [02 Well-founded relations and recursion](02-well-founded.md) | keys $`\mathrm{Key}_m`$, $`\top`$, coordinates, the first coordinate that differs, tops, termination by bounds on labels (§6) |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | templates, evaluation $`\mathrm{eval}`$, monotonicity |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | the arguments of the relation $`R(\theta, a, b)`$, requirements, the shape of finite reflection |
| [05 The official ω-Y sequence and its mountain](05-omegay-mountain.md) | expressions, rows, jumps, mountains, nodes, parents, $`u^+`$, edges, jumps of edges, degree bound $`D`$, $`t`$, root, $`c_r`$, $`w`$, $`x_0`$, $`\mu_i`$, blocks, $`s[n]`$, $`\prec`$, gap copies |

This note explains the part of the proof that does not use the meaning of labels. This part is called the **combinatorial layer**. The combinatorial layer comes from Phyrion's proof ([Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)). Phyrion proved it for weak-magma ω-Y ([05](05-omegay-mountain.md) §7). This note writes it as adapted to the official ω-Y.

- The combinatorial layer uses only three theorems (§5) about the relation $`R(\theta, a, b)`$. $`\theta`$ is a key and $`a, b`$ are labels ([04](04-patterns-of-resemblance.md) §4). $`R`$ is defined in [07](07-relation-r.md). This note does not use what $`R`$ is.
- The three theorems are proved in [09](09-obligations.md).
- What we changed from Phyrion's proof is the choice of the atoms that a representation carries. Instead of the edges of the mountain (§3) we use one leg atom per node (§10). With the edges of the mountain the proof does not go through for the official ω-Y (§9).

For a list of labels $`f`$ and a label $`b`$, we write $`f \lt b`$ when $`f(j) \lt b`$ for all $`j`$.

## 1. Templates over columns

We use the templates of [03](03-sigma1-elementary.md) §7 over the columns of a mountain. The variables are the columns. A template $`K`$ of length $`m`$ over $`n`$ columns puts a column number (an element of $`\{0, \ldots, n-1\}`$) or $`\top`$ in each coordinate. In this note templates are written $`K, K'`$ ($`t`$ is used for the top node of [05](05-omegay-mountain.md)). For labels of the columns $`f : \{0, \ldots, n-1\} \to \mathrm{Label}`$, the evaluated key $`\mathrm{eval}\,K\,f`$ has $`f(j)`$ in coordinate $`k`$ if $`K_k = j`$, and $`\top`$ if $`K_k = \top`$.

**Definition (key evaluated at column numbers).** The key $`\mathrm{eval}\,K\,\mathrm{id}`$, obtained by reading each column number $`j`$ as the label $`j`$, is called the **key of $`K`$ evaluated at column numbers**. Templates are compared, $`K \le K'`$ and $`K \lt K'`$, by comparing their keys evaluated at column numbers. In this note templates are written with column numbers, like $`(0, \top)`$.

**Theorem 1.** If $`f`$ is strictly increasing, then $`K \le K'`$ implies $`\mathrm{eval}\,K\,f \le \mathrm{eval}\,K'\,f`$, and $`K \lt K'`$ implies $`\mathrm{eval}\,K\,f \lt \mathrm{eval}\,K'\,f`$.

**Proof.** If $`K`$ and $`K'`$ are equal, this is clear. Otherwise let $`k`$ be the first coordinate that differs. The coordinates before $`k`$ are equal, so they are equal after evaluation by $`f`$. Since $`K \lt K'`$, coordinate $`k`$ is one of the following. If $`K_k = j`$ and $`K'_k = \top`$, then $`f(j) \lt \top`$. If $`K_k = j \lt j' = K'_k`$, then $`f(j) \lt f(j')`$ because $`f`$ is strictly increasing. In both cases $`\mathrm{eval}\,K\,f \lt \mathrm{eval}\,K'\,f`$. $`\square`$

So the comparison of templates is fixed by the column numbers alone, before any labels are chosen.

**Definition (relabelling).** For a column map $`\sigma : \{0, \ldots, n-1\} \to \{0, \ldots, n'-1\}`$, write $`\sigma(K)`$ for the template obtained by replacing each column number $`j`$ in $`K`$ by $`\sigma(j)`$. $`\top`$ stays. By definition, for labels $`h`$ of the new columns:

```math
\mathrm{eval}\,\sigma(K)\,h = \mathrm{eval}\,K\,(h \circ \sigma)
```

**Example.** Let $`m = 2`$ and $`n = 3`$. If $`K = (0, \top)`$ then $`\mathrm{eval}\,K\,f = (f(0), \top)`$. If $`K' = (0, 2)`$ then $`\mathrm{eval}\,K'\,f = (f(0), f(2))`$. Coordinate 0 is equal and in coordinate 1 we have $`2 \lt \top`$, so $`K' \lt K`$. If $`\sigma(j) = j + 1`$ then $`\sigma(K') = (1, 3)`$.

## 2. Atoms and diagrams

Let the columns be $`\{0, \ldots, n-1\}`$ and their labels $`f`$. The length of templates is a fixed $`m`$.

**Definition (internal atom).** An **internal atom** is a triple $`(p, q, K)`$, where $`p \lt q`$ are columns and $`K`$ is a template. It holds under $`f`$ if $`R(\mathrm{eval}\,K\,f,\ f(p),\ f(q))`$. $`p`$ is called the parent column of the atom and $`q`$ its child column.

**Definition (top atom).** A **top atom** is a pair $`(p, K)`$. It holds under $`f`$ with top $`b`$ if $`R(\mathrm{eval}\,K\,f,\ f(p),\ b)`$. A top atom is a requirement of [04](04-patterns-of-resemblance.md) §4 written as an atom.

$`\mathrm{eval}\,K\,f`$ is called the key of the atom.

**Definition (diagram).** A **diagram** $`(G, N)`$ is a pair of a finite list $`G`$ of internal atoms and a finite list $`N`$ of top atoms. The diagram holds under $`f`$ with top $`b`$ if every atom of $`G`$ holds under $`f`$ and every atom of $`N`$ holds under $`f`$ with top $`b`$.

## 3. Scale roots and keys of the edges of the mountain

Let $`M`$ be a mountain and $`D`$ a degree bound of it ([05](05-omegay-mountain.md) §3).

**Definition (scale root).** Let $`k`$ be a natural number. If a node $`u`$ has $`u^+`$ and the jump of the edge $`(u, u^+)`$ is at most $`k`$, then $`\pi(u^+)`$ is called the **scale-$`k`$ parent** of $`u`$. Otherwise $`u`$ has no scale-$`k`$ parent. The node reached from $`u`$ by following scale-$`k`$ parents until there is none is called the **scale-$`k`$ root** $`\rho_k(u)`$. Each step moves to a column further left, so this stops.

If $`k \lt k'`$, the path of scale-$`k`$ parents is an initial part of the path of scale-$`k'`$ parents. So $`\rho_{k'}(u)`$ is in the same column as $`\rho_k(u)`$ or further left.

**Definition (edge key).** Let $`e = (u, u^+)`$ be an edge with parent $`\pi = \pi(u^+)`$ and jump $`d`$. The degree of $`\mathrm{row}(u^+) = \mathrm{row}(u) + \omega^d`$ is at least $`d`$, so $`d \le D`$. The **edge key** of $`e`$ is the template of length $`D + 1`$ whose coordinates are the scales $`D, D-1, \ldots, 0`$ in this order.

```math
\kappa_D(e) = \bigl(\mathrm{col}\,\rho_D(\pi),\ \mathrm{col}\,\rho_{D-1}(\pi),\ \ldots,\ \mathrm{col}\,\rho_d(\pi),\ \underbrace{\top, \ldots, \top}_{d}\bigr)
```

The coordinate of scale $`k \ge d`$ is $`\mathrm{col}\,\rho_k(\pi)`$, and the coordinate of scale $`k \lt d`$ is $`\top`$. Every finite coordinate names a column at most the parent's column. It never names the child's column.

**Example (computed with Python).** $`f_j`$ is the label of column $`j`$. An edge is written (column, row of the lower node → row of the upper node).

| Expression | $`D`$ | Edge | Parent | Jump of the edge | Key |
|---|---|---|---|---|---|
| $`(1,3)`$ | 1 | column 1, $`0 \to 1`$ | $`(0, 0)`$ | 0 | $`(f_0, f_0)`$ |
| | | column 1, $`1 \to \omega`$ | $`(0, 0)`$ | 1 | $`(f_0, \top)`$ |
| $`(1,4)`$ | 2 | column 1, $`0 \to 1`$ | $`(0, 0)`$ | 0 | $`(f_0, f_0, f_0)`$ |
| | | column 1, $`1 \to \omega`$ | $`(0, 0)`$ | 1 | $`(f_0, f_0, \top)`$ |
| | | column 1, $`\omega \to \omega^2`$ | $`(0, 0)`$ | 2 | $`(f_0, \top, \top)`$ |
| $`(1,3,5)`$ | 1 | column 2, $`0 \to 1`$ | $`(1, 0)`$ | 0 | $`(f_0, f_0)`$ |
| | | column 2, $`1 \to \omega`$ | $`(0, 0)`$ | 1 | $`(f_0, \top)`$ |

The first edge of column 2 of $`(1,3,5)`$ has its parent in column 1, but its key names column 0. The edge from the parent $`(1, 0)`$ upward has jump 0, and its parent is $`(0, 0)`$. The key names the columns of the scale roots of the parent, not the parent's column.

**Theorem 2 (keys increase within a column).** For two edges in the same column, the key of the lower edge is smaller than the key of the upper edge. By Theorem 1 it is smaller under every strictly increasing labelling.

**Proof outline.** It suffices to compare two adjacent edges $`e_1 = (u, u^+)`$ and $`e_2 = (u^+, u^{++})`$. Let their parents be $`p_1 = \pi(u^+)`$, $`p_2 = \pi(u^{++})`$ and their jumps $`d_1, d_2`$.

- If $`p_2 = p_1`$: then $`d_2 = d_1 + 1`$. If $`d_1 = 0`$, then $`\mathrm{row}(u^+) = \mathrm{row}(p_1) + 1`$, so the jump is 1. If $`d_1 \ge 1`$, then $`\mathrm{row}(u)`$ and $`\mathrm{row}(p_1)`$ have equal coefficients of degree $`d_1`$ and more, and $`\mathrm{row}(u^+)`$ has only its coefficient of degree $`d_1`$ larger by 1. So $`\mathrm{row}(u^+)`$ and $`\mathrm{row}(p_1)`$ first differ at degree $`d_1`$. The two keys agree on the scales $`D, \ldots, d_1 + 1`$, and the coordinate of scale $`d_1`$ changes from $`\mathrm{col}\,\rho_{d_1}(p_1)`$ to $`\top`$. Hence $`\kappa_D(e_1) \lt \kappa_D(e_2)`$.
- If $`p_2 \ne p_1`$: this needs a long case analysis using the parent search. It is not proved here. It is in Phyrion's proof.

We checked with Python that it holds in every column of the mountains of the 624 expressions of length at most 5 with values at most 5 (except those with last term 1).

## 4. Atom systems and representations

**Definition (atom system).** An **atom system** $`E`$ fixes, for each mountain $`M`$ (and degree bound $`D`$), a finite list $`E(M)`$ of atoms $`(p, c, K)`$. Here $`p \lt c`$ are columns of $`M`$ and $`K`$ is a template of length $`D + 1`$ over the columns of $`M`$. The atoms are read as internal atoms.

Every atom system of this note has the following property. The mountain of a prefix $`s'`$ of an expression $`s`$ is the first columns of $`M(s)`$, and $`E(M(s'))`$ consists of the atoms of $`E(M(s))`$ whose child column is a column of $`s'`$. This is because the columns and the key of an atom are fixed by its child column and the columns to its left.

**Definition (representation).** A **representation** of a mountain $`M`$ (last column $`x_0`$) with respect to $`E`$ is a labelling of the columns $`f : \{0, \ldots, x_0\} \to \mathrm{Label}`$ such that:

1. $`f`$ is strictly increasing.
2. Every $`f(j)`$ is smaller than $`\omega_1`$.
3. Every atom $`(p, c, K)`$ of $`E(M)`$ holds under $`f`$, that is, $`R(\mathrm{eval}\,K\,f,\ f(p),\ f(c))`$.

In Phyrion's proof, $`E`$ is the list of the edges of the mountain. The atom of an edge $`e = (u, u^+)`$ is $`(\mathrm{col}\,\pi(u^+),\ \mathrm{col}\,u,\ \kappa_D(e))`$. We call this the **edge system**.

**Example.** A representation of $`(1,3,5)`$ with respect to the edge system is a labelling $`f_0 \lt f_1 \lt f_2 \lt \omega_1`$ satisfying the following (from the table of §3).

```math
R((f_0, f_0), f_0, f_1), \quad R((f_0, \top), f_0, f_1), \quad R((f_0, f_0), f_1, f_2), \quad R((f_0, \top), f_0, f_2)
```

## 5. The three theorems

The combinatorial layer uses only the following three theorems about $`R`$. $`\theta, \Theta`$ are keys and $`a, b, \beta`$ are labels. $`(G, N)`$ is a diagram over $`n`$ columns. The proofs are in [09](09-obligations.md).

**Theorem (key weakening).** If $`\theta \le \Theta`$ and $`R(\Theta, a, b)`$, then $`R(\theta, a, b)`$.

**Theorem (finite reflection).** Assume:

1. $`f : \{0, \ldots, n-1\} \to \mathrm{Label}`$ is strictly increasing and $`f \lt b`$.
2. Every atom of $`G`$ holds under $`f`$.
3. Every atom of $`N`$ has key $`\mathrm{eval}\,K\,f`$ smaller than $`\theta`$, and every atom of $`N`$ holds under $`f`$ with top $`b`$.
4. $`R(\theta, f(\mathrm{cut}), b)`$ for some column $`\mathrm{cut}`$. This column is called the **cut** and this relation the **control relation**.

Then there is $`g : \{0, \ldots, n-1\} \to \mathrm{Label}`$ with the following four properties.

1. $`g`$ is strictly increasing and $`g \lt f(\mathrm{cut})`$.
2. If $`j \lt \mathrm{cut}`$ then $`g(j) = f(j)`$.
3. $`g(j) \le f(j)`$ for all $`j`$.
4. Every atom of $`G`$ holds under $`g`$, and every atom of $`N`$ holds under $`g`$ with top $`f(\mathrm{cut})`$.

The columns named by the keys of atoms need not be before the cut. This is the answer to problem 3 of [04](04-patterns-of-resemblance.md) §4.

**Theorem (initial representation).** For every diagram $`(G, N)`$ there are $`\beta \lt \omega_1`$ and a strictly increasing $`f \lt \beta`$ such that the diagram holds under $`f`$ with top $`\beta`$.

## 6. One splice

One finite reflection adds columns. Let $`n`$ be the number of columns and $`\mathrm{cut}`$ the cut.

**Definition (column maps).** The new number of columns is $`n + (n - \mathrm{cut})`$. Two maps send an old column $`j \in \{0, \ldots, n-1\}`$ to a new column.

- The **identity map**: $`j \mapsto j`$.
- The **shift map**: $`\sigma(j) = j`$ ($`j \lt \mathrm{cut}`$), $`\sigma(j) = n + (j - \mathrm{cut})`$ ($`j \ge \mathrm{cut}`$).
- Column $`n = \sigma(\mathrm{cut})`$ is called the **border column**.

**Definition (new labels).** Let $`f`$ be the old labels and $`g`$ the labels obtained by finite reflection. The new labels $`h`$ are $`g(j)`$ for columns $`j \lt n`$ and $`f(\mathrm{cut} + j - n)`$ for columns $`j \ge n`$. The labels of the old columns $`\mathrm{cut}, \ldots, n-1`$ appear unchanged at the right end. By property 2 of finite reflection, $`h \circ \sigma = f`$.

**Example.** For $`n = 4`$ and $`\mathrm{cut} = 1`$ the new labels are:

```math
(g_0, g_1, g_2, g_3, f_1, f_2, f_3), \qquad g_0 = f_0,\quad g_1, g_2, g_3 \lt f_1
```

**Definition (classified atom).** An internal atom $`(P, Q, K)`$ over the new columns is **classified** with respect to the diagram $`(G, N)`$ and the cut if one of the following holds.

1. It is an atom of $`G`$.
2. There is an atom $`(p, q, K')`$ of $`G`$ with $`\sigma(p) = P`$, $`\sigma(q) = Q`$ and $`K \le \sigma(K')`$.
3. There is an atom $`(P, K')`$ of $`N`$ with $`Q = n`$ (the border column) and $`K \le K'`$.

**Theorem 3 (one splice).** Under the assumptions of finite reflection, the labels $`h`$ made from the $`g`$ obtained there are strictly increasing and $`h \lt b`$. Every classified atom holds under $`h`$.

**Proof.** $`g`$ is strictly increasing with $`g \lt f(\mathrm{cut}) = h(n)`$, and $`f(\mathrm{cut}), \ldots, f(n-1)`$ at the right end are strictly increasing, so $`h`$ is strictly increasing. $`g \lt f(\mathrm{cut}) \lt b`$ and $`f \lt b`$ give $`h \lt b`$.

1. The label of column $`j \lt n`$ is $`g(j)`$, so the atom holds by property 4 of finite reflection.
2. The atom of $`G`$ holds under $`f`$. By the relabelling equation and $`h \circ \sigma = f`$, $`\mathrm{eval}\,\sigma(K')\,h = \mathrm{eval}\,K'\,f`$, $`h(\sigma(p)) = f(p)`$ and $`h(\sigma(q)) = f(q)`$. By Theorem 1, $`\mathrm{eval}\,K\,h \le \mathrm{eval}\,\sigma(K')\,h`$, so it holds by key weakening.
3. By property 4 of finite reflection, $`R(\mathrm{eval}\,K'\,g,\ g(P),\ f(\mathrm{cut}))`$. We have $`h(P) = g(P)`$, $`h(n) = f(\mathrm{cut})`$ and $`\mathrm{eval}\,K'\,h = \mathrm{eval}\,K'\,g`$. It holds by Theorem 1 and key weakening. $`\square`$

## 7. Iterated reflection with reservoirs

An expansion repeats the splice $`n`$ times. For this, the facts needed for the next reflection are carried along as **reservoirs**.

**Definition (reservoirs, control atom, state).** The reservoirs are a list $`F`$ of internal atoms and a list $`T`$ of top atoms. The **control atom** is a top atom $`(p_c, K_c)`$. Let $`h`$ be labels of columns, $`\beta`$ a label (the top) and $`G`$ a list of internal atoms. The **state** $`(G, F, T, (p_c, K_c), h, \beta)`$ means that the following six hold.

1. $`h`$ is strictly increasing.
2. $`h \lt \beta`$.
3. Every atom of $`G`$ holds under $`h`$.
4. Every atom of $`F`$ holds under $`h`$.
5. Every atom of $`T`$ holds under $`h`$ with top $`\beta`$.
6. The control atom holds under $`h`$ with top $`\beta`$, that is, $`R(\mathrm{eval}\,K_c\,h,\ h(p_c),\ \beta)`$.

**Theorem 4 (splice with reservoirs).** Let $`(G, F, T, (p_c, K_c), h, \beta)`$ be a state, with $`n`$ columns and cut $`\mathrm{cut} = p_c`$. Let $`N`$ be a list of top atoms and $`H`$ a list of internal atoms over $`n + (n - \mathrm{cut})`$ columns such that:

- Each atom $`(p, K)`$ of $`N`$ has an atom $`(p, K')`$ of $`T`$ with $`K \le K'`$ ($`N`$ is covered by $`T`$).
- Each atom $`(p, K)`$ of $`N`$ has $`K \lt K_c`$.
- Every atom of $`H`$ is classified in the sense of §6, where the source atom of type 2 is taken from $`G`$ or $`F`$.

Then there are new labels $`h'`$ such that $`(H, \sigma(F), \sigma(T), (\sigma(p_c), \sigma(K_c)), h', \beta)`$ is a state. $`\sigma(F)`$ applies $`\sigma`$ to the columns and templates of each atom of $`F`$, and $`\sigma(T)`$ likewise.

**Proof.** Apply finite reflection to the diagram $`(G \cup F, N)`$ with $`\theta = \mathrm{eval}\,K_c\,h`$, cut $`p_c`$ and top $`\beta`$. The key condition of assumption 3 follows from $`K \lt K_c`$ and Theorem 1. That $`N`$ holds with top $`\beta`$ follows from the atoms of $`T`$, Theorem 1 and key weakening. Assumption 4 is item 6 of the state. Make $`h'`$ from the obtained $`g`$. By Theorem 3, $`h'`$ is strictly increasing, $`h' \lt \beta`$, and $`H`$ holds under $`h'`$. By $`h' \circ \sigma = h`$ and the relabelling equation, $`\sigma(F)`$, $`\sigma(T)`$ and the control atom mapped by $`\sigma`$ give the same relations as $`F`$, $`T`$ and the control atom, so they hold. $`\square`$

**Numbering of the splices.** This is used for an expansion $`s[n]`$ ($`s_{x_0} \gt 1`$, $`n \ge 1`$). For $`i = 0, 1, \ldots, n-1`$, the $`i`$-th splice is as follows.

- The current columns are $`0, \ldots, x_0 + i \cdot w - 1`$, so there are $`x_0 + i \cdot w`$ columns.
- The cut is $`c_r + i \cdot w`$. The shift map is $`\sigma_i(j) = j`$ ($`j \lt c_r + i \cdot w`$), $`\sigma_i(j) = j + w`$ ($`j \ge c_r + i \cdot w`$), and $`\sigma_i \circ \mu_i = \mu_{i+1}`$.
- The added columns are $`x_0 + i \cdot w, \ldots, x_0 + (i+1) \cdot w - 1`$, and the border column is $`x_0 + i \cdot w`$. In terms of the blocks of [05](05-omegay-mountain.md) §5.1, column $`x_0 + i \cdot w`$ is a column of block $`i`$ (the copy of $`x = x_0`$), and the rest are columns of block $`i + 1`$ (the copies of $`x = c_r + 1, \ldots, x_0 - 1`$).
- The reservoirs and the control atom are used as mapped by $`\mu_i`$: $`\mu_i(F)`$, $`\mu_i(T)`$, $`(c_r + i \cdot w, \mu_i(K_c))`$.

**Theorem 5 (iteration).** Let $`(G_0, F, T, (c_r, K_c), h_0, \beta)`$ be a state, where the columns of $`h_0`$ are $`0, \ldots, x_0 - 1`$. Assume that for each $`i \lt n`$ a list $`N_i`$ of top atoms and a list $`G_{i+1}`$ of internal atoms satisfy the assumptions of Theorem 4 for the reservoirs and control atom mapped by $`\mu_i`$. Then for every $`i \le n`$ there is a state $`(G_i, \mu_i(F), \mu_i(T), (c_r + i \cdot w, \mu_i(K_c)), h_i, \beta)`$. The columns of $`h_i`$ are $`0, \ldots, x_0 + i \cdot w - 1`$. $`\beta`$ does not change.

**Proof.** Induction on $`i`$ using Theorem 4. Since $`\sigma_i \circ \mu_i = \mu_{i+1}`$, the mapped reservoirs have the form required for the next round. $`\square`$

## 8. Classification and descent

Fix an atom system $`E`$. Let $`s`$ be a nonempty expression and $`n \ge 1`$ with $`s_{x_0} \gt 1`$. Let $`D`$ be a degree bound of $`M(s)`$.

- $`F`$: the atoms of $`E(M(s))`$ whose child column is smaller than $`x_0`$.
- $`T`$: the atoms $`(p, x_0, K)`$ of $`E(M(s))`$, read as top atoms $`(p, K)`$.
- Control: one atom $`(c_r, x_0, K_c)`$ of $`E(M(s))`$, read as the top atom $`(c_r, K_c)`$. Each system says which one.

**Definition (classification).** An atom $`(P, X, K)`$ of $`E(M(s[n]))`$ is **classified** if one of the following holds.

- **(base)** $`X \lt x_0`$ and $`E(M(s))`$ has an atom $`(P, X, K')`$ with $`K \le K'`$.
- When $`X \ge x_0`$, take the $`i`$ with $`x_0 + i \cdot w \le X \lt x_0 + (i+1) \cdot w`$.
- **(reservoir)** $`P \lt c_r`$ or $`P \ge x_0 + i \cdot w`$. Let $`P' = P`$ (if $`P \lt c_r`$) and $`P' = c_r + P - (x_0 + i \cdot w)`$ (if $`P \ge x_0 + i \cdot w`$). $`F`$ has an atom $`(P', c_r + X - (x_0 + i \cdot w), K')`$ with $`K \le \mu_{i+1}(K')`$.
- **(seam)** $`X = x_0 + i \cdot w`$ and $`K \lt \mu_i(K_c)`$. Moreover $`T`$ has an atom $`(\ell, x_0, K')`$ with $`\mu_i(\ell) = P`$ and $`K \le \mu_i(K')`$.

(reservoir) is type 2 of the classification in Theorem 4, and (seam) is type 3. Mapping the source atom $`(P', \ldots, K')`$ of (reservoir) by $`\mu_i`$ and then by $`\sigma_i`$ gives the columns $`(P, X)`$ and the template $`\mu_{i+1}(K')`$. For (seam), the top atom $`(P, K)`$ is put into $`N_i`$. It is covered by $`\mu_i(T)`$ and its key is smaller than $`\mu_i(K_c)`$.

**Theorem 6 (descent).** Let $`s`$ be a nonempty expression, $`n`$ a natural number and $`D`$ a degree bound of $`M(s)`$, and assume that $`s[n]`$ is defined. Assume further:

1. $`M(s[n])`$ can be built, and $`D`$ is also a degree bound of it.
2. If $`s_{x_0} \gt 1`$ and $`n \ge 1`$, then $`s[n]`$ has length $`x_0 + n \cdot w`$ and every atom of $`E(M(s[n]))`$ is classified.

Then from a representation $`f`$ of $`M(s)`$ with respect to $`E`$ one can make a representation $`f'`$ of $`M(s[n])`$ all of whose labels are smaller than $`f(x_0)`$.

**Proof.** If $`s_{x_0} = 1`$ or $`n = 0`$, then $`s[n]`$ is a prefix of $`s`$. By the prefix property of §4, restrict $`f`$ to the columns $`0, \ldots, x_0 - 1`$. Since $`f`$ is strictly increasing, every label is smaller than $`f(x_0)`$.

Otherwise let $`\beta = f(x_0)`$. Let $`G_i`$ be the atoms of $`E(M(s[n]))`$ whose child column is smaller than $`x_0 + i \cdot w`$, and $`N_i`$ the top atoms made from the (seam) atoms with $`X = x_0 + i \cdot w`$.

- State 0: $`h_0`$ is $`f`$ restricted to the columns $`0, \ldots, x_0 - 1`$. $`G_0`$ holds by (base) and key weakening. $`F`$ holds under $`f`$. $`T`$ and the control atom are atoms of $`E(M(s))`$ with child column $`x_0`$, so they hold with top $`\beta = f(x_0)`$. And $`h_0 \lt \beta`$.
- For each $`i`$, an atom of $`G_{i+1}`$ is an atom of $`G_i`$ if its child column is smaller than $`x_0 + i \cdot w`$, and otherwise it is classified by (reservoir) or (seam). So the assumptions of Theorem 5 hold.
- By Theorem 5 there is a state $`(G_n, \ldots, h_n, \beta)`$. $`G_n`$ is all of $`E(M(s[n]))`$, and $`h_n`$ has $`x_0 + n \cdot w`$ columns, the length of $`s[n]`$. Since $`h_n \lt \beta \lt \omega_1`$, $`h_n`$ is the required representation. $`\square`$

**Well-foundedness.** We apply the theorem of [02](02-well-founded.md) §6 as follows. Fix one $`D`$.

| General form | Here |
|---|---|
| states | finite sequences $`s`$ whose mountain can be built and has degree bound $`D`$ |
| one-step relation | $`t \prec s`$ ([05](05-omegay-mountain.md) §8) |
| labels | ordinals at most $`\omega_1`$ |
| $`\mathrm{valid}(s, \alpha)`$ | $`M(s)`$ has a representation with respect to $`E`$ all of whose labels are smaller than $`\alpha`$ |
| $`\alpha_0`$ | $`\omega_1`$ (the initial representation theorem applied to the diagram $`(E(M(s)), \emptyset)`$) |
| $`\alpha'`$ | the label $`f(x_0)`$ of the last column of the old representation |

If the assumptions of Theorem 6 hold for all $`s, n`$, then the set of states is closed under $`\prec`$, and the two conditions of the theorem of [02](02-well-founded.md) §6 hold. So $`\prec`$ is well-founded on this set. If there were an infinite sequence $`s_0 \succ s_1 \succ \cdots`$, then $`s_0`$ can be expanded, so its mountain can be built. Taking a degree bound $`D`$ of it, the whole sequence lies in this set, a contradiction. So $`\prec`$ is well-founded on the set of all finite sequences.

## 9. The edges of the mountain are not enough

With the edge system (§4), and with the control taken as the atom of the top edge of column $`x_0`$ (the edge whose upper node is $`t`$; its parent is the root $`r`$), the classification fails for the official ω-Y.

**Example ($`(1,3,3)[2]`$, computed with Python).** $`c_r = 0`$, $`w = 2`$, $`x_0 = 2`$. The edge $`(4,0) \to (4,1)`$ of output column 4 has as parent the node of column 3 at row 0 (the gap copy at row 1 in [05](05-omegay-mountain.md) §6.1). Its atom is $`(3, 4, (0, 0))`$.

- $`X = 4 = x_0 + 1 \cdot w`$, so $`i = 1`$ and this is the border column.
- $`P = 3`$ is neither smaller than $`c_r = 0`$ nor at least $`x_0 + i \cdot w = 4`$. It is not (reservoir).
- (seam) needs an atom of $`T`$ with $`\mu_1(\ell) = 3`$, that is $`\ell = 1`$: an atom from column 1 to column 2. But the parents of the edges of column 2 of $`M(1,3,3)`$ are all in column 0. $`T`$ is only $`(0, 2, (0, 0))`$ and $`(0, 2, (0, \top))`$.

**Test (Python).** Of the 1872 expansions of the expressions of length at most 5 with values at most 5 (except those with last term 1) with $`n = 1, 2, 3`$, the classification of the edge system fails on 328. For weak-magma ω-Y, Phyrion proved termination with this system.

## 10. Leg atoms

Instead of the edges of the mountain, we put one atom per node. Let $`M`$ be a mountain and $`D`$ a degree bound.

**Definition (leg, leg end).** The **leg** $`\ell(u)`$ of a node $`u`$ of column $`c \ge 1`$ is $`\mathrm{col}\,\pi(u)`$ (the column of the parent of the edge entering $`u`$ from below) if $`u`$ is not a bottom node, and $`c - 1`$ if $`u`$ is a bottom node. The **leg end** $`p_u`$ is the highest node of column $`\ell(u)`$ whose row is at most $`\mathrm{row}(u)`$. Column $`\ell(u)`$ has a node at row 0, so $`p_u`$ always exists.

**Definition (virtual key).** For nodes $`u`$ and $`p`$, let $`d = \mathrm{jump}(\mathrm{row}(u), \mathrm{row}(p))`$. The **virtual key** $`\kappa_D(u; p)`$ is the template of length $`D + 1`$ whose coordinate of scale $`k`$ is $`\mathrm{col}\,\rho_k(p)`$ if $`d \le k`$ and $`\top`$ otherwise. It is the edge key that an edge from $`u`$ with parent $`p`$ would have. To distinguish them from virtual keys, the edges that the mountain actually has are called **real edges**.

**Definition (leg atom).** $`\mathrm{at}(u) = (\ell(u),\ \mathrm{col}(u),\ \kappa_D(u; p_u))`$ is called the **leg atom** of $`u`$. The **leg atom system** $`E_D(M)`$ is the list of the leg atoms of all nodes of columns 1 and more. The control is $`\mathrm{at}(t) = (c_r, x_0, K_c)`$. The parent of the edge entering $`t`$ from below is the root $`r`$, so $`\ell(t) = c_r`$.

**Example 1 ($`(1,3,5)`$, $`D = 1`$, computed with Python).** The leg atoms of the nodes of column 2 are as follows.

| Node | Leg | Leg end | Jump | Key |
|---|---|---|---|---|
| $`(2, 0)`$ | 1 | $`(1, 0)`$ | 0 | $`(0, 0)`$ |
| $`(2, 1)`$ | 1 | $`(1, 1)`$ | 0 | $`(0, 1)`$ |
| $`(2, \omega)`$ | 0 | $`(0, 0)`$ | 2 | $`(\top, \top)`$ |

The coordinate of scale 0 in the key of $`(2, 1)`$ is 1. The edge from $`(1, 1)`$ upward has jump 1, so $`(1,1)`$ has no scale-0 parent and $`\rho_0((1,1)) = (1,1)`$.

**Example 2 ($`(1,3,4)[1] = (1,3,3)`$).** Column 2 of $`M(1,3,4)`$ is `0:4, 1:1←c1@0`, with $`c_r = 1`$ and $`w = 1`$. $`t = (2, 1)`$, $`\ell(t) = 1`$, $`p_t = (1, 1)`$ and the jump is 0, so $`K_c = (0, 1)`$. This is larger than the key $`(0, 0)`$ of the real edge $`(2,0) \to (2,1)`$.

Column 2 of the output $`(1,3,3)`$ is the border column $`x_0 + 0 \cdot w`$. The leg atom of its bottom node is $`(1, 2, (0, 0))`$. Since $`(0, 0) \lt \mu_0(K_c) = (0, 1)`$ and it is covered by $`\mathrm{at}(t) = (1, 2, (0, 1))`$ of $`T`$, it is classified by (seam). If the control were the real edge with $`(0, 0)`$, it would not be classified, since $`(0, 0) \lt (0, 0)`$ fails. A representation of $`(1,3,3)`$ needs a relation between columns 1 and 2. To make it by reflection from a representation of $`(1,3,4)`$, the control must be stronger than the real edge.

**Example 3 ($`(1,3,3)[2]`$).** $`K_c = (\top, \top)`$ ($`\mathrm{at}((2, \omega)) = (0, 2, (\top, \top))`$). The leg atom of $`(2, 0)`$ of $`M(1,3,3)`$ is $`(1, 2, (0, 0))`$, and it is in $`T`$. Mapped by $`\mu_1`$ it is $`(3, 4, (2, 2))`$. The output atom $`(3, 4, (0, 0))`$ of §9 (it is also the leg atom of the output node $`(4, 0)`$) is classified by (seam), since $`(0, 0) \le (2, 2)`$ and $`(0, 0) \lt (\top, \top)`$.

**Property (holds in the tested range).** The parent column of an edge $`(u, u^+)`$ is $`\ell(u^+)`$, and the edge key is at most the key of $`\mathrm{at}(u^+)`$. So a representation for $`E_D`$ is, by key weakening, also a representation for the edge system. We checked with Python that this holds for the 4073 edges of the mountains of the 624 expressions of length at most 5 with values at most 5. It is not proved here.

**Leg atoms of top nodes.** A top node $`u`$ has no edge upward. $`\mathrm{at}(u)`$ carries the key of the edge that would appear if there were one more node above $`u`$. If the leg end is low, the jump $`d`$ is large and many coordinates of the key are $`\top`$. For example, for the top node of column 2 of $`(1,3,3)`$ (row $`\omega`$), $`\mathrm{at}(u) = (0, 2, (\top, \top))`$. The control $`\mathrm{at}(t)`$ is also an atom of this kind.

## 11. The classification lemma

**Classification lemma.** For every nonempty expression $`s`$, every natural number $`n`$ and every degree bound $`D`$ of $`M(s)`$, if $`s[n]`$ is defined, the following hold.

1. The output mountain $`M(s[n])`$ can be built.
2. $`D`$ is also a degree bound of $`M(s[n])`$.
3. If $`s_{x_0} \gt 1`$ and $`n \ge 1`$, the length of $`s[n]`$ is $`x_0 + n \cdot w`$. Otherwise the length is $`x_0`$ (the last term is deleted).
4. Every atom of $`E_D(M(s[n]))`$ is classified in the sense of §8 with respect to $`E_D(M(s))`$ and the control $`\mathrm{at}(t)`$.

The proof is given in [10](10-official-descent.md). It is not proved here yet. This lemma is exactly the assumption of Theorem 6, so together with §8 it gives the final theorem of [05](05-omegay-mountain.md) §8.

**Test (Python).** On the 1872 expansions of the expressions of length at most 5 with values at most 5 (except those with last term 1) with $`n = 1, 2, 3`$, items 1 to 4 failed 0 times. The same holds with $`D`$ equal to the degree of $`M(s)`$ and with $`D`$ one larger.

## 12. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) introduction | the proof design: Phyrion's reflection theorem is used as it is, and the atoms of the representation are replaced by leg atoms |
| [README](../../README-en.md) "Status" | the final theorem (§8, §11) |
| [notes/00-survey.md](../../notes/00-survey.md) §3.2, §3.5 (Japanese) | keys, keys of the edges of the mountain, preservation of the degree bound, the shape of the combinatorial layer |
| [notes/01-feasibility.md](../../notes/01-feasibility.md) §3, §4 (Japanese) | the key bound for edges of the mountain fails for the official ω-Y |
| [notes/04-official-design.md](../../notes/04-official-design.md) §1–§4 (Japanese) | representation and classification (§1), the edges of the mountain are not enough (§2), the leg atom system (§3), numerical tests (§4) |
