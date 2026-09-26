[← Back](README.md) | [English](09-obligations.md) | [Japanese](../09-obligations.md)

# Proof of the three theorems

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | limit ordinals, $`\omega_1`$, regularity of $`\omega_1`$, labels, $`\{0, \ldots, n-1\}`$ |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded induction, keys, $`\top`$, top |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | height of a structure, $`\Sigma_1`$ formulas, parameters, witnesses, literals, $`\preccurlyeq_{\Sigma_1}`$, templates, evaluation $`\mathrm{eval}\ t\ v`$, monotonicity, internal relations $`\mathrm{Rel}_{t,i,j}`$, top predicates $`\mathrm{Top}_{t,i}`$, partial top predicates |
| [05 The official ω-Y sequence and its mountain](05-omegay-mountain.md) | the mountain $`M(s)`$, the degree bound $`D`$, $`s[n]`$, $`x_0`$, $`t`$, $`c_r`$, $`w`$, the final theorem |
| [06 The combinatorial layer and leg atoms](06-combinatorial-layer.md) | internal atoms, top atoms, diagrams, representations, the three theorems (key weakening, finite reflection, initial representation), cut, control relation, key evaluated at column numbers, new labels, splices, reservoirs $`F, T`$, states, the control atom and $`K_c`$, classification (base, reservoir, seam), the descent theorem, leg atoms $`\mathrm{at}(u)`$, the atom system $`E_D(M)`$, the classification lemma |
| [07 The relation R](07-relation-r.md) | structures $`\mathfrak A^c_\theta`$, the relation $`R`$, the defining equation, the proof of key weakening |
| [08 Closure below ω₁ and the sequence of Good points](08-closure-chain.md) | the ambient structure, Good, the sequence of Good points $`p_0 \lt p_1 \lt \cdots`$ |

This note shows that the relation $`R`$ of [07](07-relation-r.md) satisfies the three theorems of [06](06-combinatorial-layer.md) §5. The core is finite reflection (§2) and the initial representation (§3).

## 1. Overview

| Theorem ([06](06-combinatorial-layer.md) §5) | Proof |
|---|---|
| key weakening | [07](07-relation-r.md) §7 |
| finite reflection | §2 |
| initial representation | §3 (shown in §3.3 using §3.1 and §3.2) |

## 2. Finite reflection

**Notation.** We write the assumptions of finite reflection in [06](06-combinatorial-layer.md) §5 with the following notation.

- $`n`$ is the number of points of the diagram. The points are $`0, \ldots, n-1`$.
- $`f : \{0, \ldots, n-1\} \to \mathrm{Label}`$ is a strictly increasing labelling with $`f(j) \lt b`$ for every $`j`$. $`b`$ is the top.
- $`G`$ is a list of internal atoms. As in [06](06-combinatorial-layer.md) §2, an internal atom is written $`(i, j, K)`$ (points $`i \lt j`$, template $`K`$). Since $`t`$ is used for the top node of [05](05-omegay-mountain.md), this note writes templates as $`K`$, and writes the symbols $`\mathrm{Rel}_{t,i,j}`$, $`\mathrm{Top}_{t,i}`$ of [03](03-sigma1-elementary.md) §7 as $`\mathrm{Rel}_{K,i,j}`$, $`\mathrm{Top}_{K,i}`$. $`G`$ holds at $`f`$ when $`R(\mathrm{eval}\ K\ f, f(i), f(j))`$ holds for every $`(i, j, K)`$ in $`G`$.
- $`N`$ is a list of top atoms. A top atom is written $`(i, K)`$. Every key $`\mathrm{eval}\ K\ f`$ of $`N`$ is below $`\theta`$. $`N`$ holds for the top $`b`$, that is, $`R(\mathrm{eval}\ K\ f, f(i), b)`$ for every $`(i, K)`$ in $`N`$.
- $`\mathrm{cut}`$ is the cut, and the control relation $`R(\theta, f(\mathrm{cut}), b)`$ holds.

**The reflected formula.** Let the variables be $`v_0, \ldots, v_{n-1}`$. The positions $`j \lt \mathrm{cut}`$ are parameters, with values $`f(j)`$. The other positions are witness variables. The formula $`\varphi`$ is the conjunction of the following literals, preceded by $`\exists`$ over the witness variables.

```math
\varphi \;=\; \exists \vec v\ \Bigl[\ \bigwedge_{j \lt n-1} v_j \lt v_{j+1}\ \land \bigwedge_{(i,j,K) \in G} \mathrm{Rel}_{K,i,j}(\vec v)\ \land \bigwedge_{(i,K) \in N} \mathrm{Top}_{K,i}(\vec v)\ \Bigr]
```

Here $`\exists \vec v`$ binds only the witness variables. $`\mathrm{Rel}_{K,i,j}(\vec v)`$ is $`R(\mathrm{eval}\ K\ \vec v, v_i, v_j)`$. $`\mathrm{Top}_{K,i}(\vec v)`$ is, in a structure of height $`c`$, $`R(\mathrm{eval}\ K\ \vec v, v_i, c)`$. This is a $`\Sigma_1`$ formula ([03](03-sigma1-elementary.md) §2).

**Proof.**

1. By the defining equation ([07](07-relation-r.md) §6), $`f(\mathrm{cut}) \lt b`$ and $`\mathfrak A^{f(\mathrm{cut})}_\theta \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_\theta`$.
2. The parameters $`f(j)`$ ($`j \lt \mathrm{cut}`$) are below $`f(\mathrm{cut})`$, since $`f`$ is strictly increasing. So $`\varphi`$ can also be read in $`\mathfrak A^{f(\mathrm{cut})}_\theta`$.
3. At height $`b`$, $`\vec v = f`$ is a witness of $`\varphi`$.
   - Domain: $`f(j) \lt b`$ for every $`j`$.
   - Order literals: $`f`$ is strictly increasing.
   - $`\mathrm{Rel}`$ literals: $`G`$ holds at $`f`$.
   - $`\mathrm{Top}`$ literals: the key $`\mathrm{eval}\ K\ f`$ is below $`\theta`$, so the top predicate is defined, and $`N`$ holds for the top $`b`$.
4. By 1, $`\varphi`$ is also true in $`\mathfrak A^{f(\mathrm{cut})}_\theta`$. Let $`g`$ be the sequence made of its witness and the parameters.
5. $`g`$ satisfies the following.
   - By the order literals, $`g`$ is strictly increasing.
   - $`g(j) \lt f(\mathrm{cut})`$ for every $`j`$ (witnesses lie in the domain).
   - $`g(j) = f(j)`$ for $`j \lt \mathrm{cut}`$ (parameters).
   - By the $`\mathrm{Rel}`$ literals, $`G`$ holds at $`g`$.
   - The $`\mathrm{Top}`$ literals are true at height $`f(\mathrm{cut})`$. So their keys are below $`\theta`$ and $`R(\mathrm{eval}\ K\ g, g(i), f(\mathrm{cut}))`$ holds. That is, $`N`$ holds for the top $`f(\mathrm{cut})`$.
   - $`g \le f`$ pointwise: equal for $`j \lt \mathrm{cut}`$, and $`g(j) \lt f(\mathrm{cut}) \le f(j)`$ for $`j \ge \mathrm{cut}`$. $`\square`$

**Not used.** That $`b`$ is Good. That $`b`$ or $`f(\mathrm{cut})`$ is a limit ordinal.

**Example (shape only).** Look at the 0-th splice (which adds columns 2 and 3) of $`(1,3,3)[2] = (1,3,2,5,7,12)`$ in the iteration of [06](06-combinatorial-layer.md) §7. The lists of atoms were computed with Python (the leg atom system $`E_D(M)`$, $`D = 1`$). Templates are written with column numbers, and a key evaluated at $`f_j = f(j)`$ is written like $`(f_0, f_0)`$.

- $`x_0 = 2`$, $`c_r = 0`$, $`w = 2`$ and $`K_c = (\top, \top)`$.
- $`M(1,3,3)`$ has 6 leg atoms. Those whose child column is below $`x_0`$ (the reservoir $`F`$) are $`(0, 1, (0,0))`$, $`(0, 1, (0,\top))`$, $`(0, 1, (\top,\top))`$. Those whose child column is $`x_0`$ (the reservoir $`T`$) are $`(1, 2, (0,0))`$, $`(0, 2, (0,\top))`$, $`(0, 2, (\top,\top))`$. The last one is the control atom $`\mathrm{at}(t)`$.

This reflection takes the following data.

| Symbol | Value |
|---|---|
| points | columns 0, 1 (labels $`f_0 \lt f_1`$) |
| top $`b`$ | $`f_2`$ |
| cut | $`c_r = 0`$ (no parameters) |
| $`\theta`$ | $`(\top, \top)`$, the evaluation of $`K_c`$ |
| $`G`$ | the 3 atoms of column 1 |
| $`N`$ | the top atoms $`(1, (0,0))`$ and $`(0, (0,\top))`$, made from $`(1, 2, (0,0))`$ and $`(0, 2, (0,\top))`$ of $`T`$ |

The keys of $`N`$ are $`(f_0, f_0)`$ and $`(f_0, \top)`$, both below $`\theta = (\top, \top)`$. The control relation $`R((\top,\top), f_0, f_2)`$ says that $`\mathrm{at}(t)`$ holds at $`f`$. The reflected formula is below. $`\mathrm{Top}[\kappa](x)`$ says that the top predicate with key $`\kappa`$ holds at the point $`x`$, that is, $`R(\kappa, x, c)`$ at height $`c`$ (the value of the key is written instead of the template).

```math
\exists v_0\ \exists v_1\ \bigl[\ v_0 \lt v_1 \land R((v_0,v_0), v_0, v_1) \land R((v_0,\top), v_0, v_1) \land R((\top,\top), v_0, v_1) \land \mathrm{Top}[(v_0,v_0)](v_1) \land \mathrm{Top}[(v_0,\top)](v_0)\ \bigr]
```

- At height $`f_2`$, $`(v_0, v_1) = (f_0, f_1)`$ is a witness. The $`\mathrm{Top}`$ literals are $`R((f_0,f_0), f_1, f_2)`$ and $`R((f_0,\top), f_0, f_2)`$, that is, the atoms of $`T`$ hold at $`f`$.
- Reflection gives $`g_0 \lt g_1 \lt f_0`$ that satisfy the same formula at height $`f_0`$. The $`\mathrm{Top}`$ literals become $`R((g_0,g_0), g_1, f_0)`$ and $`R((g_0,\top), g_0, f_0)`$.
- The new labels are $`(g_0, g_1, f_0, f_1)`$. All of them are below $`f_2`$.

The leg atoms of columns 1–3 of the output hold at the new labels as follows (the atoms and their classification were computed with Python).

| Atom | Classification | Why it holds |
|---|---|---|
| the 3 of column 1 | base | $`G`$ holds at $`g`$ |
| $`(1, 2, (0,0))`$ | seam | $`R((g_0,g_0), g_1, f_0)`$ (a top literal obtained by reflection) |
| $`(0, 2, (0,\top))`$ | seam | $`R((g_0,\top), g_0, f_0)`$ (same) |
| $`(2, 3, (0,0))`$ | reservoir | $`R((f_0,f_0), f_0, f_1)`$ from $`(0,1,(0,0))`$ of $`F`$, then key weakening since $`(g_0,g_0) \le (f_0,f_0)`$ |
| $`(2, 3, (2,2))`$ | reservoir | $`R((f_0,f_0), f_0, f_1)`$ |
| $`(2, 3, (2,\top))`$ | reservoir | $`R((f_0,\top), f_0, f_1)`$ from $`(0,1,(0,\top))`$ of $`F`$ |
| $`(2, 3, (\top,\top))`$ | reservoir | $`R((\top,\top), f_0, f_1)`$ from $`(0,1,(\top,\top))`$ of $`F`$ |

In the next splice, the 1st (which adds columns 4 and 5), the cut is $`c_r + w = 2`$ (label $`f_0`$), and the labels $`g_0, g_1`$ of columns 0, 1 are parameters. Reflection gives $`g_1 \lt g'_2 \lt g'_3 \lt f_0`$, and the new labels are $`(g_0, g_1, g'_2, g'_3, f_0, f_1)`$. This is a representation of $`(1,3,2,5,7,12)`$, and every label is below $`f_2`$. The concrete values of the labels are unknown. Only the shape is shown here.

## 3. The initial representation

As in [08](08-closure-chain.md) §1, the ambient structure (the structure of height $`\omega_1`$ with the top predicates defined at every key) is written $`\mathfrak B`$. Its top predicates are $`R(\mathrm{eval}\ K\ \vec v, v_i, \omega_1)`$. $`\mathrm{Good}(\alpha)`$ says: if a $`\Sigma_1`$ formula with parameters below $`\alpha`$ is true in $`\mathfrak B`$, it has a witness below $`\alpha`$.

### 3.1 Absoluteness of the top predicates

**Lemma 1.** Let $`\alpha`$ be a label with $`\mathrm{Good}(\alpha)`$ and $`\alpha \lt \omega_1`$. For a key $`\kappa`$, assume: for every key $`\kappa' \lt \kappa`$ and label $`x \lt \alpha`$, $`R(\kappa', x, \alpha) \iff R(\kappa', x, \omega_1)`$. Then for every $`\Sigma_1`$ formula $`\varphi`$ with parameters $`\vec y`$ below $`\alpha`$:

```math
\mathfrak A^{\alpha}_{\kappa} \models \varphi(\vec y) \iff \mathfrak A^{\omega_1}_{\kappa} \models \varphi(\vec y)
```

**Proof.** The two structures have the same order and the same internal relations. Only the top predicates differ. The top predicates of $`\mathfrak A^{\alpha}_{\kappa}`$ are $`R(\kappa', x, \alpha)`$, and those of $`\mathfrak A^{\omega_1}_{\kappa}`$ are $`R(\kappa', x, \omega_1)`$. Both are defined only at keys $`\kappa' \lt \kappa`$.

- From height $`\alpha`$ to height $`\omega_1`$: the witness $`\vec w`$ is below $`\alpha`$, hence below $`\omega_1`$. The $`\mathrm{Top}`$ literals are read at keys $`\kappa' \lt \kappa`$ and points $`w_i \lt \alpha`$, so by the assumption they have the same truth values.
- From height $`\omega_1`$ to height $`\alpha`$: take a witness $`\vec v \lt \omega_1`$.
  1. Every true literal is also true in $`\mathfrak B`$. A true $`\mathrm{Top}`$ literal is defined (key $`\lt \kappa`$) and reads the same $`R(\cdot, \cdot, \omega_1)`$ as $`\mathfrak B`$. So $`\vec v`$ is a witness of $`\varphi`$ in $`\mathfrak B`$.
  2. Make the formula $`\varphi'`$ in which the positions $`j`$ with $`v_j \lt \alpha`$ are parameters too. All parameters are below $`\alpha`$. By $`\mathrm{Good}(\alpha)`$, $`\varphi'`$ has a witness $`\vec w`$ in $`\mathfrak B`$ below $`\alpha`$.
  3. $`\vec w \le \vec v`$ pointwise. At parameter positions they are equal. At the other positions $`w_j \lt \alpha \le v_j`$.
  4. By monotonicity ([03](03-sigma1-elementary.md) §7), $`\mathrm{eval}\ K\ \vec w \le \mathrm{eval}\ K\ \vec v \lt \kappa`$. So the $`\mathrm{Top}`$ literals at $`\vec w`$ also have keys below $`\kappa`$, and are defined and true in $`\mathfrak A^{\omega_1}_{\kappa}`$ ([03](03-sigma1-elementary.md) §8).
  5. The points are $`w_i \lt \alpha`$ and the keys are $`\lt \kappa`$, so by the assumption the $`\mathrm{Top}`$ literals can be replaced by those of height $`\alpha`$. So $`\vec w`$ is a witness in $`\mathfrak A^{\alpha}_{\kappa}`$. $`\square`$

**Theorem 2 (absoluteness of the top predicates).** Let $`\alpha`$ be a label with $`\mathrm{Good}(\alpha)`$ and $`\alpha \lt \omega_1`$. For every key $`\kappa`$ and label $`x \lt \alpha`$:

```math
R(\kappa, x, \alpha) \iff R(\kappa, x, \omega_1)
```

**Proof.** Well-founded induction on $`\kappa`$ ([02](02-well-founded.md) §2). The order of keys is well-founded ([02](02-well-founded.md) §3). Assume the theorem for keys below $`\kappa`$. Unfold both sides with the defining equation ([07](07-relation-r.md) §6).

```math
R(\kappa, x, \alpha) \iff x \lt \alpha \land \mathfrak A^{x}_{\kappa} \preccurlyeq_{\Sigma_1} \mathfrak A^{\alpha}_{\kappa}, \qquad R(\kappa, x, \omega_1) \iff x \lt \omega_1 \land \mathfrak A^{x}_{\kappa} \preccurlyeq_{\Sigma_1} \mathfrak A^{\omega_1}_{\kappa}
```

Both $`x \lt \alpha`$ and $`x \lt \omega_1`$ are true. The right conjuncts compare, for formulas with parameters below $`x`$, the truth value in $`\mathfrak A^{x}_{\kappa}`$ with that in $`\mathfrak A^{\alpha}_{\kappa}`$ or in $`\mathfrak A^{\omega_1}_{\kappa}`$. By the induction hypothesis Lemma 1 applies, so the truth values in $`\mathfrak A^{\alpha}_{\kappa}`$ and $`\mathfrak A^{\omega_1}_{\kappa}`$ are the same (the parameters are below $`x \lt \alpha`$). So the right conjuncts are equivalent too. $`\square`$

**Corollary 3.** If $`\mathrm{Good}(\alpha)`$ and $`\alpha \lt \omega_1`$, then for every key $`\kappa`$ and every $`\Sigma_1`$ formula $`\varphi`$ with parameters below $`\alpha`$, $`\mathfrak A^{\alpha}_{\kappa} \models \varphi \iff \mathfrak A^{\omega_1}_{\kappa} \models \varphi`$.

**Proof.** By Theorem 2, the assumption of Lemma 1 holds for every $`\kappa`$. $`\square`$

### 3.2 Good points are in the relation R

**Theorem 4.** Let $`\alpha, \beta`$ be labels with $`\mathrm{Good}(\alpha)`$, $`\mathrm{Good}(\beta)`$ and $`\alpha \lt \beta \lt \omega_1`$. Then $`R(\kappa, \alpha, \beta)`$ for every key $`\kappa`$.

**Proof.** By the defining equation. $`\alpha \lt \beta`$ holds. For a formula $`\psi`$ at key $`\kappa`$ with parameters below $`\alpha`$, use Corollary 3 at $`\alpha`$ and at $`\beta`$ (the parameters are also below $`\beta`$).

```math
\mathfrak A^{\alpha}_{\kappa} \models \psi \iff \mathfrak A^{\omega_1}_{\kappa} \models \psi \iff \mathfrak A^{\beta}_{\kappa} \models \psi
```

So $`\mathfrak A^{\alpha}_{\kappa} \preccurlyeq_{\Sigma_1} \mathfrak A^{\beta}_{\kappa}`$. $`\square`$

The key $`\kappa`$ is arbitrary. Good points are related at every key.

### 3.3 Every finite diagram has a representation

**Theorem 5 (initial representation).** For every diagram $`(G, N)`$ there are a label $`\beta \lt \omega_1`$ and a strictly increasing labelling $`f`$ ($`f \lt \beta`$ at every point) such that $`G`$ holds at $`f`$ and $`N`$ holds for the top $`\beta`$.

**Proof.** Let $`n`$ be the number of points of the diagram. Using the sequence of Good points ([08](08-closure-chain.md) §7), put $`\beta := p_n`$ and $`f(j) := p_j`$.

- $`p_0 \lt p_1 \lt \cdots \lt p_n \lt \omega_1`$, so $`f`$ is strictly increasing and $`f \lt \beta \lt \omega_1`$.
- An internal atom $`(i, j, K)`$ has $`i \lt j`$, so Theorem 4 gives $`R(\mathrm{eval}\ K\ f, p_i, p_j)`$.
- A top atom $`(i, K)`$ has $`i \lt n`$, so Theorem 4 gives $`R(\mathrm{eval}\ K\ f, p_i, p_n)`$. $`\square`$

One sequence $`p_0 \lt p_1 \lt \cdots`$ represents all diagrams at once. No condition on keys is needed.

**Representations of mountains.** The leg atom system $`E_D(M)`$ of a mountain $`M`$ ([06](06-combinatorial-layer.md) §10) is a finite list of atoms $`(p, c, K)`$ with $`p \lt c`$. Take it as the list $`G`$ of internal atoms, let $`N`$ be empty, and apply Theorem 5. The resulting $`f`$ is a representation of $`M`$ in the sense of [06](06-combinatorial-layer.md) §4. So every mountain has a representation.

**Example.** The mountain of $`(1,3,3)`$ ($`D = 1`$) has the 6 leg atoms of the example of §2 (computed with Python). With $`f = (p_0, p_1, p_2)`$, the relations that must hold are the following 6, and all hold by Theorem 4.

```math
R((p_0,p_0), p_0, p_1),\ R((p_0,\top), p_0, p_1),\ R((\top,\top), p_0, p_1),\ R((p_0,p_0), p_1, p_2),\ R((p_0,\top), p_0, p_2),\ R((\top,\top), p_0, p_2)
```

### 3.4 Initial representation with a control

**Theorem 6 (initial representation with a control).** Take a diagram $`(G, N)`$ and one top atom $`(q, K_c)`$, called the control atom. Assume that for every atom $`(i, K)`$ of $`N`$, the key evaluated at column numbers ([06](06-combinatorial-layer.md) §1) of $`K`$ is below that of $`K_c`$. Then there are a label $`\beta \lt \omega_1`$ and a strictly increasing labelling $`f \lt \beta`$ such that:

1. $`G`$ holds at $`f`$, and $`N`$ holds for the top $`\beta`$;
2. every key of $`N`$ is below $`\mathrm{eval}\ K_c\ f`$;
3. the control relation $`R(\mathrm{eval}\ K_c\ f, f(q), \beta)`$ holds.

**Proof.** Apply Theorem 5 to the diagram obtained by adding $`(q, K_c)`$ to $`N`$. Items 1 and 3 follow. Item 2 follows because $`f`$ is strictly increasing and, when the key evaluated at column numbers is smaller, the key evaluated at $`f`$ is smaller too ([06](06-combinatorial-layer.md) §1). $`\square`$

The descent of [06](06-combinatorial-layer.md) §8 does not use Theorem 6. The first state of the iteration (the state for $`i = 0`$ in Theorem 5 of [06](06-combinatorial-layer.md) §7) is built directly from the representation $`f`$ of $`s`$: the reservoir $`F`$, the reservoir $`T`$ and the control atom $`\mathrm{at}(t)`$ are all atoms of $`E_D(M(s))`$, and with the top $`\beta = f(x_0)`$ they all hold at $`f`$.

## 4. Summary

- The semantic layer (the relation $`R`$ of [07](07-relation-r.md)) satisfies the three theorems of [06](06-combinatorial-layer.md) §5. Key weakening is [07](07-relation-r.md) §7, finite reflection is §2, and the initial representation is Theorem 5 of §3.3.
- The descent theorem of [06](06-combinatorial-layer.md) §8 follows from these three theorems and the classification. The classification is proved in [10](10-official-descent.md) in the form of the classification lemma of [06](06-combinatorial-layer.md) §11. This gives the final theorem of [05](05-omegay-mountain.md) §8.
- **Strength.** The proof is carried out in ordinary set theory with the axiom of choice, and uses the regularity of $`\omega_1`$. The labels are Good points below $`\omega_1`$ whose concrete values are unknown. So no ordinal bound comes out of this proof, and no ordinal notation system (a way to write ordinals as finite strings of symbols) is obtained.

## 5. Where this repository uses it

| Place | Use |
|---|---|
| the opening of the [README](../../README-en.md) | Phyrion's reflection theorem is used as it is |
| [README](../../README-en.md) "Status" | the final theorem and the axioms it uses |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §1 (Japanese) | the three theorems the combinatorial layer uses from the semantic layer |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §3.2, §3.3 (Japanese) | finite reflection (§2), absoluteness of top predicates and the relation between Good points (§3) |
| [notes/04-official-design.md](../../notes/04-official-design.md) §1.1, §1.2 (Japanese) | the initial representation and the descent by reflection |
