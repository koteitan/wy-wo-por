[← Back](README.md) | [English](04-patterns-of-resemblance.md) | [Japanese](../04-patterns-of-resemblance.md)

# Patterns of resemblance

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, successor ordinal, limit ordinal, label, position |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded recursion, keys $`\mathrm{Key}_m`$, $`\top`$, coordinate, stage, top, termination by a bound on labels |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | structure $`(\gamma; \ldots)`$, domain, height, point, atomic formula, $`\Sigma_1`$ formula, parameter, witness, literal, $`\Sigma_1`$-elementary substructure $`\preccurlyeq_{\Sigma_1}`$, template, evaluation $`\mathrm{eval}\ t\ \vec v`$, monotonicity, internal relation, top predicate, partial top predicates |

This note explains the idea of Carlson's patterns of resemblance. Next it describes how [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) used it for BMS (the Bashicu matrix system, a system of sequences that expands matrices). Finally it says why it is not enough as it stands for ω-Y, and what this repository changes.

## 1. A relation that has itself in its language

**Definition (Carlson's ≤₁).** Define the relation $`\le_1`$ on ordinals, for ordinals $`\alpha, \beta`$, by the formula below. The structures on the right are written as in [03](03-sigma1-elementary.md) §1, and the language is $`\{\le, \le_1\}`$.

```math
\alpha \le_1 \beta \iff \alpha \le \beta \ \land\ (\alpha; \le, \le_1) \preccurlyeq_{\Sigma_1} (\beta; \le, \le_1)
```

$`\alpha \lt_1 \beta`$ means $`\alpha \lt \beta \land \alpha \le_1 \beta`$.

**Reading.** "The shape of the ordinals below $`\alpha`$ cannot be distinguished by $`\Sigma_1`$ formulas from its extension up to $`\beta`$." Here the shape consists of the order and the relation $`\le_1`$ itself.

The right side uses the $`\le_1`$ of the left side. It looks circular, but it can be defined by well-founded recursion on $`\beta`$.

- The domain of $`(\beta; \le, \le_1)`$ is $`\{x \mid x \lt \beta\}`$. The only instances of $`\le_1`$ read there are $`x \le_1 y`$ with $`x, y \lt \beta`$.
- Since $`y \lt \beta`$, the truth of $`x \le_1 y`$ is already fixed earlier in the recursion, before $`\beta`$.
- The same holds for $`(\alpha; \ldots)`$, and $`\alpha \le \beta`$.

Carlson studied the structures that extend this to $`\le_1, \ldots, \le_N`$ ($`\Sigma_1`$- to $`\Sigma_N`$-elementarity).

```math
\mathcal R_N = (\mathrm{Ord}; \le, \le_1, \ldots, \le_N)
```

$`\mathrm{Ord}`$ is the class of all ordinals. $`N`$ is a positive integer.

Reference: T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77.

## 2. Small examples

The three examples below were found by hand, by following the definitions.

**Example 1.** For a natural number $`n \lt \beta`$, $`n \le_1 \beta`$ fails.

- If $`n \ge 1`$: with parameter $`n - 1`$, $`\exists x\ (n - 1 \lt x)`$ is true in $`\beta`$ ($`x = n`$) and false in $`n`$.
- If $`n = 0`$: $`\exists x\ (x \le x)`$ is true in $`\beta`$ and false in the empty structure $`0`$.

For the same reason, a successor ordinal $`\gamma + 1`$ is not in the relation $`\le_1`$ with any larger ordinal. Use $`\exists x\ (\gamma \lt x)`$ with parameter $`\gamma`$.

**Example 2.** $`\omega \lt_1 \omega + 1`$.

By Example 1, no two distinct points below $`\omega + 1`$ are in the relation $`\le_1`$: pairs of natural numbers by Example 1, and the only other point is $`\omega`$ itself. So in $`(\omega; \le, \le_1)`$ and $`(\omega + 1; \le, \le_1)`$, $`x \le_1 y`$ is the same as $`x = y`$. Then we compare the order-only structures $`(\omega; \le)`$ and $`(\omega + 1; \le)`$, and since $`\omega`$ is a limit ordinal, the example of [03](03-sigma1-elementary.md) §5 applies.

**Example 3.** If $`\beta \ge \omega + 2`$, then $`\omega \le_1 \beta`$ fails. $`\exists x\ \exists y\ (x \lt y \land x \le_1 y)`$ is true in $`\beta`$ (the $`x = \omega`$, $`y = \omega + 1`$ of Example 2 are both below $`\beta`$) and false in $`\omega`$ (Example 1).

$`\omega \le_1 \omega`$ holds by definition. So $`\{\beta \mid \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$.

In the order-only language, $`(\omega; \le) \preccurlyeq_{\Sigma_1} (\beta; \le)`$ held for every $`\beta \gt \omega`$. Putting $`\le_1`$ itself into the language made the relation finer.

## 3. Use in termination proofs

An expansion in a system of sequences is an operation that makes a new sequence from a sequence. A termination proof of an expansion puts an ordinal label ([01](01-ordinals.md) §6) on each entry of the sequence and shows that the labels decrease under expansion (termination by a bound on labels, [02](02-well-founded.md) §6). The property needed there is **finite reflection**.

**The shape of finite reflection.** Let $`\alpha \lt_1 \beta`$. Suppose points $`\vec p`$ below $`\alpha`$ and points $`\vec y`$ below $`\beta`$ satisfy finitely many atomic conditions $`\psi(\vec p, \vec y)`$. Then there are points $`\vec y'`$ below $`\alpha`$ with $`\psi(\vec p, \vec y')`$.

**Reason.** $`\exists \vec y\ \psi(\vec p, \vec y)`$ is a $`\Sigma_1`$ formula true in $`(\beta; \ldots)`$. By $`\Sigma_1`$-elementarity it is true in $`(\alpha; \ldots)`$. Take its witness as $`\vec y'`$.

In an expansion this is used as follows.

- Choose one entry, and let $`\alpha`$ be the old label of that entry.
- Let $`\vec p`$ be the old labels of the entries before the chosen one. The reflection does not move these labels.
- Let $`\vec y`$ be the old labels of the entries that get new labels. The $`\vec y`$ are all at least $`\alpha`$.
- $`\psi`$ states relations between the labels of entries, for example that the labels of two columns that are parent and child in a BMS matrix satisfy $`\le_1`$ and so on.

The new labels $`\vec y'`$ given by finite reflection satisfy the same relations, and they are all below $`\alpha`$. So the new labels are smaller than the old ones.

**Use in bms-elem-pattern.** [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) proved termination of BMS with $`\mathcal R_N`$. The labels of two columns that are parent and child in row $`k`$ of a BMS matrix are made to satisfy $`\lt_{k+1}`$ ($`\lt_{k+1}`$ means $`\lt`$ and $`\le_{k+1}`$). Finite reflection uses continuity and cofinality lemmas for each $`\le_n`$. The definition and examples of $`\mathcal R_N`$ are in the note [proof/pss/03-patterns.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/pss/03-patterns.md) of that repository.

## 4. What is missing for ω-Y

The label relation required by the combinatorial layer of ω-Y (the part of Phyrion's proof that deals only with the combinatorial shape of the expansion of sequences, explained in [06](06-combinatorial-layer.md)) has three arguments.

```math
R(\theta, a, b) \quad (\theta \in \mathrm{Key}_m,\ a, b \in \mathrm{Label})
```

$`\theta`$ is a key, and $`a, b`$ are labels. $`m`$ is the key length. The key $`\theta`$ is a sequence of $`m`$ entries, each a label or $`\top`$ ([02](02-well-founded.md) §3). The third argument $`b`$ is the top ([02](02-well-founded.md) §3). In this repository $`R(\theta, a, b)`$ is read as follows: "in the language whose top predicates are defined only where the key is below $`\theta`$ (§5), the structure of height $`a`$ is a $`\Sigma_1`$-elementary substructure of the structure of height $`b`$". The definition is given in [07](07-relation-r.md). This reading causes three problems.

**Problem 1: keys are transfinite.** Keys range over $`\mathrm{Key}_m`$ in lexicographic order. The coordinates are labels, so the order of keys is transfinite. The $`j = 1, \ldots, N`$ of $`\le_j`$ in $`\mathcal R_N`$ ($`\Sigma_1`$- to $`\Sigma_N`$-elementarity) are finitely many and counted by natural numbers. A key cannot be used as such a number.

**Problem 2: conditions toward the top.** Finite reflection must also make the relation $`R(\kappa, x, b)`$ ($`\kappa`$ a key) from a point $`x`$ to the top $`b`$ true for the new labels.

**Definition (demand).** A condition $`R(\kappa, x, b)`$ from a point $`x`$ to the top $`b`$ is called a **demand**.

$`b`$ is not an element of the structure $`(b; \ldots)`$. Writing a demand by unfolding the definition of $`R`$ does not give a $`\Sigma_1`$ formula.

**Problem 3: the key of a demand may name points that the reflection moves.** Let $`f(i)`$ be the label of entry $`i`$ of the sequence. A demand has the form $`R(\mathrm{eval}\ t\ f, f(p), b)`$, where $`p`$ is the number of an entry and $`t`$ a template ([03](03-sigma1-elementary.md) §7). The template decides which entry's label is put at each coordinate of the key. We say that "the template names the entry". Phyrion's finite reflection theorem ([Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)) does not require the entries named by a key to be points that the reflection does not move. So a label inside a key may belong to a witness ([03](03-sigma1-elementary.md) §2) that the reflection relabels. When the witness is relabelled, the value of the key changes too. The 1-Y version ([koteitan/1y-wo-por study/](https://github.com/koteitan/1y-wo-por/tree/main/study)) decided whether a top predicate is defined only by the positions of the variables. That method does not work here.

## 5. The changes made in this repository

As in [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §2 (Japanese), the following changes are made.

1. **Every key gives $`\Sigma_1`$-elementarity.** The difference in strength between keys is not the quantifier complexity but which top predicates are defined.
2. **Top predicates are atomic symbols.** A structure of height $`c`$ has a symbol $`\mathrm{Top}_{t,i}`$ ([03](03-sigma1-elementary.md) §7) for each template $`t`$ and position $`i`$, interpreted as "$`R(\mathrm{eval}\ t\ \vec v, v_i, c)`$". Demands become atomic formulas (Problem 2).
3. **Top predicates are defined only where the key is below $`\theta`$.** Where they are not defined, top literals are false ([03](03-sigma1-elementary.md) §8). Whether they are defined depends on the value of the key (Problem 3). Lowering witnesses pointwise keeps the key below $`\theta`$, by the monotonicity of $`\mathrm{eval}`$ ([03](03-sigma1-elementary.md) §8).
4. **Internal relations exist for every key.** For each template $`t`$ and positions $`i, j`$ there is a symbol $`\mathrm{Rel}_{t,i,j}`$ ([03](03-sigma1-elementary.md) §7), interpreted as $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v, v_i, v_j)`$.
5. **The stages are (top, key).** The top $`b`$ is the outermost component ([02](02-well-founded.md) §3). The right side at the stage of key $`\theta`$ reads only top predicates of keys below $`\theta`$. This is exactly the "defined range" of item 3 (Problem 1).

The resulting relation $`R`$ is not Carlson's $`\mathcal R_N`$ itself. We do not claim that it is the same as $`\mathcal R_N`$. The definition is given in [07 The relation R](07-relation-r.md).

| | $`\mathcal R_N`$ (bms-elem-pattern) | 1-Y version (1y-wo-por) | Phyrion's original semantic layer for ω-Y | this repository |
|---|---|---|---|---|
| argument that distinguishes the relations | $`j = 1, \ldots, N`$ | $`(k, \eta) \in \mathbb N \times \mathrm{Ord}`$ | keys $`\theta \in \mathrm{Key}_m`$ | keys $`\theta \in \mathrm{Key}_m`$ |
| content of $`R(\cdot, a, b)`$ | $`\Sigma_j`$-elementarity | $`\Sigma_1`$-elementarity | sets of conditions below $`b`$ can be shrunk below $`a`$ | $`\Sigma_1`$-elementarity |
| relation to the top | continuity and cofinality lemmas | atomic symbols (whether defined is decided by the positions of variables) | demands inside the sets of conditions | partial atomic symbols (defined by the value of the key) |
| recursion | top $`\beta`$ | (top, $`k`$, $`\eta`$) | (top, key) | (top, key) |

The terms of the table are as follows ([notes/00-survey.md](../../notes/00-survey.md) §3.1, §3.2 (Japanese)).

- $`(k, \eta)`$ of the 1-Y version: $`k`$ is a natural number, the number of a layer, and $`\eta`$ is a root label (in the 1-Y version, the label of the root column of that layer).
- Phyrion's set of conditions: a set of conditions between finitely many points. It consists of finitely many conditions of the relation $`R`$ between points and finitely many demands from points to the top. No condition contains a negation.
- "Sets of conditions below $`b`$ can be shrunk below $`a`$": suppose a strictly increasing labelling below $`b`$ makes the relations between the points of the set true, and makes the demands (with keys below $`\theta`$) true for the top $`b`$. Then there is a strictly increasing labelling below $`a`$ that makes the same relations true and the demands true for the top $`a`$. The original labels below $`a`$ are not moved.

Phyrion's original semantic layer is summarized in [notes/00-survey.md](../../notes/00-survey.md) §3.2 (Japanese). It is not included in this repository ([NOTICE](../../NOTICE)).

## 6. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) introduction | Phyrion's reflection theorem is used as it is. Reference to the re-proof of weak-magma ω-Y by patterns of resemblance (koteitan/wmwy-wo-por) |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §0, §2 (Japanese) | summary of the design, and the definitions of the structures, formulas and the relation |
| [notes/00-survey.md](../../notes/00-survey.md) §3.1–§3.4 (Japanese) | the shape for 1-Y, Phyrion's original relation, and the problems in extending the 1-Y method |
