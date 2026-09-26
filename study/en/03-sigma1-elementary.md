[← Back](README.md) | [English](03-sigma1-elementary.md) | [Japanese](../03-sigma1-elementary.md)

# Structures and Σ₁-elementary substructures

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, limit ordinal, $`\{x \mid x \lt \gamma\}`$, label, $`\{0, \ldots, n-1\}`$, position |
| [02 Well-founded relations and recursion](02-well-founded.md) | keys $`\mathrm{Key}_m`$ and their order, $`\top`$, coordinate, top |

This note explains the model-theoretic terms used in the definition of the relation $`R`$ ([07](07-relation-r.md)): first-order structures, $`\Sigma_1`$ formulas, $`\Sigma_1`$-elementary substructures and the Tarski–Vaught test. §7 and §8 explain the language used in this repository and the way two structures are compared.

## 1. Languages and structures

**Definition (language).** A **language** is a collection of relation symbols, each with a fixed number of arguments. This repository uses no function symbols and no constant symbols.

**Definition (structure).** A **structure** $`\mathfrak A`$ for a language $`L`$ consists of a set $`A`$ (the domain, possibly empty) and an interpretation $`P^{\mathfrak A} \subseteq A^n`$ of each symbol $`P`$ with $`n`$ arguments.

**Notation.** We write a structure as $`(A; P_1, \ldots, P_k)`$.

- Left of the semicolon, $`A`$ is the domain.
- Right of the semicolon are the interpretations of the symbols, in the order of the language. A symbol and its interpretation are written with the same letter.
- When an ordinal $`\gamma`$ stands on the left, the domain is $`\{x \mid x \lt \gamma\}`$.
- The relations on the right are restricted to the domain. For example, the $`\le`$ of $`(\gamma; \le)`$ is $`\{(x, y) \mid x, y \lt \gamma,\ x \le y\}`$.

Example: $`(4; \lt)`$ has domain $`\{0, 1, 2, 3\}`$, and its relation is $`\lt`$ on $`\{0, 1, 2, 3\}`$.

| Language | Structure | Domain |
|---|---|---|
| $`\{\lt\}`$ | $`(\omega; \lt)`$ | natural numbers |
| $`\{\lt\}`$ | $`(\gamma; \lt)`$ | $`\{x \mid x \lt \gamma\}`$ |
| $`\{\lt, E\}`$ ($`E`$ a symbol with 2 arguments) | $`(\omega; \lt, E)`$, $`E(x, y) :\iff y = x + 1`$ | natural numbers |

Every structure in this repository has a domain of the form $`\{x \mid x \lt \gamma\}`$. We call $`\gamma`$ the **height** of the structure. The elements of the domain are called **points**.

## 2. Formulas and Σ₁ formulas

**Definition (formula).** Formulas are built as follows.

- **Atomic formulas**: $`P(x_1, \ldots, x_n)`$ ($`P`$ a symbol with $`n`$ arguments, $`x_i`$ variables).
- Formulas joined by $`\neg, \land, \lor, \to`$.
- A formula with $`\exists x`$ or $`\forall x`$ in front.

**Definition (quantifier-free formula).** A formula that contains no quantifier $`\exists`$ or $`\forall`$.

**Definition (Σ₁ formula).** A formula of the form

```math
\exists y_1 \cdots \exists y_k\ \psi(\vec p, y_1, \ldots, y_k)
```

with $`\psi`$ quantifier-free, that is, with only existential quantifiers in front, is a **$`\Sigma_1`$ formula**. $`k`$ is a natural number. A letter with an arrow, such as $`\vec p`$ or $`\vec y`$, stands for a finite tuple of variables (or elements). $`\vec p`$ is a tuple of free variables, into which elements of the domain are put later. The elements put there are called **parameters**.

| Formula | Kind |
|---|---|
| $`p \lt q`$ | quantifier-free (also $`\Sigma_1`$, with $`k = 0`$) |
| $`\exists y\ (p \lt y)`$ | $`\Sigma_1`$ |
| $`\exists y\ \exists z\ (p \lt y \land y \lt z \land E(y, z))`$ | $`\Sigma_1`$ |
| $`\forall y\ (y \lt p \lor p \lt y \lor y = p)`$ | not $`\Sigma_1`$ |

**Definition (satisfaction).** For a structure $`\mathfrak A`$ and a tuple of parameters $`\vec p`$ (each entry an element of $`A`$; we write $`\vec p \in A`$), $`\mathfrak A \models \varphi(\vec p)`$ means "$`\varphi`$ is true in $`\mathfrak A`$ at $`\vec p`$". We say that $`\mathfrak A`$ **satisfies** $`\varphi(\vec p)`$. A quantifier $`\exists y`$ ranges over the domain $`A`$. When $`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$, a tuple $`\vec y`$ of elements of $`A`$ that makes $`\psi(\vec p, \vec y)`$ true is called a **witness**.

Example (by hand): $`(\omega; \lt) \models \exists y\ (3 \lt y)`$ is true, with witness $`y = 4`$. $`(4; \lt) \models \exists y\ (3 \lt y)`$ is false, because the domain of $`(4; \lt)`$ is $`\{0, 1, 2, 3\}`$.

## 3. Conjunctions of literals

**Definition (literal).** An atomic formula or the negation of an atomic formula is a **literal**.

**Fact (disjunctive normal form).** A quantifier-free formula is equivalent to a finite disjunction of conjunctions of literals. This form is called the **disjunctive normal form**. An existential quantifier distributes over a disjunction.

```math
\exists \vec y\ (\psi_1 \lor \psi_2) \iff \exists \vec y\ \psi_1 \ \lor\ \exists \vec y\ \psi_2
```

So every $`\Sigma_1`$ formula is equivalent to a finite disjunction of formulas of the form "existential quantifiers in front of a conjunction of literals". If two structures agree on all formulas of this form, they agree on all $`\Sigma_1`$ formulas.

**Example.** $`\exists y\ \bigl((p \lt y \land \neg(y \lt q)) \lor E(p, y)\bigr)`$ is equivalent to $`\exists y\ (p \lt y \land \neg(y \lt q)) \lor \exists y\ E(p, y)`$.

**Equality.** If $`\lt`$ is a linear order, no equality symbol is needed, because $`x = y \iff \neg(x \lt y) \land \neg(y \lt x)`$.

The formulas of this repository have only the form "existential quantifiers in front of a conjunction of literals" (§7).

## 4. Substructures and upward preservation

**Definition (substructure).** $`\mathfrak A`$ is a **substructure** of $`\mathfrak B`$ if $`A \subseteq B`$ and each symbol is interpreted by the restriction, that is, $`P^{\mathfrak A}(\vec a) \iff P^{\mathfrak B}(\vec a)`$ for $`\vec a \in A`$.

**Property 1.** In a substructure, quantifier-free formulas about elements of $`A`$ have the same truth value, because the atomic formulas have the same truth values.

**Property 2 (Σ₁ is preserved upward).** In a substructure, if $`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$ then $`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$. The witnesses $`\vec y`$ from $`\mathfrak A`$ are also in $`B`$, and by Property 1 the truth of $`\psi`$ is the same.

**The converse fails.** $`(4; \lt)`$ is a substructure of $`(\omega; \lt)`$. $`\exists y\ (3 \lt y)`$ is true in $`(\omega; \lt)`$ and false in $`(4; \lt)`$ (the example of §2).

## 5. Σ₁-elementary substructures

**Definition (Σ₁-elementary substructure).** $`\mathfrak A`$ is a **$`\Sigma_1`$-elementary substructure** of $`\mathfrak B`$ if $`\mathfrak A`$ is a substructure of $`\mathfrak B`$ and for every $`\Sigma_1`$ formula $`\varphi`$ and all parameters $`\vec p \in A`$:

```math
\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)
```

This is written $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$.

**Meaning.** A claim "there are finitely many elements like this" that uses only elements of $`A`$ is true in $`\mathfrak A`$ if it is true in $`\mathfrak B`$. The witnesses can be chosen again inside $`A`$.

**Example (the language of order only).** Let $`0 \lt \alpha \lt \beta`$ be ordinals.

```math
(\alpha; \lt) \preccurlyeq_{\Sigma_1} (\beta; \lt) \iff \alpha \text{ is a limit ordinal}
```

**Proof.**

- If $`\alpha = \gamma + 1`$: with parameter $`\gamma`$, $`\exists y\ (\gamma \lt y)`$ is true in $`(\beta; \lt)`$ ($`y = \gamma + 1`$) and false in $`(\alpha; \lt)`$. So it fails.
- If $`\alpha`$ is a limit: suppose a $`\Sigma_1`$ formula $`\exists \vec y\ \psi(\vec p, \vec y)`$ is true in $`(\beta; \lt)`$. Move its witnesses $`\vec y`$ into $`\alpha`$, keeping their order relative to the parameters.
  - Witnesses below the largest parameter are already in $`\alpha`$. Keep them.
  - There are finitely many witnesses above the largest parameter (if there are no parameters, count all witnesses here). Since $`\alpha`$ is a limit, there are infinitely many elements of $`\alpha`$ above the largest parameter ([01](01-ordinals.md) §2). Place the witnesses there in the same order.
  - Moving them does not change the truth values of $`\lt`$. So $`\psi`$ is true in $`(\alpha; \lt)`$.
  - The other direction is Property 2 of §4. $`\square`$

$`\alpha = 0`$ is also excluded: $`\exists y\ \neg(y \lt y)`$ is false in the empty structure $`(0; \lt)`$ and true in $`(\beta; \lt)`$.

## 6. The Tarski–Vaught test (Σ₁ version)

To show $`\Sigma_1`$-elementarity it is enough to check the downward direction.

**Theorem (Tarski–Vaught test, Σ₁ version).** Let $`\mathfrak A`$ be a substructure of $`\mathfrak B`$. The following are equivalent.

1. $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$.
2. For quantifier-free $`\psi`$ and $`\vec p \in A`$: if $`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$, then $`\mathfrak B \models \psi(\vec p, \vec y)`$ for some $`\vec y \in A`$.

**Proof.** 1 to 2: the formula is true in $`\mathfrak A`$, so it has witnesses in $`A`$, and by Property 1 of §4 $`\psi`$ is also true in $`\mathfrak B`$. 2 to 1: the upward direction is Property 2 of §4. The downward direction: the witnesses of 2 are in $`A`$, and by Property 1 $`\mathfrak A \models \psi(\vec p, \vec y)`$. $`\square`$

The general Tarski–Vaught test says the same for all formulas. This repository uses only $`\Sigma_1`$.

**How it is used.** Condition 2 says "$`A`$ is closed under witnesses". [08](08-closure-chain.md) uses this form: start from $`\gamma`$, add witnesses of true claims, and take the supremum.

## 7. Templates and the language of this repository

**Definition (template).** Let $`m`$ and $`n`$ be natural numbers. A **template** of length $`m`$ over $`n`$ variables is a sequence $`t = (t_0, \ldots, t_{m-1})`$ that puts, at each coordinate $`k \lt m`$, a number in $`\{0, \ldots, n-1\}`$ or $`\top`$.

**Definition (evaluation).** Let $`v = (v_0, \ldots, v_{n-1})`$ be a tuple of labels. The **evaluation** $`\mathrm{eval}\ t\ v`$ of a template $`t`$ is the key of length $`m`$ with these coordinates:

```math
(\mathrm{eval}\ t\ v)_k = \begin{cases} v_i & (t_k = i) \cr \top & (t_k = \top) \end{cases}
```

**Example (computed with Python).** Let $`m = 2`$ and $`n = 3`$. Let $`v = (3, 5, 8)`$ and $`w = (2, 5, 7)`$.

| Template $`t`$ | $`\mathrm{eval}\ t\ v`$ | $`\mathrm{eval}\ t\ w`$ |
|---|---|---|
| $`(1, \top)`$ | $`(5, \top)`$ | $`(5, \top)`$ |
| $`(2, 0)`$ | $`(8, 3)`$ | $`(7, 2)`$ |
| $`(\top, \top)`$ | $`(\top, \top)`$ | $`(\top, \top)`$ |

In every row $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v`$. The following property is the reason.

**Property 3 (monotonicity).** If $`w_i \le v_i`$ for all $`i`$, then $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v`$.

**Proof.** At each coordinate $`(\mathrm{eval}\ t\ w)_k \le (\mathrm{eval}\ t\ v)_k`$: if $`t_k = i`$ then $`w_i \le v_i`$, and if $`t_k = \top`$ both are $`\top`$. If every coordinate is smaller or equal, then at the first differing coordinate ([02](02-well-founded.md) §3) it is smaller. So $`\le`$ holds for the keys. $`\square`$

**The language of this repository.** The variables of a formula are $`v_0, \ldots, v_{n-1}`$, and we write $`\vec v = (v_0, \ldots, v_{n-1})`$. The number $`i`$ is the position of the variable ([01](01-ordinals.md) §7). There are three kinds of symbols.

- The order $`\lt`$.
- For each template $`t`$ and positions $`i, j`$, an **internal relation** $`\mathrm{Rel}_{t,i,j}(\vec v)`$. It is a relation between the two points $`v_i, v_j`$, with key $`\mathrm{eval}\ t\ v`$.
- For each template $`t`$ and position $`i`$, a **top predicate** $`\mathrm{Top}_{t,i}(\vec v)`$. It is a relation from the point $`v_i`$ to the height $`c`$ of the structure, with key $`\mathrm{eval}\ t\ v`$. $`c`$ plays the role of the top ([02](02-well-founded.md) §3). $`c`$ itself is not in the domain.

The key depends on the values of the variables. Here only the symbols are fixed. The interpretations of the two symbols are given in [07](07-relation-r.md).

The formulas of this repository are $`\Sigma_1`$ formulas of this form:

```math
\exists \vec y\ (\ell_1 \land \cdots \land \ell_r)
```

- Each $`\ell`$ is a literal: $`v_i \lt v_j`$, $`\mathrm{Rel}_{t,i,j}(\vec v)`$, $`\mathrm{Top}_{t,i}(\vec v)`$, or the negation of one of them.
- Some chosen positions are parameters. The variables $`\vec y`$ at the remaining positions are existentially quantified.
- By §3 it is enough to consider this form.

**Example (by hand).** Let $`n = 2`$, position 0 a parameter and position 1 an existentially quantified variable. Let the only literal be $`v_0 \lt v_1`$. This formula is $`\exists v_1\ (p_0 \lt v_1)`$. In a structure of height $`c`$, for a parameter $`p_0 \lt c`$, the formula is true if and only if $`p_0 + 1 \lt c`$.

## 8. Comparing two structures, and partial top predicates

The comparison in this repository differs from the textbook definition in two ways. Below, fix one key $`\theta`$.

**Difference 1: the same symbol is interpreted differently.** The definition of $`R`$ ([07](07-relation-r.md)) compares a structure of height $`a`$ with a structure of height $`b`$ ($`a \lt b`$). The interpretation of the internal relations is shared by the two structures. The top predicate means "the relation to $`a`$" at height $`a`$ and "the relation to $`b`$" at height $`b`$. So we cannot say in advance that one is a substructure of the other.

Therefore, for two structures $`\mathfrak A`$ (height $`a`$) and $`\mathfrak B`$ (height $`b`$), we use $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$ in the following sense.

```math
\forall \varphi\ \forall \vec p \lt a\ \ \bigl(\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)\bigr)
```

$`\varphi`$ ranges over formulas of the form of §7. $`\vec p \lt a`$ means that every parameter is below $`a`$. Being a substructure is not assumed.

Still, being a substructure follows from this condition. Taking formulas in which every variable is a parameter (quantifier-free formulas), the literals about points below $`a`$ have the same truth values. Top literals agree too, where they are defined (Difference 2). So $`\mathfrak A`$ is a substructure of $`\mathfrak B`$, and it is $`\Sigma_1`$-elementary in the sense of §5.

**Difference 2: top predicates are partial.** A top predicate is defined only where its key is below $`\theta`$. That is, the literal $`\mathrm{Top}_{t,i}(\vec v)`$ and its negation $`\neg\mathrm{Top}_{t,i}(\vec v)`$ can each be true only when $`\mathrm{eval}\ t\ v \lt \theta`$. If $`\mathrm{eval}\ t\ v \ge \theta`$, both are false. A top predicate of this kind is called a **partial top predicate**.

**Example (checked with Python).** Let the key length be $`m = 1`$ and $`\theta = (5)`$ (the key whose coordinate 0 is the label 5). There are two variables $`v_0, v_1`$. The template $`t = (0)`$ gives the key $`(v_0)`$, and the template $`t' = (\top)`$ gives the key $`(\top)`$.

| Literal | $`v = (3, 10)`$ | $`v = (7, 10)`$ |
|---|---|---|
| $`\mathrm{Top}_{t,1}(\vec v)`$ | defined, since the key $`(3) \lt \theta`$; the truth value is given by the interpretation | false (the key $`(7)`$ is not below $`\theta`$) |
| $`\neg\mathrm{Top}_{t,1}(\vec v)`$ | defined, since the key $`(3) \lt \theta`$; the truth value is given by the interpretation | false |
| $`\mathrm{Top}_{t',1}(\vec v)`$ | false (the key $`(\top)`$ is not below $`\theta`$) | false |

**Property 4 (lowering the witnesses pointwise keeps the key below θ).** Suppose $`w_i \le v_i`$ for all $`i`$. If $`\mathrm{eval}\ t\ v \lt \theta`$, then $`\mathrm{eval}\ t\ w \lt \theta`$. So a top literal that is defined at $`v`$ is also defined at $`w`$.

**Proof.** By Property 3, $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v \lt \theta`$. $`\square`$

This property is used where witnesses are replaced by pointwise smaller values ([07](07-relation-r.md) §7, [09](09-obligations.md)).

**Property 5 (only what is read matters).** In a structure of height $`c`$, the truth value of a formula of the form of §7 depends only on two things: the interpretation of the internal relations between points below $`c`$, and the interpretation of the top predicates at points below $`c`$ with keys below $`\theta`$. If two interpretations agree there, every formula has the same truth value in both, because a formula reads nothing else.

This property is used in [07](07-relation-r.md) to remove the guards ([02](02-well-founded.md) §5).

**Difference from the 1-Y version.** In the 1-Y study ([study/ of koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por/tree/main/study)), whether a top predicate is defined was decided by the positions of the variables alone. In this repository it is decided by the value of the key $`\mathrm{eval}\ t\ v`$, that is, by the values of the variables. This is why Property 4 is needed.

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §2.1 (Japanese) | the domain of the structures, internal relations, partial top predicates (§1, §7, §8) |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §2.2 (Japanese) | a formula is a conjunction of literals with existential quantifiers in front; a top literal can be true only when its key is below $`\theta`$ (§3, §7, §8) |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §2.3 (Japanese) | $`\preccurlyeq_{\Sigma_1}`$ read as agreement of formulas with parameters below $`a`$ (§5, §8) |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §3.1 (Japanese) | lowering the witnesses pointwise keeps the key below $`\theta`$ (Property 4 of §8) |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §3.3 (Japanese) | closed points are defined in the form of condition 2 of §6 (closed under witnesses) |
| [notes/00-survey.md](../../notes/00-survey.md) §3.2 (Japanese) | key templates and the monotonicity of evaluation (§7) |
