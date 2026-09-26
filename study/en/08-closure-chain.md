[← Back](README.md) | [English](08-closure-chain.md) | [Japanese](../08-closure-chain.md)

# Closure below ω₁ and the sequence of Good points

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, supremum, countable, $`\omega_1`$, regularity of $`\omega_1`$, label, $`\{0, \ldots, n-1\}`$, the set with none added, position, the set of inputs |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | structure, domain, height, formula, $`\Sigma_1`$ formula, parameter, witness, literal, substructure, $`\preccurlyeq_{\Sigma_1}`$, Tarski–Vaught test, template, evaluation $`\mathrm{eval}\ t\ \vec v`$ |
| [07 The relation R](07-relation-r.md) | the relation $`R`$, the structure $`\mathfrak A^c_\theta`$, $`\mathrm{Rel}_{t,i,j}`$, $`\mathrm{Top}_{t,i}`$, $`\vec p \lt a`$ |

This note explains how to build points below $`\omega_1`$ that are closed under witnesses of $`\Sigma_1`$ formulas (the Good points of §1). The idea is the same as in the Löwenheim–Skolem theorem: add witnesses and take the supremum. The sequence of the points built here gives the first labels in [09](09-obligations.md).

The key length $`m`$ is fixed.

## 1. The ambient structure and Good

**Definition (ambient structure).** Let $`\mathfrak B`$ be the structure of height $`\omega_1`$ whose top predicates are defined for every key. The symbols $`\mathrm{Rel}_{t,i,j}`$ and $`\mathrm{Top}_{t,i}`$ are those of [07](07-relation-r.md) §2.

```math
\mathfrak B = \bigl(\omega_1;\ \lt,\ (\mathrm{Rel}_{t,i,j}),\ (\mathrm{Top}_{t,i})\bigr), \qquad \mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ \omega_1)
```

$`\mathrm{Rel}_{t,i,j}`$ has the meaning of [07](07-relation-r.md) §2. Since $`\omega_1`$ is a label ([01](01-ordinals.md) §6), $`R(\kappa, x, \omega_1)`$ makes sense. Unlike $`\mathfrak A^{\omega_1}_\theta`$ of [07](07-relation-r.md) §3, the top predicates are defined for every key.

**Definition (Good).** Let $`\alpha`$ be a label. Let $`\mathfrak B{\restriction}\alpha`$ be $`\mathfrak B`$ with its domain restricted to $`\{x \mid x \lt \alpha\}`$. The top predicates stay those toward $`\omega_1`$. A label $`\alpha`$ is **Good** if the following holds, where $`\varphi`$ ranges over $`\Sigma_1`$ formulas and $`\vec p \lt \alpha`$ over parameters.

```math
\mathrm{Good}(\alpha) :\iff \forall \varphi\ \forall \vec p \lt \alpha\ \bigl(\mathfrak B \models \varphi(\vec p) \implies \mathfrak B{\restriction}\alpha \models \varphi(\vec p)\bigr)
```

$`\mathfrak B{\restriction}\alpha`$ is a substructure of $`\mathfrak B`$ (the same interpretation, only the domain differs). The converse implication always holds ($`\Sigma_1`$ formulas are preserved upward, [03](03-sigma1-elementary.md) §4). So by the Tarski–Vaught test of [03](03-sigma1-elementary.md) §6, $`\mathrm{Good}(\alpha)`$ is the same as $`\mathfrak B{\restriction}\alpha \preccurlyeq_{\Sigma_1} \mathfrak B`$. A Good point has, below itself, witnesses of the $`\Sigma_1`$ statements true in $`\mathfrak B`$.

## 2. There are countably many formulas

**Theorem.** The set of all formulas of this language is countable.

**Proof.** A formula is a finite sequence of the following symbols.

| Symbols | How many |
|---|---|
| variables $`v_0, v_1, \ldots`$ | countably many |
| $`\lt`$, logical symbols ($`\neg, \land, \lor, \to, \exists, \forall`$), parentheses | finitely many |
| $`\mathrm{Rel}_{t,i,j}`$, $`\mathrm{Top}_{t,i}`$ for a template $`t`$ over $`n`$ variables and positions $`i, j \lt n`$ | finitely many for each $`n`$ |

A template over $`n`$ variables puts a number in $`\{0, \ldots, n-1\}`$ or $`\top`$ at each coordinate of a key of length $`m`$ ([03](03-sigma1-elementary.md) §7). There are $`(n+1)^m`$ of them, finitely many. So there are countably many symbols. The set of all finite sequences of elements of a countable set is countable. $`\square`$

The set of all templates must be countable. One formula uses only finitely many templates, but for the set of all formulas to be countable, the set of all templates must be countable.

## 3. The witness height

**Definition (witness height).** For a $`\Sigma_1`$ formula $`\varphi = \exists \vec y\ \psi(\vec p, \vec y)`$ and parameters $`\vec p \lt \omega_1`$, define the **witness height** $`H(\varphi, \vec p)`$ as follows.

- If $`\mathfrak B \models \varphi(\vec p)`$, choose one witness $`\vec y = (y_1, \ldots, y_k)`$ and let $`H(\varphi, \vec p) := \sup_{j} (y_j + 1)`$. If $`k = 0`$, it is $`0`$.
- Otherwise $`H(\varphi, \vec p) := 0`$.

$`H(\varphi, \vec p)`$ is the least height of a structure whose domain contains all of the chosen witness. The choice of the witness is fixed once for each $`(\varphi, \vec p)`$. The choice is made for all $`(\varphi, \vec p)`$ at once, so it uses the axiom of choice.

| Property | Statement | Reason |
|---|---|---|
| Property 1 | $`H(\varphi, \vec p) \lt \omega_1`$ | the supremum of finitely many $`y_j + 1 \lt \omega_1`$ ([01](01-ordinals.md) §5) |
| Property 2 | every entry of the chosen witness is below $`H(\varphi, \vec p)`$ | $`y_j \lt y_j + 1 \le H(\varphi, \vec p)`$ |

## 4. One step of the closure

An element $`q`$ of the set of inputs $`\mathrm{In}(\gamma)`$ ([01](01-ordinals.md) §7) is a pair of a $`\Sigma_1`$ formula $`\varphi_q`$ and a function that puts, at each position of $`\varphi_q`$, a label below $`\gamma`$ or none. Let $`\vec p_q`$ be the values that $`q`$ puts at the parameter positions (with 0 where it puts none).

**Lemma.** If $`\gamma \lt \omega_1`$, then $`\mathrm{In}(\gamma)`$ is countable.

**Proof.** By §2, the set $`\Phi`$ of $`\Sigma_1`$ formulas is countable. Apply the theorem of [01](01-ordinals.md) §7 (the set of inputs is countable). $`\square`$

**Definition (one step of the closure).** For $`\gamma \lt \omega_1`$, define:

```math
N(\gamma) := \max\Bigl(\gamma + 1,\ \sup_{q \in \mathrm{In}(\gamma)} H\bigl(\varphi_q, \vec p_q\bigr)\Bigr)
```

The supremum ranges over all formulas with parameters below $`\gamma`$.

| Property | Statement | Reason |
|---|---|---|
| Property 3 | $`\gamma \lt N(\gamma)`$ | the term $`\gamma + 1`$ |
| Property 4 | $`N(\gamma) \lt \omega_1`$ | by the lemma, a supremum of countably many terms, each below $`\omega_1`$ by Property 1. Regularity of $`\omega_1`$ ([01](01-ordinals.md) §5) |
| Property 5 | if $`\vec p \lt \gamma`$ and $`\mathfrak B \models \varphi(\vec p)`$, then $`\mathfrak B{\restriction}N(\gamma) \models \varphi(\vec p)`$ | the proof below |

**Proof of Property 5.** Make the input $`q \in \mathrm{In}(\gamma)`$ that puts the values of $`\vec p`$ at the parameter positions and none at the other positions. Then $`\varphi_q = \varphi`$ and $`\vec p_q = \vec p`$. The witness chosen for $`q`$ is below $`H(\varphi, \vec p)`$ (Property 2). $`H(\varphi, \vec p)`$ is one of the terms of the supremum, so it is at most $`N(\gamma)`$. So the witness is below $`N(\gamma)`$ and lies in the domain of $`\mathfrak B{\restriction}N(\gamma)`$. The quantifier-free part has the same truth value in the substructure. $`\square`$

## 5. The tower and λ

**Definition (tower and λ).** Let $`\gamma \lt \omega_1`$ and let $`k`$ be a natural number.

```math
N^0(\gamma) := \gamma, \quad N^{k+1}(\gamma) := N\bigl(N^k(\gamma)\bigr), \qquad \lambda(\gamma) := \sup_{k \in \mathbb N} N^k(\gamma)
```

The sequence $`N^0(\gamma), N^1(\gamma), \ldots`$ is called the **tower**. By Property 4 each $`N^k(\gamma)`$ is below $`\omega_1`$, so $`N`$ can be applied again and again.

| Property | Statement | Reason |
|---|---|---|
| Property 6 | $`N^k(\gamma) \lt \omega_1`$ | Property 4 and induction on $`k`$ |
| Property 7 | $`N^k(\gamma) \lt N^{k+1}(\gamma)`$ | Property 3 |
| Property 8 | if $`k \le k'`$ then $`N^k(\gamma) \le N^{k'}(\gamma)`$ | Property 7 |
| Property 9 | $`N^k(\gamma) \le \lambda(\gamma)`$ | definition of the supremum |
| Property 10 | $`\lambda(\gamma) \lt \omega_1`$ | a supremum of countably many terms (Property 6, regularity of $`\omega_1`$) |
| Property 11 | $`\gamma \lt \lambda(\gamma)`$ | $`\gamma \lt N^1(\gamma) \le \lambda(\gamma)`$ |
| Property 12 | for finitely many $`p_i \lt \lambda(\gamma)`$, there is $`k`$ with $`p_i \lt N^k(\gamma)`$ for all of them | the proof below |

**Proof of Property 12.** Each $`p_i`$ is below the supremum, so $`p_i \lt N^{k_i}(\gamma)`$ for some $`k_i`$. Take $`k := \max_i k_i`$ and use Property 8. $`\square`$

## 6. λ(γ) is Good

**Theorem.** If $`\gamma \lt \omega_1`$, then $`\mathrm{Good}(\lambda(\gamma))`$.

**Proof.** We prove it in the form of the Tarski–Vaught test ([03](03-sigma1-elementary.md) §6). Let $`\vec p \lt \lambda(\gamma)`$ and $`\mathfrak B \models \varphi(\vec p)`$. By Property 12, $`\vec p \lt N^k(\gamma)`$ for some $`k`$. Property 5 at $`N^k(\gamma)`$ gives a witness below $`N^{k+1}(\gamma)`$. Since $`N^{k+1}(\gamma) \le \lambda(\gamma)`$ (Property 9), the witness is below $`\lambda(\gamma)`$. $`\square`$

**Corollary (Good points are cofinal).** If $`\sigma \lt \omega_1`$, there is $`\alpha`$ with $`\sigma \lt \alpha \lt \omega_1`$ and $`\mathrm{Good}(\alpha)`$. $`\alpha = \lambda(\sigma)`$ works (Property 10, Property 11, the theorem).

**Example (only the shape).** $`\lambda(0)`$ contains all witnesses of the $`\Sigma_1`$ statements true in $`\mathfrak B`$ whose parameters are below $`\lambda(0)`$. The concrete value of $`\lambda(0)`$ is unknown. The proof does not use the value; it uses only $`\lambda(0) \lt \omega_1`$ and $`\mathrm{Good}(\lambda(0))`$. This example was not computed, since truth in $`\mathfrak B`$ cannot be computed.

**On the set of Good points.** We do not show, and do not use, that the set of Good points is closed in $`\omega_1`$ (that the supremum of an increasing sequence of Good points is again Good). So we do not call it a club (closed unbounded set).

## 7. The sequence of Good points

**Definition (sequence of Good points).**

```math
p_0 := \lambda(0), \qquad p_{k+1} := \lambda(p_k)
```

| Property | Statement |
|---|---|
| Property 13 | $`p_k \lt \omega_1`$ |
| Property 14 | $`p_0 \lt p_1 \lt p_2 \lt \cdots`$ |
| Property 15 | $`\mathrm{Good}(p_k)`$ |

All follow from §5 and §6 by induction on $`k`$. Property 13 follows from Property 10, Property 14 from Property 11, and Property 15 from the theorem of §6.

Any two points of this sequence are in the relation $`R`$ for every key. The proof needs that at a Good point the top predicates agree with the top predicates toward $`\omega_1`$. Both are explained in [09](09-obligations.md) §3.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Status" | the axioms used by the proof include the axiom of choice. It is used where §3 chooses witnesses and where §4 uses that the set of inputs is countable ([01](01-ordinals.md) §7) |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §3.3 (Japanese) | closed points (the Good points of this note), repeating $`\omega`$ times, the sequence of closed points |
