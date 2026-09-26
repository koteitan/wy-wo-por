[← Back](README.md) | [English](01-ordinals.md) | [Japanese](../01-ordinals.md)

# Ordinals and ω₁

Prerequisites

| Note | Terms used here |
|---|---|
| none | none |

This note explains ordinals and $`\omega_1`$. Later notes use two kinds of ordinals. One kind is the ordinals below $`\omega^\omega`$, used as rows of the mountain ([05](05-omegay-mountain.md)). The other kind is the ordinals at most $`\omega_1`$, used as labels put on columns (§6). The facts used later are the coefficients and sums of §1, the regularity of §5, the labels of §6 and the counting of §7.

## 1. Well-orders and ordinals

**Definition (well-order).** A total order $`\lt`$ on a set $`X`$ is a **well-order** if every nonempty subset of $`X`$ has a least element.

**Definition (infinite descending sequence).** A sequence $`(x_n)_{n \in \mathbb N}`$ with $`x_0 \gt x_1 \gt x_2 \gt \cdots`$ is an **infinite descending sequence**.

A total order is a well-order if and only if it has no infinite descending sequence. The direction "no infinite descending sequence implies well-order" uses a weak form of the axiom of choice (dependent choice).

| Order | Well-order? | Reason |
|---|---|---|
| $`(\mathbb N, \lt)`$ | yes | every nonempty subset has a least element |
| $`(\mathbb Z, \lt)`$ | no | $`0 \gt -1 \gt -2 \gt \cdots`$ |
| $`(\mathbb Q_{\ge 0}, \lt)`$ | no | $`1 \gt 1/2 \gt 1/4 \gt \cdots`$ |

**Definition (ordinal).** An **ordinal** is the order type of a well-order. An ordinal $`\alpha`$ is identified with the set $`\{\beta \mid \beta \lt \alpha\}`$ of smaller ordinals.

In increasing order:

```math
0,\ 1,\ 2,\ \ldots,\ \omega,\ \omega+1,\ \omega+2,\ \ldots,\ \omega \cdot 2,\ \ldots,\ \omega^2,\ \ldots,\ \omega^\omega,\ \ldots
```

- $`\omega`$ is the type of the natural numbers: $`\omega = \{0, 1, 2, \ldots\}`$.
- The ordinals are well-ordered by $`\lt`$. Every nonempty collection of ordinals has a least element.

**Definition (sum).** The sum $`\alpha + \beta`$ of ordinals is the type of the well-order obtained by putting a well-order of type $`\beta`$ after a well-order of type $`\alpha`$.

Example: $`2 + \omega`$ is the type of $`0, 1`$ followed by a sequence of type $`\omega`$. This is the type $`\omega`$, so $`2 + \omega = \omega`$. On the other hand $`\omega + 2 \gt \omega`$. The sum is not commutative.

### Cantor normal form

**Theorem (Cantor normal form).** An ordinal $`\alpha`$ below $`\omega^\omega`$ can be written in exactly one way in the form below, with a natural number $`d`$ and natural numbers $`c_0, \ldots, c_d`$. Here $`c_d \ne 0`$ if $`\alpha \ne 0`$, and $`d = 0`$, $`c_0 = 0`$ if $`\alpha = 0`$.

```math
\alpha = \omega^d \cdot c_d + \cdots + \omega \cdot c_1 + c_0
```

This theorem is not proved here. It is in textbooks on ordinals.

**Definition (coefficient).** For $`\alpha`$ in the form above, put $`c_k(\alpha) := c_k`$ for $`k \le d`$ and $`c_k(\alpha) := 0`$ for $`k \gt d`$. $`c_k(\alpha)`$ is the **coefficient of degree $`k`$** of $`\alpha`$.

**Definition (degree).** For $`\alpha \ne 0`$, the **degree** $`\deg \alpha`$ of $`\alpha`$ is the largest $`k`$ with $`c_k(\alpha) \ne 0`$. Put $`\deg 0 = 0`$.

| $`\alpha`$ | $`c_2(\alpha)`$ | $`c_1(\alpha)`$ | $`c_0(\alpha)`$ | $`\deg \alpha`$ |
|---|---|---|---|---|
| $`\omega^2 \cdot 2 + 3`$ | 2 | 0 | 3 | 2 |
| $`\omega`$ | 0 | 1 | 0 | 1 |
| $`7`$ | 0 | 0 | 7 | 0 |
| $`0`$ | 0 | 0 | 0 | 0 |

**Comparison.** Let $`\alpha \ne \beta`$, and take the largest $`k`$ with $`c_k(\alpha) \ne c_k(\beta)`$. Then $`\alpha \lt \beta \iff c_k(\alpha) \lt c_k(\beta)`$.

The following examples were computed with Python.

| Two ordinals | Result | Largest $`k`$ where the coefficients differ |
|---|---|---|
| $`\omega \cdot 2 + 5`$ and $`\omega^2`$ | $`\omega \cdot 2 + 5 \lt \omega^2`$ | 2 |
| $`\omega^2 \cdot 2 + 3`$ and $`\omega^2 \cdot 2 + \omega`$ | $`\omega^2 \cdot 2 + 3 \lt \omega^2 \cdot 2 + \omega`$ | 1 |
| $`7`$ and $`\omega`$ | $`7 \lt \omega`$ | 1 |

**The sum $`\alpha + \omega^e`$.** Let $`e`$ be a natural number. If $`k \lt e`$, then $`\omega^k \cdot c + \omega^e = \omega^e`$ (for the same reason as $`2 + \omega = \omega`$). So in $`\alpha + \omega^e`$ the coefficients below degree $`e`$ vanish.

```math
c_k(\alpha + \omega^e) = \begin{cases} 0 & (k \lt e) \cr c_e(\alpha) + 1 & (k = e) \cr c_k(\alpha) & (k \gt e) \end{cases}
```

The following examples were computed with Python.

| $`\alpha`$ | $`e`$ | $`\alpha + \omega^e`$ |
|---|---|---|
| $`2`$ | 1 | $`\omega`$ |
| $`\omega`$ | 2 | $`\omega^2`$ |
| $`\omega^2 \cdot 2 + \omega + 3`$ | 0 | $`\omega^2 \cdot 2 + \omega + 4`$ |
| $`\omega^2 \cdot 2 + \omega + 3`$ | 1 | $`\omega^2 \cdot 2 + \omega \cdot 2`$ |
| $`\omega^2 \cdot 2 + \omega + 3`$ | 3 | $`\omega^3`$ |

## 2. Successors and limits

**Definition (successor).** $`\alpha + 1`$ is the ordinal right after $`\alpha`$. An ordinal of the form $`\alpha + 1`$ is a **successor ordinal**.

**Definition (limit ordinal).** An ordinal that is neither 0 nor a successor ordinal is a **limit ordinal**.

| Ordinal | Kind |
|---|---|
| $`0`$ | neither |
| $`5`$, $`\omega+1`$, $`\omega \cdot 2 + 3`$ | successor |
| $`\omega`$, $`\omega \cdot 2`$, $`\omega^2`$ | limit |

**Property.** If $`\alpha`$ is a limit ordinal and $`\beta \lt \alpha`$, then $`\beta + 1 \lt \alpha`$. Hence there are infinitely many elements above $`\beta`$ and below $`\alpha`$.

This property is used in the example of [03](03-sigma1-elementary.md) §5.

## 3. Suprema

**Definition (supremum).** The **supremum** $`\sup S`$ of a set $`S`$ of ordinals is the least ordinal that is at least every element of $`S`$.

- If $`S`$ has a greatest element, $`\sup S`$ is that element. A nonempty finite set always has one. The supremum of the empty set is $`0`$.
- If $`S`$ has no greatest element, $`\sup S`$ is not in $`S`$.

| $`S`$ | $`\sup S`$ |
|---|---|
| $`\{2, 5, 3\}`$ | $`5`$ |
| $`\{0, 1, 2, \ldots\}`$ | $`\omega`$ |
| $`\{\omega, \omega+1, \omega+2, \ldots\}`$ | $`\omega \cdot 2`$ |

To get a number strictly greater than every element, use $`\sup_{i} (y_i + 1)`$, since $`y_i \lt y_i + 1 \le \sup_i (y_i + 1)`$. [08](08-closure-chain.md) §3 uses a supremum of this form.

## 4. Countability and ω₁

**Definition (countable).** A set $`X`$ is **countable** if it is empty or there is a surjection $`\mathbb N \to X`$.

**Definition (countable ordinal).** An ordinal $`\alpha`$ is **countable** if $`\{\beta \mid \beta \lt \alpha\}`$ is countable.

$`0, 1, \omega, \omega+1, \omega \cdot 2, \omega^2, \omega^\omega`$ are all countable.

**Definition (ω₁).** $`\omega_1`$ is the first uncountable ordinal. The ordinals below $`\omega_1`$ are exactly the countable ordinals.

```math
\alpha \lt \omega_1 \iff \alpha \text{ is countable}
```

We use the following three facts.

- $`0 \lt \omega_1`$.
- $`\alpha \lt \omega_1 \implies \alpha + 1 \lt \omega_1`$.
- $`\gamma \lt \omega_1 \implies \{\beta \mid \beta \lt \gamma\}`$ is countable.

Reason for the second: $`\{\beta \mid \beta \lt \alpha + 1\} = \{\beta \mid \beta \lt \alpha\} \cup \{\alpha\}`$, and adding one point to a countable set gives a countable set. In other words, $`\omega_1`$ is a limit ordinal.

## 5. Regularity of ω₁

**Theorem (regularity of ω₁).** Let $`I`$ be a countable set and $`\alpha_i \lt \omega_1`$ for each $`i \in I`$. Then:

```math
\sup_{i \in I} \alpha_i \lt \omega_1
```

In other words, the supremum of countably many countable ordinals is below $`\omega_1`$.

**Proof.** Put $`\sigma := \sup_i \alpha_i`$. If $`\beta \lt \sigma`$, then $`\beta \lt \alpha_i`$ for some $`i`$. Hence

```math
\{\beta \mid \beta \lt \sigma\} = \bigcup_{i \in I} \{\beta \mid \beta \lt \alpha_i\}
```

The right side is a countable union of countable sets. Terms with $`\alpha_i = 0`$ add nothing, so drop them. For each remaining $`i`$ choose a surjection $`e_i : \mathbb N \to \{\beta \mid \beta \lt \alpha_i\}`$. Enumerate $`I`$ by $`\mathbb N`$ and write $`i_n`$ for the $`n`$-th element. Then $`(n, t) \mapsto e_{i_n}(t)`$ is a surjection from $`\mathbb N \times \mathbb N`$ onto the union. $`\mathbb N \times \mathbb N`$ is countable, so the union is countable. Hence $`\sigma`$ is countable and $`\sigma \lt \omega_1`$. $`\square`$

- Choosing countably many surjections $`e_i`$ at once uses the axiom of choice (countable choice).
- It fails for an uncountable $`I`$. For example, $`\sup_{\alpha \lt \omega_1} \alpha = \omega_1`$.

## 6. Labels

**Definition (label).** An ordinal at most $`\omega_1`$ is a **label**.

```math
\mathrm{Label} = \{\, o \mid o \le \omega_1 \,\}
```

The order of labels is the order of ordinals. It is a well-order. The greatest label is $`\omega_1`$.

- Since $`0 \lt \omega_1`$, there is a label below $`\omega_1`$.
- If $`a \lt \omega_1`$, the set $`\{x \mid x \lt a\}`$ of labels below $`a`$ is countable (§4).

**Why ω₁ itself is a label.** Later notes choose finitely many labels below $`\omega_1`$ and put them on columns. On the other hand, they also consider a condition between two labels $`x \lt b`$ in the case $`b = \omega_1`$ ([08](08-closure-chain.md), [09](09-obligations.md)). For this, $`\omega_1`$ is put into the same set $`\mathrm{Label}`$.

## 7. Counting parameters

A later note ([08](08-closure-chain.md)) takes a supremum over all tuples that put ordinals below $`\gamma`$ at finitely many numbered places. Here we show that the set of these tuples is countable. The ordinals put there are called parameters in [03](03-sigma1-elementary.md) §2.

Notation.

- For a natural number $`n`$, $`\{0, \ldots, n-1\}`$ is the set of $`n`$ numbers. It is empty if $`n = 0`$.
- For a set $`X`$, $`X \cup \{\mathrm{none}\}`$ is $`X`$ with one new element $`\mathrm{none}`$ added. $`\mathrm{none}`$ is not an element of $`X`$. $`\mathrm{none}`$ stands for "put nothing".
- For a set $`\Phi`$ and a set $`X_\varphi`$ for each $`\varphi \in \Phi`$, the **dependent sum** is $`\sum_{\varphi \in \Phi} X_\varphi = \{(\varphi, q) \mid \varphi \in \Phi,\ q \in X_\varphi\}`$.
- Let $`\Phi`$ be a set, and suppose each $`\varphi \in \Phi`$ has a natural number $`n_\varphi`$. The elements of $`\{0, \ldots, n_\varphi - 1\}`$ are the **positions** of $`\varphi`$.

**Definition (set of inputs).** Let $`\gamma`$ be an ordinal. The **set of inputs** is:

```math
\mathrm{In}(\gamma) = \sum_{\varphi \in \Phi} \Bigl(\{0, \ldots, n_\varphi - 1\} \to \{\, x \mid x \lt \gamma \,\} \cup \{\mathrm{none}\}\Bigr)
```

Here $`A \to B`$ is the set of functions from $`A`$ to $`B`$. An input $`(\varphi, q)`$ puts on each position of $`\varphi`$ either an ordinal below $`\gamma`$ or nothing ($`\mathrm{none}`$).

**Theorem (the set of inputs is countable).** If $`\Phi`$ is countable and $`\gamma \lt \omega_1`$, then $`\mathrm{In}(\gamma)`$ is countable.

**Proof.**

- $`Y := \{x \mid x \lt \gamma\} \cup \{\mathrm{none}\}`$ is countable, because $`\{x \mid x \lt \gamma\}`$ is countable (§4) and adding one point keeps it countable.
- There are countably many finite functions into a countable set. That is, $`\{0, \ldots, n-1\} \to Y`$ is countable. This set is the same as the product $`Y^n`$ of $`n`$ copies of $`Y`$, and a finite product of countable sets is countable.
- A dependent sum of countable sets over a countable $`\Phi`$ is countable, because it is a union of countably many countable sets (this uses countable choice, as in the proof of §5). $`\square`$

**Example (by hand).** Let $`\gamma = \omega + 1`$ and $`n_\varphi = 3`$. The input that puts $`3`$ at position 0, nothing at position 1 and $`\omega`$ at position 2 is $`(\varphi, q)`$ with $`q(0) = 3`$, $`q(1) = \mathrm{none}`$, $`q(2) = \omega`$. Since $`3 \lt \gamma`$ and $`\omega \lt \gamma`$, it is an element of $`\mathrm{In}(\gamma)`$.

The 1-Y study ([study/ of koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por/tree/main/study)) enumerated the ordinals below $`\gamma`$ by natural numbers, so that the set of tuples did not depend on $`\gamma`$. This repository puts the ordinals themselves at the positions. The set of tuples depends on $`\gamma`$, but it is countable, so the theorem of §5 applies directly.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [notes/00-survey.md](../../notes/00-survey.md) §1.3 (Japanese) | rows of the mountain are ordinals below $`\omega^\omega`$, written by their coefficients (§1) |
| [notes/03-official-rule.md](../../notes/03-official-rule.md) §1.1 (Japanese) | the coefficient of degree $`k`$; in the sum $`\rho + \omega^e`$ the coefficients below degree $`e`$ vanish (§1) |
| [notes/00-survey.md](../../notes/00-survey.md) §3.2 (Japanese) | labels are ordinals at most $`\omega_1`$ (§6) |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §3.3 (Japanese) | countably many formulas, $`\omega`$ iterations, a supremum below $`\omega_1`$ (§3–§5, §7) |
