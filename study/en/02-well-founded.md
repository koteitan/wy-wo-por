[← Back](README.md) | [English](02-well-founded.md) | [Japanese](../02-well-founded.md)

# Well-founded relations and recursion

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, infinite descending sequence, labels $`\{o \mid o \le \omega_1\}`$, $`\{0, \ldots, n-1\}`$ |

This note explains three things: well-founded relations, well-founded recursion, and termination by decreasing labels. The definition of the relation $`R`$ ([07](07-relation-r.md)) has the form of §4 and §5. The whole termination proof ([06](06-combinatorial-layer.md)) has the form of §6.

## 1. Well-founded relations

**Definition (well-founded).** A relation $`\prec`$ on a set $`X`$ is **well-founded** if every nonempty subset $`S`$ of $`X`$ has a $`\prec`$-minimal element, that is, an $`x \in S`$ with no $`y \in S`$ such that $`y \prec x`$.

A relation is well-founded if and only if there is no infinite descending sequence $`x_0 \succ x_1 \succ x_2 \succ \cdots`$. The direction "no infinite descending sequence implies well-founded" uses a weak form of the axiom of choice (dependent choice).

**Definition (accessible).** Let $`Q`$ be the least subset of $`X`$ closed under the following condition.

```math
\bigl(\forall y \prec x\ \ y \in Q\bigr) \implies x \in Q
```

If $`x \in Q`$, we say that $`x`$ is **accessible**. In other words, $`x`$ is accessible when every $`y`$ with $`y \prec x`$ is accessible. An $`x`$ with no $`y \prec x`$ is accessible.

**Property.** $`\prec`$ is well-founded if and only if every $`x \in X`$ is accessible.

**Proof.**

- If it is well-founded: suppose the set $`S`$ of elements that are not accessible is nonempty. Take a minimal element $`x`$ of it. If $`y \prec x`$, then $`y \notin S`$, so $`y`$ is accessible. Hence $`x`$ is accessible, against $`x \in S`$.
- If every element is accessible: let $`S`$ be a subset with no minimal element. $`X \setminus S`$ is closed under the condition above, because if no $`y \prec x`$ lies in $`S`$ but $`x \in S`$, then $`x`$ would be a minimal element of $`S`$. $`Q`$ is the least closed set, so $`Q \subseteq X \setminus S`$. Since $`Q = X`$, $`S`$ is empty. $`\square`$

| Relation | Well-founded? |
|---|---|
| $`\lt`$ on $`\mathbb N`$ | yes |
| $`\lt`$ on ordinals, on labels | yes |
| $`\lt`$ on $`\mathbb Z`$ | no |
| lexicographic order on all finite sequences | no |

**Definition (lexicographic order on finite sequences).** Two finite sequences $`s, t`$ of integers are compared at the first entry where they differ. If one is a proper initial part (prefix) of the other, the shorter one is smaller. This is the **lexicographic order**.

**Example.** The following is an infinite descending sequence in the lexicographic order. The first differing entry is $`2`$ in the left sequence and $`1`$ in the right one. The first 5 terms were checked with Python.

```math
(1,2) \gt (1,1,2) \gt (1,1,1,2) \gt (1,1,1,1,2) \gt \cdots
```

So the lexicographic order is not well-founded on all finite sequences. Even when the order on the entries is well-founded, it fails when the length is unbounded. The termination proof of later notes uses the method of §6, not the lexicographic order.

## 2. Well-founded induction

**Theorem (well-founded induction).** Let $`\prec`$ be well-founded, and let a property $`P`$ satisfy:

```math
\forall x\ \Bigl(\bigl(\forall y \prec x\ \ P(y)\bigr) \implies P(x)\Bigr)
```

Then $`P(x)`$ holds for every $`x`$.

**Proof.** Suppose the set of $`x`$ where $`P`$ fails is nonempty. Take a minimal element $`x`$. For $`y \prec x`$, $`P(y)`$ holds. By the assumption $`P(x)`$ holds, a contradiction. $`\square`$

## 3. Lexicographic products and the order of keys

**Definition (lexicographic product).** For $`(A, \lt_A)`$ and $`(B, \lt_B)`$, the **lexicographic order** on $`A \times B`$ is:

```math
(a, b) \prec (a', b') \iff a \lt_A a' \ \lor\ (a = a' \land b \lt_B b')
```

**Theorem.** If $`\lt_A`$ and $`\lt_B`$ are well-founded, so is the lexicographic order.

**Proof.** Show that $`(a, b)`$ is accessible by well-founded induction on $`b`$ inside well-founded induction on $`a`$. A pair below $`(a, b)`$ either has $`a' \lt_A a`$ (accessible by the outer induction hypothesis) or has the same $`a`$ and $`b' \lt_B b`$ (accessible by the inner induction hypothesis). By the property of §1 the order is well-founded. $`\square`$

**Example.** In $`\mathbb N \times \mathbb N`$ there are infinitely many pairs below $`(1, 0)`$: $`(0, 0), (0, 1), (0, 2), \ldots`$. Still every descending sequence is finite. For example $`(1,0) \succ (0, 100) \succ (0, 99) \succ \cdots \succ (0, 0)`$ stops after 102 terms (counted with Python).

**Definition (key).** Let $`m`$ be a natural number. **$`\top`$** is a new element that is not a label and is greater than every label. $`\omega_1`$ is a label, so $`\omega_1 \lt \top`$. A **key** of length $`m`$ is a sequence $`K = (K_0, \ldots, K_{m-1})`$ of $`m`$ entries, each a label or $`\top`$. The set of keys is written $`\mathrm{Key}_m`$.

```math
\mathrm{Key}_m = \bigl\{\, K \mid K : \{0, \ldots, m-1\} \to \mathrm{Label} \cup \{\top\} \,\bigr\}
```

The $`k`$-th entry $`K_k`$ of a key is called **coordinate** $`k`$. Two keys are compared at the **first coordinate where they differ**.

```math
K \lt K' \iff \exists k\ \bigl(K_k \lt K'_k \ \land\ \forall j \lt k\ \ K_j = K'_j\bigr)
```

The key $`(\top, \ldots, \top)`$ whose coordinates are all $`\top`$ is the greatest element of $`\mathrm{Key}_m`$.

The following table was checked with Python.

| Two keys ($`m = 2`$) | Result | Reason |
|---|---|---|
| $`(3, 5)`$ and $`(3, \top)`$ | $`(3, 5) \lt (3, \top)`$ | equal at coordinate 0, $`5 \lt \top`$ at coordinate 1 |
| $`(2, \top)`$ and $`(3, 0)`$ | $`(2, \top) \lt (3, 0)`$ | $`2 \lt 3`$ at coordinate 0 |
| $`(\omega, 0)`$ and $`(5, \top)`$ | $`(5, \top) \lt (\omega, 0)`$ | $`5 \lt \omega`$ at coordinate 0 |

**Theorem (the order of keys is well-founded).** The order on $`\mathrm{Key}_m`$ is well-founded.

**Proof.** $`\mathrm{Label} \cup \{\top\}`$ is well-founded: a descending sequence contains $`\top`$ at most once, as its first term, and the rest is a descending sequence of labels. Comparing sequences of length $`m`$ at the first differing coordinate is the same order as the lexicographic product above iterated $`m - 1`$ times. So it is well-founded. $`\square`$

**Definition (stage and top).** [07](07-relation-r.md) defines a relation $`R(\theta, a, b)`$, where $`\theta`$ is a key and $`a`$ and $`b`$ are labels. The definition is a well-founded recursion (§4) on the pair $`(b, \theta)`$. This pair $`(b, \theta)`$ is called a **stage**. The first component $`b`$ of a stage is called the **top**. The order $`\lhd`$ of stages is the lexicographic product of the order of labels and the order of keys.

```math
(b', \kappa') \lhd (b, \theta) \iff b' \lt b\ \lor\ (b' = b \land \kappa' \lt \theta)
```

$`b', b`$ are labels and $`\kappa', \theta`$ are keys. By the two theorems above, $`\lhd`$ is well-founded.

The following table was checked with Python.

| Two stages ($`m = 2`$) | Result | Reason |
|---|---|---|
| $`(5, (3, \top))`$ and $`(\omega, (0, 0))`$ | $`(5, (3, \top)) \lhd (\omega, (0, 0))`$ | $`5 \lt \omega`$ at the top |
| $`(\omega, (0, \top))`$ and $`(\omega, (1, 0))`$ | $`(\omega, (0, \top)) \lhd (\omega, (1, 0))`$ | equal tops, $`0 \lt 1`$ at coordinate 0 of the key |

## 4. Well-founded recursion

**Theorem (well-founded recursion).** Let $`\prec`$ be a well-founded relation on a set $`T`$. Let $`V`$ be a set of values. Suppose a rule $`G`$ takes $`t \in T`$ and "the values at arguments smaller than $`t`$" and returns the value at $`t`$. Then there is exactly one function $`F : T \to V`$ with the equation below. $`F{\restriction}X`$ is the restriction of $`F`$ to the set $`X`$.

```math
F(t) = G\bigl(t,\ F{\restriction}\{t' \mid t' \prec t\}\bigr)
```

**Proof outline.**

- At most one: for two solutions $`F, F'`$, show $`F(t) = F'(t)`$ by well-founded induction on $`t`$. If they agree below $`t`$, the right sides are the same, so they agree at $`t`$.
- At least one: call a function a partial solution if it satisfies the equation on a subset $`U`$ with "$`t' \prec t`$ and $`t \in U`$ imply $`t' \in U`$". Two partial solutions agree where both are defined (the same induction as above). All partial solutions together form one function. Show by well-founded induction that it is defined on all of $`T`$: if it is defined at every element below $`t`$, then adding the value at $`t`$ given by $`G`$ yields a partial solution. $`\square`$

**Example (the Ackermann function).** Give the set $`\mathbb N \times \mathbb N`$ of argument pairs $`(m, n)`$ the lexicographic order of §3.

```math
\begin{aligned}
A(0, n) &= n + 1, \cr
A(m+1, 0) &= A(m, 1), \cr
A(m+1, n+1) &= A\bigl(m,\ A(m+1, n)\bigr).
\end{aligned}
```

The arguments $`(m, 1)`$, $`(m+1, n)`$, $`(m, \cdot)`$ called on the right are all lexicographically smaller than the argument on the left. So well-founded recursion defines $`A`$.

The following values were computed with Python.

| $`A(m, n)`$ | $`n = 0`$ | $`n = 1`$ | $`n = 2`$ | $`n = 3`$ |
|---|---|---|---|---|
| $`m = 0`$ | 1 | 2 | 3 | 4 |
| $`m = 1`$ | 2 | 3 | 4 | 5 |
| $`m = 2`$ | 3 | 5 | 7 | 9 |
| $`m = 3`$ | 5 | 13 | 29 | 61 |

## 5. Guarded recursion

The rule $`G`$ of §4 can read only the values at arguments smaller than $`t`$. In the definition of $`R`$ in [07](07-relation-r.md), which stage (§3) is read depends on the values of variables that range inside the definition. So we cannot say in advance that the stage read is smaller. We therefore take the following three steps.

1. Where the right side reads the value at an argument $`t'`$, replace it by "$`t' \prec t`$, and the value at $`t'`$ is true". This condition $`t' \prec t`$ is called a **guard**. Where $`t' \prec t`$ fails, the expression is false. Then the right side reads only arguments smaller than $`t`$, so the theorem of §4 defines it.
2. Obtain the equation of §4. At this point the right side carries guards.
3. Show separately that the guards are always true where the right side actually reads. This gives the equation without guards.

When the values are numbers, the terms whose guard is false are dropped from the sum.

**Small example.** On $`\mathbb N`$ consider a definition of the form $`F(n) := 1 + \sum_{i \in S_n} F(i)`$. $`S_n`$ is a given finite set for each $`n`$, and it may contain numbers $`\ge n`$. As written this is not a well-founded recursion. With a guard it is defined by well-founded recursion:

```math
F(n) := 1 + \sum_{i \in S_n,\ i \lt n} F(i)
```

If $`S_n \subseteq \{0, \ldots, n-1\}`$ is shown separately, the equation without the guard, $`F(n) = 1 + \sum_{i \in S_n} F(i)`$, holds.

For example, let $`S_n = \{\lfloor n/2 \rfloor, n\}`$. The values of the guarded definition for $`n = 0, \ldots, 7`$ are $`1, 2, 3, 3, 4, 4, 4, 4`$ (computed with Python). This $`S_n`$ contains $`n`$. No $`F`$ satisfies the equation without the guard, $`F(n) = 1 + F(\lfloor n/2 \rfloor) + F(n)`$ ($`n \ge 1`$). In this example the guard cannot be removed.

## 6. Termination by a bound on labels

We show that a one-step relation $`\to`$ on a set of states $`X`$ is well-founded, using elements (labels) of a well-founded order $`(L, \lt)`$. Read $`s \to t`$ as "one step goes from $`s`$ to $`t`$". We say that $`\to`$ is well-founded if the reversed relation $`t \leftarrow s`$ is well-founded in the sense of §1, that is, if there is no infinite sequence $`s_0 \to s_1 \to s_2 \to \cdots`$.

**Theorem (termination by a bound on labels).** Suppose a relation $`\mathrm{valid}(s, \alpha)`$ between states $`s \in X`$ and labels $`\alpha \in L`$ satisfies:

- There is $`\alpha_0`$ with $`\mathrm{valid}(s, \alpha_0)`$ for every state $`s`$.
- If $`\mathrm{valid}(s, \alpha)`$ and $`s \to t`$, then $`\mathrm{valid}(t, \alpha')`$ for some $`\alpha' \lt \alpha`$.

Then $`\to`$ is well-founded: there is no infinite sequence $`s_0 \to s_1 \to s_2 \to \cdots`$.

**Proof.** By well-founded induction on $`\alpha`$, show "if $`\mathrm{valid}(s, \alpha)`$ then $`s`$ is accessible". Here accessible is in the sense of §1 for the reversed relation. If $`s \to t`$, then $`t`$ has some $`\alpha' \lt \alpha`$ with $`\mathrm{valid}(t, \alpha')`$. By the induction hypothesis $`t`$ is accessible. So $`s`$ is accessible. By the first condition every state is accessible. By the property of §1, $`\to`$ is well-founded. $`\square`$

The point is that a state need not have a unique label. We only use "$`\mathrm{valid}`$ holds for some label" and "after one step it holds for a smaller label".

The application to the expansion of the official ω-Y is written in [06](06-combinatorial-layer.md) §8.

## 7. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Status" | the final theorem is stated as well-foundedness of a one-step relation; its restatement "cannot go on forever" is the equivalence of §1 |
| [notes/00-survey.md](../../notes/00-survey.md) §3.2 (Japanese) | keys $`\mathrm{Key}_m`$ and $`\top`$; recursion on the lexicographic order of (top, key) (§3–§5) |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §2.3 (Japanese) | the order of stages and the stages read on the right side (§3, §5) |
| [notes/04-official-design.md](../../notes/04-official-design.md) §1.1 (Japanese) | termination by induction on the last label (§6) |
