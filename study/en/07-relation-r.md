[← Back](README.md) | [English](07-relation-r.md) | [Japanese](../07-relation-r.md)

# The relation R

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, successor ordinal, limit ordinal, label, $`\omega_1`$, position |
| [02 Well-founded relations and recursion](02-well-founded.md) | lexicographic order, well-founded recursion, guard, keys $`\mathrm{Key}_m`$, $`\top`$, coordinate, stage, top |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | structure $`(A; P_1, \ldots, P_k)`$, domain, height, point, $`\Sigma_1`$ formula, quantifier-free formula, parameter, witness, literal, $`\Sigma_1`$-elementary substructure $`\preccurlyeq_{\Sigma_1}`$, template, evaluation $`\mathrm{eval}\ t\ \vec v`$, monotonicity, internal relation $`\mathrm{Rel}_{t,i,j}`$, top predicate $`\mathrm{Top}_{t,i}`$, partial top predicates |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | the idea of making top predicates atomic symbols, demand |
| [06 The combinatorial layer and leg atoms](06-combinatorial-layer.md) | key weakening (the statement in §5) |

This note explains the definition of the label relation $`R`$ of this repository and the properties that follow directly from it. Key weakening, stated without proof in [06](06-combinatorial-layer.md) §5, is proved here.

## 1. Notation

- $`\mathrm{Label} = \{o \mid o \le \omega_1\}`$: the set of labels ([01](01-ordinals.md) §6). The arguments of this note use only that the order of labels is a well-ordered linear order.
- $`\mathrm{Key}_m`$: the set of keys of length $`m`$ ([02](02-well-founded.md) §3). The arguments of this note use only that the order of keys is a well-ordered linear order.
- $`R(\theta, a, b)`$: the relation for a key $`\theta`$, a lower point $`a`$ (a label) and an upper point $`b`$ (a label). $`b`$ is the top ([02](02-well-founded.md) §3).
- $`\vec v = (v_0, \ldots, v_{n-1})`$ is a tuple of labels. $`\vec v \lt a`$ means that every entry is below $`a`$. $`\vec w \le \vec v`$ means $`w_i \le v_i`$ for every $`i`$ (pointwise smaller).

## 2. The language

Here the symbols of the language of [03](03-sigma1-elementary.md) §7 get their meaning. There are three kinds of symbols. For each template $`t`$ over $`n`$ variables and positions $`i, j \lt n`$ there are the following.

| Symbol | Number of arguments | Meaning (in the structure of height $`c`$) |
|---|---|---|
| $`\lt`$ | 2 | the order of labels |
| $`\mathrm{Rel}_{t,i,j}`$ | $`n`$ | $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$ |
| $`\mathrm{Top}_{t,i}`$ | $`n`$ | $`\mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$ |

$`\mathrm{Rel}`$ is a relation between points, and $`\mathrm{Top}`$ a relation from a point to the top $`c`$ (the height of the structure). $`c`$ itself is not in the domain. Both symbols compute their key from the $`n`$ points by the template. $`\mathrm{Top}_{t,i}(\vec v)`$ is the demand $`R(\kappa, v_i, c)`$ of [04](04-patterns-of-resemblance.md) §4 ($`\kappa = \mathrm{eval}\ t\ \vec v`$) written as one atomic formula.

## 3. The structure 𝔄^c_θ

**Definition.** For a key $`\theta`$ and a label $`c`$, the structure $`\mathfrak A^c_\theta`$ of height $`c`$ is:

```math
\mathfrak A^c_\theta = \bigl(c;\ \lt,\ (\mathrm{Rel}_{t,i,j}),\ (\mathrm{Top}_{t,i})\bigr)
```

- The domain is $`\{x \mid x \lt c\}`$ and the order is $`\lt`$.
- $`\mathrm{Rel}_{t,i,j}`$ has the meaning of §2 for every template $`t`$.
- $`\mathrm{Top}_{t,i}(\vec v)`$ is defined only when $`\mathrm{eval}\ t\ \vec v \lt \theta`$, and then it has the meaning of §2. Where it is not defined, top literals are false, both positive and negative ones ([03](03-sigma1-elementary.md) §8).

**Example.** Consider templates over one variable $`v_0`$. A template puts the variable number $`0`$ or $`\top`$ at each coordinate of the key ([03](03-sigma1-elementary.md) §7). The table below gives the range of $`v_0`$ where the top predicate is defined. It was found by hand, by following the definitions, and also checked with Python (comparing $`v_0 \in \{0, 1, 2, 3, 4, 5, \omega, \omega + 1\}`$).

| key length | $`\theta`$ | template | key $`\mathrm{eval}\ t\ (v_0)`$ | defined range |
|---|---|---|---|---|
| $`m = 1`$ | $`(\omega)`$ | $`(0)`$ | $`(v_0)`$ | $`v_0 \lt \omega`$ ($`v_0`$ a natural number) |
| $`m = 1`$ | $`(\omega)`$ | $`(\top)`$ | $`(\top)`$ | nowhere |
| $`m = 1`$ | $`(\top)`$ | $`(0)`$ | $`(v_0)`$ | everywhere ($`v_0`$ is a label, so $`v_0 \lt \top`$) |
| $`m = 2`$ | $`(3, \omega)`$ | $`(0, \top)`$ | $`(v_0, \top)`$ | $`v_0 \lt 3`$ |
| $`m = 2`$ | $`(3, \omega)`$ | $`(0, 0)`$ | $`(v_0, v_0)`$ | $`v_0 \le 3`$ |
| $`m = 2`$ | $`(3, \omega)`$ | $`(\top, 0)`$ | $`(\top, v_0)`$ | nowhere |

In the second row for $`m = 2`$, when $`v_0 = 3`$ the coordinate 0 is equal, and at coordinate 1 we have $`3 \lt \omega`$, so the predicate is defined.

## 4. Definition

**Definition (R).**

```math
R(\theta, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

The two structures have different top predicates ($`R`$ to $`a`$ and $`R`$ to $`b`$). So, as in [03](03-sigma1-elementary.md) §8, $`\preccurlyeq_{\Sigma_1}`$ here means the following: for every $`\Sigma_1`$ formula $`\varphi`$ and all parameters $`\vec p \lt a`$,

```math
\mathfrak A^{a}_{\theta} \models \varphi(\vec p) \iff \mathfrak A^{b}_{\theta} \models \varphi(\vec p)
```

Applied to quantifier-free formulas, this says that at points below $`a`$ the atomic formulas of the two structures have the same truth values. The top predicates also agree where they are defined.

## 5. Recursion

The right side reads $`R`$ itself. The definition uses well-founded recursion on the lexicographic order $`\lhd`$ of the stages $`(b, \theta)`$ (pairs of a top and a key, [02](02-well-founded.md) §3). At one stage $`(b, \theta)`$ it defines the relation for all $`a`$ at once.

**What the right side reads.** Only three kinds, all at smaller stages.

| Read | Stage | Why smaller |
|---|---|---|
| internal relation $`\mathrm{Rel}(\vec v)`$, that is, $`R(\kappa, x, y)`$ | $`(y, \kappa)`$ | points are below the height ($`a`$ or $`b`$), so $`y \lt b`$ |
| top predicate of $`\mathfrak A^{a}_\theta`$, $`R(\kappa, x, a)`$ | $`(a, \kappa)`$ | $`a \lt b`$ |
| top predicate of $`\mathfrak A^{b}_\theta`$, $`R(\kappa, x, b)`$ | $`(b, \kappa)`$ | defined only when $`\kappa \lt \theta`$ |

The third row is the key point. Since the top predicates of $`\mathfrak A^{b}_\theta`$ are defined only below the key $`\theta`$, the right side does not read the stage $`(b, \theta)`$ itself.

**The recursive formula.** At the stage $`(b, \theta)`$, assume $`R`$ is already fixed at all stages smaller than $`(b, \theta)`$. Every place that reads $`R`$ gets a guard ([02](02-well-founded.md) §5). When the guard is false, $`R`$ is not read and the value is false.

| Interpretation | Formula |
|---|---|
| internal relation | $`\mathrm{rel}(\kappa, x, y) :\iff y \lt b \text{ and } R(\kappa, x, y)`$ |
| top at height $`a`$ | $`\mathrm{top}_A(\kappa, x) :\iff R(\kappa, x, a)`$ (the guard $`a \lt b`$ is required at the head of the formula below) |
| top at height $`b`$ | $`\mathrm{top}_B(\kappa, x) :\iff \kappa \lt \theta \text{ and } R(\kappa, x, b)`$ |

Let $`\mathfrak C^{a}`$ be the structure of height $`a`$ that interprets the internal relations by $`\mathrm{rel}`$ and the top predicates by $`\mathrm{top}_A`$, with the top predicates defined only for keys $`\lt \theta`$. Let $`\mathfrak C^{b}`$ be the structure of height $`b`$ that interprets the internal relations by $`\mathrm{rel}`$ and the top predicates by $`\mathrm{top}_B`$, again defined only for keys $`\lt \theta`$. The definition at the stage $`(b, \theta)`$ is:

```math
R(\theta, a, b) :\iff a \lt b \ \land\ \mathfrak C^{a} \preccurlyeq_{\Sigma_1} \mathfrak C^{b}
```

Because of the guards, this formula reads $`R`$ only at stages smaller than $`(b, \theta)`$. So well-founded recursion fixes $`R`$.

## 6. The formula without guards

The proof uses Property 5 of [03](03-sigma1-elementary.md) §8 (only what is read matters): if two interpretations of a structure of height $`c`$ agree on the internal relations between points below $`c`$ and on the top predicates with keys $`\lt \theta`$ at points below $`c`$, then every formula has the same truth value in both.

**Theorem (the defining formula).**

```math
R(\theta, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

The two structures on the right have the true interpretations of §3 (without guards).

**Proof.** By the defining equation of well-founded recursion, the left side is equivalent to $`a \lt b \land \mathfrak C^{a} \preccurlyeq_{\Sigma_1} \mathfrak C^{b}`$. Assume $`a \lt b`$. We show that $`\mathfrak C^{a}`$ and $`\mathfrak A^{a}_\theta`$, and $`\mathfrak C^{b}`$ and $`\mathfrak A^{b}_\theta`$, satisfy the condition of this property.

1. Internal relations: they are read only where the second point $`y`$ is below the height. The height is $`a`$ or $`b`$, both at most $`b`$, so the guard $`y \lt b`$ is true.
2. Top at height $`a`$: the guard is $`a \lt b`$, which is the assumption itself.
3. Top at height $`b`$: it is read only at keys $`\kappa \lt \theta`$. There the guard $`\kappa \lt \theta`$ is true.

By Property 5, every $`\Sigma_1`$ formula with parameters below $`a`$ has the same truth value in $`\mathfrak C^{a}`$ and $`\mathfrak A^{a}_\theta`$, and in $`\mathfrak C^{b}`$ and $`\mathfrak A^{b}_\theta`$. So the two $`\preccurlyeq_{\Sigma_1}`$ are equivalent. $`\square`$

From here on, only this defining formula is used.

## 7. Properties that follow directly from the definition

**Property 1.** If $`R(\theta, a, b)`$ then $`a \lt b`$. This is the first conjunct of the defining formula.

**Theorem (key weakening).** If $`\theta \le \Theta`$ and $`R(\Theta, a, b)`$, then $`R(\theta, a, b)`$.

The proof uses two facts.

- Fact A: let $`\theta \le \Theta`$. A literal that holds in a structure whose top predicates are defined for keys $`\lt \theta`$ also holds, with the same interpretation, in the structure whose top predicates are defined for keys $`\lt \Theta`$. If a top literal holds, its key is below $`\theta`$, hence below $`\Theta`$. The other literals do not read the defined range.
- Fact B (Property 4 of [03](03-sigma1-elementary.md) §8): if $`\vec w \le \vec v`$ and $`\mathrm{eval}\ t\ \vec v \lt \theta`$, then $`\mathrm{eval}\ t\ \vec w \le \mathrm{eval}\ t\ \vec v \lt \theta`$. This is the monotonicity of evaluation.

**Proof.** By the defining formula, $`a \lt b`$ and $`\mathfrak A^{a}_{\Theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\Theta}`$. For a $`\Sigma_1`$ formula $`\varphi`$ and parameters $`\vec p \lt a`$, we show both directions.

- From below to above: let $`\mathfrak A^{a}_\theta \models \varphi(\vec p)`$ with witness $`\vec w \lt a`$. Make the formula $`\varphi'`$ in which every variable is a parameter. The parameter values are the original parameters $`\vec p`$ and the witness $`\vec w`$. By Fact A, $`\mathfrak A^{a}_\Theta \models \varphi'`$. By elementarity at the key $`\Theta`$, $`\mathfrak A^{b}_\Theta \models \varphi'`$. $`\varphi'`$ has no quantifier, so the literals hold at the same points. The key of a top literal depends only on the points, and it was defined in $`\mathfrak A^{a}_\theta`$, so it is below $`\theta`$. Hence it is also defined in $`\mathfrak A^{b}_\theta`$ and holds there. $`\vec w`$ is a witness in $`\mathfrak A^{b}_\theta`$.
- From above to below: let $`\mathfrak A^{b}_\theta \models \varphi(\vec p)`$ with witness $`\vec v \lt b`$. Make the formula $`\varphi'`$ in which every position whose value is below $`a`$ is a parameter. The original parameters $`\vec p`$ are below $`a`$, so their positions stay parameters. By Fact A, $`\mathfrak A^{b}_\Theta \models \varphi'`$. By elementarity at the key $`\Theta`$, there is a witness $`\vec w \lt a`$ in $`\mathfrak A^{a}_\Theta`$. At positions whose value is below $`a`$, $`w_i = v_i`$. At the other positions, $`w_i \lt a \le v_i`$. So $`\vec w \le \vec v`$. Each top literal was defined at $`\vec v`$ in $`\mathfrak A^{b}_\theta`$, so its key is below $`\theta`$. By Fact B, its key at $`\vec w`$ is also below $`\theta`$. Hence it is also defined in $`\mathfrak A^{a}_\theta`$ and has the same truth value as in $`\mathfrak A^{a}_\Theta`$. $`\vec w`$ is a witness in $`\mathfrak A^{a}_\theta`$. $`\square`$

The second direction needs lowering the witness pointwise. This is where the monotonicity of evaluation is used.

**Property 2 (defined top predicates agree).** Let $`R(\theta, a, b)`$ and $`\vec v \lt a`$. If $`\mathrm{eval}\ t\ \vec v \lt \theta`$, then:

```math
R(\mathrm{eval}\ t\ \vec v,\ v_i,\ a) \iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ b)
```

**Reason.** Use the formula $`\mathrm{Top}_{t,i}(\vec v)`$ in which every variable is a parameter. At height $`a`$ it means the left side, and at height $`b`$ the right side. By the elementarity of §4 they are equivalent. The main line of the proof does not use this property. [09](09-obligations.md) §3.1 proves a property of a similar form.

**Property 3 (the lower point is a limit ordinal).** If $`R(\theta, a, b)`$, then $`a`$ is a nonzero limit ordinal.

**Reason.** The same as the example of [03](03-sigma1-elementary.md) §5.

- If $`a = 0`$: $`\exists v_0\ \neg(v_0 \lt v_0)`$, with no parameter, is true at height $`b`$ and false at height 0.
- If $`a = \gamma + 1`$: $`\exists v_1\ (\gamma \lt v_1)`$ with parameter $`\gamma \lt a`$ is true at height $`b`$ ($`v_1 = \gamma + 1 \lt b`$) and false at height $`a`$.

Both contradict elementarity. The main line of the proof does not use this property.

## 8. A property that is not used

**Transitivity.** $`R(\theta, a, b) \land R(\theta, b, c) \implies R(\theta, a, c)`$. The middle structure $`\mathfrak A^b_\theta`$ is the same in the two relations, so for formulas with parameters $`\vec p \lt a`$ the two equivalences can be chained. The proof does not use this property.

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) introduction | Phyrion's reflection theorem is used as it is. The relation $`R`$ and key weakening that the theorem needs are given by the definition of this note |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §1 (Japanese) | the relation $`R`$ and key weakening used by the combinatorial layer |
| [notes/02-wmwy-design.md](../../notes/02-wmwy-design.md) §2, §3.1 (Japanese) | structures, definition, stages of the recursion, proof of key weakening |
