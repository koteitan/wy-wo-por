[← Back](README.md) | [English](en/01-ordinals.md) | [Japanese](01-ordinals.md)

# 順序数と ω₁

前提

| ノート | ここで使う言葉 |
|---|---|
| なし | なし |

このノートは、順序数と $`\omega_1`$ を説明する。あとのノートでは 2 種類の順序数を使う。1 つは山の行に使う $`\omega^\omega`$ より小さい順序数である（[05](05-omegay-mountain.md)）。もう 1 つは列に付けるラベルに使う $`\omega_1`$ 以下の順序数である（§6）。あとで使う事実は、§1 の係数と和、§5 の正則性、§6 のラベル、§7 の数え方である。

## 1. 整列順序と順序数

**定義（整列順序）.** 集合 $`X`$ の上の全順序 $`\lt`$ が **整列順序** であるとは、$`X`$ の空でない部分集合がどれも最小元を持つことをいう。

**定義（無限降下列）.** $`x_0 \gt x_1 \gt x_2 \gt \cdots`$ となる列 $`(x_n)_{n \in \mathbb N}`$ を **無限降下列** と呼ぶ。

全順序が整列順序であることと、無限降下列が無いことは同値である。「無限降下列が無いなら整列順序」の向きには、選択公理の弱い形（従属選択）を使う。

| 順序 | 整列か | 理由 |
|---|---|---|
| $`(\mathbb N, \lt)`$ | はい | 空でない部分集合は最小元を持つ |
| $`(\mathbb Z, \lt)`$ | いいえ | $`0 \gt -1 \gt -2 \gt \cdots`$ |
| $`(\mathbb Q_{\ge 0}, \lt)`$ | いいえ | $`1 \gt 1/2 \gt 1/4 \gt \cdots`$ |

**定義（順序数）.** **順序数** は整列順序の型である。順序数 $`\alpha`$ は、それより小さい順序数の集合 $`\{\beta \mid \beta \lt \alpha\}`$ と同一視する。

小さい順に並べると次のようになる。

```math
0,\ 1,\ 2,\ \ldots,\ \omega,\ \omega+1,\ \omega+2,\ \ldots,\ \omega \cdot 2,\ \ldots,\ \omega^2,\ \ldots,\ \omega^\omega,\ \ldots
```

- $`\omega`$ は自然数全体の型である。$`\omega = \{0, 1, 2, \ldots\}`$。
- 順序数の全体は $`\lt`$ で整列する。空でない順序数の集まりには、どれも最小元がある。

**定義（和）.** 順序数の和 $`\alpha + \beta`$ は、$`\alpha`$ の型の整列順序の後ろに $`\beta`$ の型の整列順序を並べた整列順序の型である。

例：$`2 + \omega`$ は $`0, 1`$ の後ろに $`\omega`$ の型の列を並べた型である。これは $`\omega`$ の型と同じなので、$`2 + \omega = \omega`$ である。一方 $`\omega + 2 \gt \omega`$ である。和は交換できない。

### Cantor の標準形

**定理（Cantor の標準形）.** $`\omega^\omega`$ より小さい順序数 $`\alpha`$ は、自然数 $`d`$ と自然数 $`c_0, \ldots, c_d`$ を使って、次の形にただ 1 通りに書ける。ただし $`\alpha \ne 0`$ なら $`c_d \ne 0`$ とし、$`\alpha = 0`$ なら $`d = 0`$、$`c_0 = 0`$ とする。

```math
\alpha = \omega^d \cdot c_d + \cdots + \omega \cdot c_1 + c_0
```

この定理はここでは証明しない。順序数の教科書にある。

**定義（係数）.** 上の形のとき、$`k \le d`$ なら $`c_k(\alpha) := c_k`$、$`k \gt d`$ なら $`c_k(\alpha) := 0`$ とする。$`c_k(\alpha)`$ を $`\alpha`$ の **$`k`$ 次の係数** と呼ぶ。

**定義（次数）.** $`\alpha \ne 0`$ のとき、$`\alpha`$ の **次数** $`\deg \alpha`$ は、$`c_k(\alpha) \ne 0`$ となる最大の $`k`$ である。$`\deg 0 = 0`$ とする。

| $`\alpha`$ | $`c_2(\alpha)`$ | $`c_1(\alpha)`$ | $`c_0(\alpha)`$ | $`\deg \alpha`$ |
|---|---|---|---|---|
| $`\omega^2 \cdot 2 + 3`$ | 2 | 0 | 3 | 2 |
| $`\omega`$ | 0 | 1 | 0 | 1 |
| $`7`$ | 0 | 0 | 7 | 0 |
| $`0`$ | 0 | 0 | 0 | 0 |

**比べ方.** $`\alpha \ne \beta`$ とし、$`c_k(\alpha) \ne c_k(\beta)`$ となる最大の $`k`$ を取る。このとき $`\alpha \lt \beta \iff c_k(\alpha) \lt c_k(\beta)`$ である。

次の例は Python で計算した。

| 比べる 2 つ | 結果 | 係数が違う最大の $`k`$ |
|---|---|---|
| $`\omega \cdot 2 + 5`$ と $`\omega^2`$ | $`\omega \cdot 2 + 5 \lt \omega^2`$ | 2 |
| $`\omega^2 \cdot 2 + 3`$ と $`\omega^2 \cdot 2 + \omega`$ | $`\omega^2 \cdot 2 + 3 \lt \omega^2 \cdot 2 + \omega`$ | 1 |
| $`7`$ と $`\omega`$ | $`7 \lt \omega`$ | 1 |

**和 $`\alpha + \omega^e`$.** $`e`$ を自然数とする。$`k \lt e`$ なら $`\omega^k \cdot c + \omega^e = \omega^e`$ である（$`2 + \omega = \omega`$ と同じ理由）。そのため、$`\alpha + \omega^e`$ では $`e`$ 次より下の係数が消える。

```math
c_k(\alpha + \omega^e) = \begin{cases} 0 & (k \lt e) \cr c_e(\alpha) + 1 & (k = e) \cr c_k(\alpha) & (k \gt e) \end{cases}
```

次の例は Python で計算した。

| $`\alpha`$ | $`e`$ | $`\alpha + \omega^e`$ |
|---|---|---|
| $`2`$ | 1 | $`\omega`$ |
| $`\omega`$ | 2 | $`\omega^2`$ |
| $`\omega^2 \cdot 2 + \omega + 3`$ | 0 | $`\omega^2 \cdot 2 + \omega + 4`$ |
| $`\omega^2 \cdot 2 + \omega + 3`$ | 1 | $`\omega^2 \cdot 2 + \omega \cdot 2`$ |
| $`\omega^2 \cdot 2 + \omega + 3`$ | 3 | $`\omega^3`$ |

## 2. 後者と極限

**定義（後者）.** $`\alpha + 1`$ は $`\alpha`$ の次の順序数である。$`\alpha + 1`$ の形の順序数を **後者順序数** と呼ぶ。

**定義（極限順序数）.** 0 でも後者順序数でもない順序数を **極限順序数** と呼ぶ。

| 順序数 | 種類 |
|---|---|
| $`0`$ | どちらでもない |
| $`5`$、$`\omega+1`$、$`\omega \cdot 2 + 3`$ | 後者 |
| $`\omega`$、$`\omega \cdot 2`$、$`\omega^2`$ | 極限 |

**性質.** $`\alpha`$ が極限順序数で $`\beta \lt \alpha`$ なら、$`\beta + 1 \lt \alpha`$ である。したがって $`\beta`$ より上に、$`\alpha`$ より下の元が無限個ある。

この性質は [03](03-sigma1-elementary.md) §5 の例で使う。

## 3. 上限

**定義（上限）.** 順序数の集合 $`S`$ の **上限** $`\sup S`$ は、$`S`$ のすべての元以上である最小の順序数である。

- $`S`$ が最大元を持てば、$`\sup S`$ はその最大元である。空でない有限集合ならいつもそうである。空集合の上限は $`0`$ である。
- $`S`$ が最大元を持たなければ、$`\sup S`$ は $`S`$ に入らない。

| $`S`$ | $`\sup S`$ |
|---|---|
| $`\{2, 5, 3\}`$ | $`5`$ |
| $`\{0, 1, 2, \ldots\}`$ | $`\omega`$ |
| $`\{\omega, \omega+1, \omega+2, \ldots\}`$ | $`\omega \cdot 2`$ |

「すべての元より真に大きい」数が欲しいときは、$`\sup_{i} (y_i + 1)`$ を使う。$`y_i \lt y_i + 1 \le \sup_i (y_i + 1)`$ だからである。[08](08-closure-chain.md) §3 はこの形の上限を使う。

## 4. 可算と ω₁

**定義（可算）.** 集合 $`X`$ が **可算** であるとは、$`X`$ が空であるか、全射 $`\mathbb N \to X`$ があることをいう。

**定義（可算順序数）.** 順序数 $`\alpha`$ が **可算** であるとは、$`\{\beta \mid \beta \lt \alpha\}`$ が可算であることをいう。

$`0, 1, \omega, \omega+1, \omega \cdot 2, \omega^2, \omega^\omega`$ はどれも可算である。

**定義（ω₁）.** $`\omega_1`$ は最初の非可算順序数である。つまり、$`\omega_1`$ より小さい順序数はちょうど可算順序数である。

```math
\alpha \lt \omega_1 \iff \alpha \text{ は可算}
```

次の 3 つを使う。

- $`0 \lt \omega_1`$。
- $`\alpha \lt \omega_1 \implies \alpha + 1 \lt \omega_1`$。
- $`\gamma \lt \omega_1 \implies \{\beta \mid \beta \lt \gamma\}`$ は可算。

2 つめの理由：$`\{\beta \mid \beta \lt \alpha + 1\} = \{\beta \mid \beta \lt \alpha\} \cup \{\alpha\}`$ で、可算集合に 1 点を足しても可算である。言いかえると、$`\omega_1`$ は極限順序数である。

## 5. ω₁ の正則性

**定理（ω₁ の正則性）.** 可算な集合 $`I`$ と、各 $`i \in I`$ について $`\alpha_i \lt \omega_1`$ があるとする。このとき次が成り立つ。

```math
\sup_{i \in I} \alpha_i \lt \omega_1
```

言いかえると、可算個の可算順序数の上限は $`\omega_1`$ より小さい。

**証明.** $`\sigma := \sup_i \alpha_i`$ と置く。$`\beta \lt \sigma`$ なら、ある $`i`$ で $`\beta \lt \alpha_i`$ である。よって

```math
\{\beta \mid \beta \lt \sigma\} = \bigcup_{i \in I} \{\beta \mid \beta \lt \alpha_i\}
```

である。右辺は可算集合の可算個の和である。$`\alpha_i = 0`$ の項は和に何も足さないので除く。残りの各 $`i`$ で全射 $`e_i : \mathbb N \to \{\beta \mid \beta \lt \alpha_i\}`$ を 1 つずつ選ぶ。$`I`$ を $`\mathbb N`$ で数え上げ、$`n`$ 番目の元を $`i_n`$ と書く。すると $`(n, t) \mapsto e_{i_n}(t)`$ は $`\mathbb N \times \mathbb N`$ から和の上への全射になる。$`\mathbb N \times \mathbb N`$ は可算なので、和も可算である。よって $`\sigma`$ は可算で、$`\sigma \lt \omega_1`$ である。$`\square`$

- 全射 $`e_i`$ を可算個同時に選ぶところで、選択公理（可算選択）を使う。
- $`I`$ が非可算なら成り立たない。例えば $`\sup_{\alpha \lt \omega_1} \alpha = \omega_1`$ である。

## 6. ラベル

**定義（ラベル）.** $`\omega_1`$ 以下の順序数を **ラベル** と呼ぶ。

```math
\mathrm{Label} = \{\, o \mid o \le \omega_1 \,\}
```

ラベルの順序は順序数の順序である。これは整列順序である。最大のラベルは $`\omega_1`$ である。

- $`0 \lt \omega_1`$ なので、$`\omega_1`$ より小さいラベルがある。
- $`a \lt \omega_1`$ なら、$`a`$ より小さいラベルの集合 $`\{x \mid x \lt a\}`$ は可算である（§4）。

**なぜ ω₁ 自身をラベルに入れるか.** あとのノートでは、有限個のラベルを $`\omega_1`$ より小さく選んで、列に付ける。一方で、2 つのラベル $`x \lt b`$ の間の条件を、$`b = \omega_1`$ の場合にも考える（[08](08-closure-chain.md)、[09](09-obligations.md)）。そのために、$`\omega_1`$ も同じ集合 $`\mathrm{Label}`$ に入れる。

## 7. パラメータの数え方

あとのノート（[08](08-closure-chain.md)）では、有限個の番号の付いた場所に $`\gamma`$ より下の順序数を置いた組の全体について、上限を取る。ここでは、その組の集合が可算であることを示す。そこに置いた順序数は、[03](03-sigma1-elementary.md) §2 でパラメータと呼ぶ。

記号を決める。

- 自然数 $`n`$ について、$`\{0, \ldots, n-1\}`$ は $`n`$ 個の番号の集合である。$`n = 0`$ なら空集合である。
- 集合 $`X`$ について、$`X \cup \{\mathrm{none}\}`$ は、$`X`$ に新しい元 $`\mathrm{none}`$ を 1 つ足した集合である。$`\mathrm{none}`$ は $`X`$ の元ではない。$`\mathrm{none}`$ は「何も置かない」ことを表す。
- 集合 $`\Phi`$ と、各 $`\varphi \in \Phi`$ ごとの集合 $`X_\varphi`$ について、**依存和** を $`\sum_{\varphi \in \Phi} X_\varphi = \{(\varphi, q) \mid \varphi \in \Phi,\ q \in X_\varphi\}`$ とする。
- $`\Phi`$ を集合とし、各 $`\varphi \in \Phi`$ に自然数 $`n_\varphi`$ が決まっているとする。$`\{0, \ldots, n_\varphi - 1\}`$ の元を $`\varphi`$ の **位置** と呼ぶ。

**定義（入力の集合）.** $`\gamma`$ を順序数とする。**入力の集合** を次で定める。

```math
\mathrm{In}(\gamma) = \sum_{\varphi \in \Phi} \Bigl(\{0, \ldots, n_\varphi - 1\} \to \{\, x \mid x \lt \gamma \,\} \cup \{\mathrm{none}\}\Bigr)
```

右辺の $`A \to B`$ は、$`A`$ から $`B`$ への関数の集合である。入力 $`(\varphi, q)`$ は、$`\varphi`$ の各位置に、$`\gamma`$ より下の順序数を置くか、何も置かない（$`\mathrm{none}`$）。

**定理（入力の集合は可算）.** $`\Phi`$ が可算で $`\gamma \lt \omega_1`$ なら、$`\mathrm{In}(\gamma)`$ は可算である。

**証明.**

- $`Y := \{x \mid x \lt \gamma\} \cup \{\mathrm{none}\}`$ は可算である。$`\{x \mid x \lt \gamma\}`$ は可算で（§4）、1 点を足しても可算だからである。
- 可算な集合の上の有限の関数は可算個である。つまり $`\{0, \ldots, n-1\} \to Y`$ は可算である。この集合は $`Y`$ の $`n`$ 個の積 $`Y^n`$ と同じもので、可算集合の有限個の積は可算だからである。
- 可算な $`\Phi`$ の上の、可算な集合の依存和は可算である。可算個の可算集合の和だからである（§5 の証明と同じく、可算選択を使う）。$`\square`$

**例（手で求めた）.** $`\gamma = \omega + 1`$ とし、$`n_\varphi = 3`$ とする。位置 0 に $`3`$ を置き、位置 1 に何も置かず、位置 2 に $`\omega`$ を置く入力は $`(\varphi, q)`$ で、$`q(0) = 3`$、$`q(1) = \mathrm{none}`$、$`q(2) = \omega`$ である。$`3 \lt \gamma`$、$`\omega \lt \gamma`$ なので、これは $`\mathrm{In}(\gamma)`$ の元である。

1-Y 版の study（[koteitan/1y-wo-por の study/](https://github.com/koteitan/1y-wo-por/tree/main/study)）は、$`\gamma`$ より下の順序数を自然数で数え上げて、組の集合を $`\gamma`$ に依らないものにした。このリポジトリは、順序数をそのまま位置に置く。組の集合は $`\gamma`$ に依るが、可算なので、§5 の定理をそのまま使える。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [notes/00-survey.md](../notes/00-survey.md) §1.3 | 山の行は $`\omega^\omega`$ より小さい順序数で、係数で書く（§1） |
| [notes/03-official-rule.md](../notes/03-official-rule.md) §1.1 | $`k`$ 次の係数、和 $`\rho + \omega^e`$ で $`e`$ 次より下の係数が消えること（§1） |
| [notes/00-survey.md](../notes/00-survey.md) §3.2 | ラベルは $`\omega_1`$ 以下の順序数（§6） |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §3.3 | 可算個の論理式、$`\omega`$ 回のくり返し、上限が $`\omega_1`$ より小さいこと（§3〜§5、§7） |
