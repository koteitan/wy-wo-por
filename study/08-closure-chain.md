[← Back](README.md) | [English](en/08-closure-chain.md) | [Japanese](08-closure-chain.md)

# ω₁ より下の閉包と Good な点の列

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、上限、可算、$`\omega_1`$、$`\omega_1`$ の正則性、ラベル、$`\{0, \ldots, n-1\}`$、none を足した集合、位置、入力の集合 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 構造、領域、高さ、論理式、$`\Sigma_1`$ 論理式、パラメータ、証人、リテラル、部分構造、$`\preccurlyeq_{\Sigma_1}`$、Tarski–Vaught の判定法、型板、評価 $`\mathrm{eval}\ t\ \vec v`$ |
| [07 関係 R](07-relation-r.md) | 関係 $`R`$、構造 $`\mathfrak A^c_\theta`$、$`\mathrm{Rel}_{t,i,j}`$、$`\mathrm{Top}_{t,i}`$、$`\vec p \lt a`$ |

このノートは、$`\omega_1`$ より下に、$`\Sigma_1`$ 論理式の証人で閉じた点（§1 の Good な点）を作る方法を説明する。これは Löwenheim–Skolem の定理と同じ考え方で、証人を足して上限を取る。できた点を並べた列が、[09](09-obligations.md) で最初のラベルになる。

鍵の長さ $`m`$ は 1 つに固定する。

## 1. 周りの構造と Good

**定義（周りの構造）.** 高さ $`\omega_1`$ で、上端の述語をすべての鍵で定義した構造を $`\mathfrak B`$ とする。記号 $`\mathrm{Rel}_{t,i,j}`$、$`\mathrm{Top}_{t,i}`$ は [07](07-relation-r.md) §2 のものである。

```math
\mathfrak B = \bigl(\omega_1;\ \lt,\ (\mathrm{Rel}_{t,i,j}),\ (\mathrm{Top}_{t,i})\bigr), \qquad \mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ \omega_1)
```

$`\mathrm{Rel}_{t,i,j}`$ は [07](07-relation-r.md) §2 の意味を持つ。$`\omega_1`$ はラベルなので（[01](01-ordinals.md) §6）、$`R(\kappa, x, \omega_1)`$ は意味を持つ。[07](07-relation-r.md) §3 の $`\mathfrak A^{\omega_1}_\theta`$ と違い、上端の述語はどの鍵でも定義されている。

**定義（Good）.** $`\alpha`$ をラベルとする。$`\mathfrak B{\restriction}\alpha`$ を、$`\mathfrak B`$ の領域を $`\{x \mid x \lt \alpha\}`$ に制限したものとする。上端の述語は $`\omega_1`$ へのもののままである。ラベル $`\alpha`$ が **Good** であるとは、次が成り立つことをいう。$`\varphi`$ は $`\Sigma_1`$ 論理式、$`\vec p \lt \alpha`$ はパラメータを動く。

```math
\mathrm{Good}(\alpha) :\iff \forall \varphi\ \forall \vec p \lt \alpha\ \bigl(\mathfrak B \models \varphi(\vec p) \implies \mathfrak B{\restriction}\alpha \models \varphi(\vec p)\bigr)
```

$`\mathfrak B{\restriction}\alpha`$ は $`\mathfrak B`$ の部分構造である（解釈が同じで、領域だけが違う）。逆向きの含意はいつも成り立つ（[03](03-sigma1-elementary.md) §4 の上への保存）。したがって [03](03-sigma1-elementary.md) §6 の Tarski–Vaught の判定法から、$`\mathrm{Good}(\alpha)`$ は $`\mathfrak B{\restriction}\alpha \preccurlyeq_{\Sigma_1} \mathfrak B`$ と同じである。Good な点は、$`\mathfrak B`$ で真の $`\Sigma_1`$ の主張の証人を、自分より下に持つ。

## 2. 論理式は可算個

**定理.** この言語の論理式の全体は可算である。

**証明.** 論理式は、次の記号の有限列である。

| 記号 | 個数 |
|---|---|
| 変数 $`v_0, v_1, \ldots`$ | 可算個 |
| $`\lt`$、論理の記号（$`\neg, \land, \lor, \to, \exists, \forall`$）、かっこ | 有限個 |
| $`n`$ 変数の型板 $`t`$ と位置 $`i, j \lt n`$ の $`\mathrm{Rel}_{t,i,j}`$、$`\mathrm{Top}_{t,i}`$ | 各 $`n`$ で有限個 |

$`n`$ 変数の型板は、長さ $`m`$ の鍵の各座標に $`\{0, \ldots, n-1\}`$ の番号か $`\top`$ を置いたものである（[03](03-sigma1-elementary.md) §7）。その個数は $`(n+1)^m`$ で有限である。よって記号は可算個である。可算な集合の元の有限列の全体は可算である。$`\square`$

型板の全体が可算であることが要る。1 つの論理式は有限個の型板しか使わないが、論理式の全体が可算であるためには、型板の全体が可算でなければならない。

## 3. 証人の高さ

**定義（証人の高さ）.** $`\Sigma_1`$ 論理式 $`\varphi = \exists \vec y\ \psi(\vec p, \vec y)`$ と、パラメータ $`\vec p \lt \omega_1`$ について、**証人の高さ** $`H(\varphi, \vec p)`$ を次で定める。

- $`\mathfrak B \models \varphi(\vec p)`$ なら、証人 $`\vec y = (y_1, \ldots, y_k)`$ を 1 組選び、$`H(\varphi, \vec p) := \sup_{j} (y_j + 1)`$ とする。$`k = 0`$ なら $`0`$ とする。
- そうでなければ $`H(\varphi, \vec p) := 0`$ とする。

$`H(\varphi, \vec p)`$ は、選んだ証人をすべて領域に含む構造の高さのうち、最小のものである。証人の選び方は $`(\varphi, \vec p)`$ ごとに 1 つに決めておく。すべての $`(\varphi, \vec p)`$ について一度に選ぶので、選択公理を使う。

| 性質 | 内容 | 理由 |
|---|---|---|
| 性質 1 | $`H(\varphi, \vec p) \lt \omega_1`$ | 有限個の $`y_j + 1 \lt \omega_1`$ の上限である（[01](01-ordinals.md) §5） |
| 性質 2 | 選んだ証人は、どれも $`H(\varphi, \vec p)`$ より下 | $`y_j \lt y_j + 1 \le H(\varphi, \vec p)`$ |

## 4. 閉包の 1 歩

入力の集合 $`\mathrm{In}(\gamma)`$（[01](01-ordinals.md) §7）の元 $`q`$ は、$`\Sigma_1`$ 論理式 $`\varphi_q`$ と、$`\varphi_q`$ の各位置に $`\gamma`$ より下のラベルか none を置く関数の組である。$`q`$ がパラメータの位置に置いた値を $`\vec p_q`$ とする（none のところは 0 とする）。

**補題.** $`\gamma \lt \omega_1`$ なら、$`\mathrm{In}(\gamma)`$ は可算である。

**証明.** §2 から、$`\Sigma_1`$ 論理式の集合 $`\Phi`$ は可算である。[01](01-ordinals.md) §7 の定理（入力の集合は可算）を当てはめる。$`\square`$

**定義（閉包の 1 歩）.** $`\gamma \lt \omega_1`$ について、次で定める。

```math
N(\gamma) := \max\Bigl(\gamma + 1,\ \sup_{q \in \mathrm{In}(\gamma)} H\bigl(\varphi_q, \vec p_q\bigr)\Bigr)
```

上限は、$`\gamma`$ より下のパラメータを持つすべての論理式を動く。

| 性質 | 内容 | 理由 |
|---|---|---|
| 性質 3 | $`\gamma \lt N(\gamma)`$ | $`\gamma + 1`$ の項 |
| 性質 4 | $`N(\gamma) \lt \omega_1`$ | 補題から可算個の上限で、各項は性質 1 から $`\omega_1`$ より下。$`\omega_1`$ の正則性（[01](01-ordinals.md) §5） |
| 性質 5 | $`\vec p \lt \gamma`$ で $`\mathfrak B \models \varphi(\vec p)`$ なら、$`\mathfrak B{\restriction}N(\gamma) \models \varphi(\vec p)`$ | 下の証明 |

**性質 5 の証明.** パラメータの位置に $`\vec p`$ の値、ほかの位置に none を置いた入力 $`q \in \mathrm{In}(\gamma)`$ を作る。$`\varphi_q = \varphi`$、$`\vec p_q = \vec p`$ である。$`q`$ について選んだ証人は $`H(\varphi, \vec p)`$ より下にある（性質 2）。$`H(\varphi, \vec p)`$ は上限の項の 1 つなので、$`N(\gamma)`$ 以下である。よって証人は $`N(\gamma)`$ より下にあり、$`\mathfrak B{\restriction}N(\gamma)`$ の領域に入る。量化子の無い部分の真偽は、部分構造でも同じである。$`\square`$

## 5. 塔と λ

**定義（塔と λ）.** $`\gamma \lt \omega_1`$ とする。$`k`$ を自然数とする。

```math
N^0(\gamma) := \gamma, \quad N^{k+1}(\gamma) := N\bigl(N^k(\gamma)\bigr), \qquad \lambda(\gamma) := \sup_{k \in \mathbb N} N^k(\gamma)
```

列 $`N^0(\gamma), N^1(\gamma), \ldots`$ を **塔** と呼ぶ。性質 4 から、各 $`N^k(\gamma)`$ は $`\omega_1`$ より下なので、$`N`$ をくり返し当てはめられる。

| 性質 | 内容 | 理由 |
|---|---|---|
| 性質 6 | $`N^k(\gamma) \lt \omega_1`$ | 性質 4 と、$`k`$ についての帰納法 |
| 性質 7 | $`N^k(\gamma) \lt N^{k+1}(\gamma)`$ | 性質 3 |
| 性質 8 | $`k \le k'`$ なら $`N^k(\gamma) \le N^{k'}(\gamma)`$ | 性質 7 |
| 性質 9 | $`N^k(\gamma) \le \lambda(\gamma)`$ | 上限の定義 |
| 性質 10 | $`\lambda(\gamma) \lt \omega_1`$ | 可算個の上限（性質 6、$`\omega_1`$ の正則性） |
| 性質 11 | $`\gamma \lt \lambda(\gamma)`$ | $`\gamma \lt N^1(\gamma) \le \lambda(\gamma)`$ |
| 性質 12 | 有限個の $`p_i \lt \lambda(\gamma)`$ について、ある $`k`$ で全部 $`p_i \lt N^k(\gamma)`$ | 下の証明 |

**性質 12 の証明.** 各 $`p_i`$ は上限より小さいので、ある $`k_i`$ で $`p_i \lt N^{k_i}(\gamma)`$ である。$`k := \max_i k_i`$ を取り、性質 8 を使う。$`\square`$

## 6. λ(γ) は Good

**定理.** $`\gamma \lt \omega_1`$ なら $`\mathrm{Good}(\lambda(\gamma))`$。

**証明.** Tarski–Vaught の判定法（[03](03-sigma1-elementary.md) §6）の形で示す。$`\vec p \lt \lambda(\gamma)`$ で $`\mathfrak B \models \varphi(\vec p)`$ とする。性質 12 から、ある $`k`$ で $`\vec p \lt N^k(\gamma)`$ である。性質 5 を $`N^k(\gamma)`$ で使うと、証人は $`N^{k+1}(\gamma)`$ より下に取れる。$`N^{k+1}(\gamma) \le \lambda(\gamma)`$（性質 9）なので、証人は $`\lambda(\gamma)`$ より下にある。$`\square`$

**系（Good な点は共終）.** $`\sigma \lt \omega_1`$ なら、$`\sigma \lt \alpha \lt \omega_1`$ で $`\mathrm{Good}(\alpha)`$ となる $`\alpha`$ がある。$`\alpha = \lambda(\sigma)`$ でよい（性質 10、性質 11、定理）。

**例（形だけ）.** $`\lambda(0)`$ は、「$`\mathfrak B`$ で真の $`\Sigma_1`$ の主張で、パラメータが $`\lambda(0)`$ より下のもの」の証人をすべて含む。$`\lambda(0)`$ の具体的な値は分からない。証明は値を使わず、$`\lambda(0) \lt \omega_1`$ と $`\mathrm{Good}(\lambda(0))`$ だけを使う。この例は計算していない。$`\mathfrak B`$ の真偽は計算できないからである。

**Good な点の集合について.** Good な点の集合が $`\omega_1`$ の中で閉じていること（Good な点の増加列の上限がまた Good であること）は示していないし、使わない。そのため club（閉非有界集合）とは呼ばない。

## 7. Good な点の列

**定義（Good な点の列）.**

```math
p_0 := \lambda(0), \qquad p_{k+1} := \lambda(p_k)
```

| 性質 | 内容 |
|---|---|
| 性質 13 | $`p_k \lt \omega_1`$ |
| 性質 14 | $`p_0 \lt p_1 \lt p_2 \lt \cdots`$ |
| 性質 15 | $`\mathrm{Good}(p_k)`$ |

どれも §5、§6 から $`k`$ についての帰納法で出る。性質 13 は性質 10、性質 14 は性質 11、性質 15 は §6 の定理による。

この列の 2 点は、すべての鍵で $`R`$ の関係にある。その証明には、Good な点で、上端の述語が $`\omega_1`$ への上端の述語と一致することが要る。どちらも [09](09-obligations.md) §3 で説明する。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「状態」 | 証明が使う公理に選択公理がある。§3 で証人を選ぶところと、§4 の入力の集合が可算であること（[01](01-ordinals.md) §7）で使う |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §3.3 | 閉じた点（このノートの Good な点）、$`\omega`$ 回のくり返し、閉じた点の列 |
