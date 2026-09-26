[← Back](README.md) | [English](en/07-relation-r.md) | [Japanese](07-relation-r.md)

# 関係 R

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、後者順序数、極限順序数、ラベル、$`\omega_1`$、位置 |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 辞書式順序、整礎再帰、ガード、鍵 $`\mathrm{Key}_m`$、$`\top`$、座標、段、上端 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 構造 $`(A; P_1, \ldots, P_k)`$、領域、高さ、点、$`\Sigma_1`$ 論理式、量化子の無い論理式、パラメータ、証人、リテラル、$`\Sigma_1`$ 初等部分構造 $`\preccurlyeq_{\Sigma_1}`$、型板、評価 $`\mathrm{eval}\ t\ \vec v`$、単調性、内部の関係 $`\mathrm{Rel}_{t,i,j}`$、上端の述語 $`\mathrm{Top}_{t,i}`$、部分的な上端の述語 |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | 上端の述語を原子記号にする考え方、要求 |
| [06 組合せの層と脚の原子](06-combinatorial-layer.md) | 鍵の弱化（§5 の文） |

このノートは、このリポジトリのラベルの関係 $`R`$ の定義と、定義から直接出る性質を説明する。[06](06-combinatorial-layer.md) §5 で文だけを述べた鍵の弱化を、ここで証明する。

## 1. 記号

- $`\mathrm{Label} = \{o \mid o \le \omega_1\}`$：ラベルの集合（[01](01-ordinals.md) §6）。このノートの議論は、ラベルの順序が整列した線形順序であることだけを使う。
- $`\mathrm{Key}_m`$：長さ $`m`$ の鍵の集合（[02](02-well-founded.md) §3）。このノートの議論は、鍵の順序が整列した線形順序であることだけを使う。
- $`R(\theta, a, b)`$：鍵 $`\theta`$、下の点 $`a`$（ラベル）、上の点 $`b`$（ラベル）の関係。$`b`$ は上端である（[02](02-well-founded.md) §3）。
- $`\vec v = (v_0, \ldots, v_{n-1})`$ はラベルの列である。$`\vec v \lt a`$ は、各成分が $`a`$ より下であることを表す。$`\vec w \le \vec v`$ は、すべての $`i`$ で $`w_i \le v_i`$ であること（各点で小さい）を表す。

## 2. 言語

[03](03-sigma1-elementary.md) §7 の言語の記号に、ここで意味を与える。記号は 3 種類である。$`n`$ 変数の型板 $`t`$ と位置 $`i, j \lt n`$ ごとに、次の記号がある。

| 記号 | 引数の数 | 意味（高さ $`c`$ の構造で） |
|---|---|---|
| $`\lt`$ | 2 | ラベルの大小 |
| $`\mathrm{Rel}_{t,i,j}`$ | $`n`$ | $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$ |
| $`\mathrm{Top}_{t,i}`$ | $`n`$ | $`\mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$ |

$`\mathrm{Rel}`$ は点どうしの関係、$`\mathrm{Top}`$ は点から上端 $`c`$（構造の高さ）への関係である。$`c`$ 自身は領域に無い。どちらの記号も、鍵を $`n`$ 個の点から型板で計算する。$`\mathrm{Top}_{t,i}(\vec v)`$ は、[04](04-patterns-of-resemblance.md) §4 の要求 $`R(\kappa, v_i, c)`$（$`\kappa = \mathrm{eval}\ t\ \vec v`$）を 1 つの原子式にしたものである。

## 3. 構造 𝔄^c_θ

**定義.** 鍵 $`\theta`$ とラベル $`c`$ について、高さ $`c`$ の構造 $`\mathfrak A^c_\theta`$ を次で定める。

```math
\mathfrak A^c_\theta = \bigl(c;\ \lt,\ (\mathrm{Rel}_{t,i,j}),\ (\mathrm{Top}_{t,i})\bigr)
```

- 領域は $`\{x \mid x \lt c\}`$、順序は $`\lt`$ である。
- $`\mathrm{Rel}_{t,i,j}`$ は、すべての型板 $`t`$ で §2 の意味を持つ。
- $`\mathrm{Top}_{t,i}(\vec v)`$ は、$`\mathrm{eval}\ t\ \vec v \lt \theta`$ のときだけ定義され、そのとき §2 の意味を持つ。定義されないところでは、上端のリテラルは肯定でも否定でも偽である（[03](03-sigma1-elementary.md) §8）。

**例.** 1 変数 $`v_0`$ の型板を考える。型板は、鍵の各座標に変数の番号 $`0`$ か $`\top`$ を置いたものである（[03](03-sigma1-elementary.md) §7）。次の表は、上端の述語が定義される $`v_0`$ の範囲である。手で定義をたどって求め、Python でも確かめた（$`v_0 \in \{0, 1, 2, 3, 4, 5, \omega, \omega + 1\}`$ で比べた）。

| 鍵の長さ | $`\theta`$ | 型板 | 鍵 $`\mathrm{eval}\ t\ (v_0)`$ | 定義される範囲 |
|---|---|---|---|---|
| $`m = 1`$ | $`(\omega)`$ | $`(0)`$ | $`(v_0)`$ | $`v_0 \lt \omega`$（$`v_0`$ が自然数） |
| $`m = 1`$ | $`(\omega)`$ | $`(\top)`$ | $`(\top)`$ | どこでもない |
| $`m = 1`$ | $`(\top)`$ | $`(0)`$ | $`(v_0)`$ | どこでも（$`v_0`$ はラベルなので $`v_0 \lt \top`$） |
| $`m = 2`$ | $`(3, \omega)`$ | $`(0, \top)`$ | $`(v_0, \top)`$ | $`v_0 \lt 3`$ |
| $`m = 2`$ | $`(3, \omega)`$ | $`(0, 0)`$ | $`(v_0, v_0)`$ | $`v_0 \le 3`$ |
| $`m = 2`$ | $`(3, \omega)`$ | $`(\top, 0)`$ | $`(\top, v_0)`$ | どこでもない |

$`m = 2`$ の 2 行目では、$`v_0 = 3`$ のとき座標 0 が等しく、座標 1 で $`3 \lt \omega`$ なので定義される。

## 4. 定義

**定義（R）.**

```math
R(\theta, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

2 つの構造で、上端の述語は別のもの（$`a`$ への $`R`$ と $`b`$ への $`R`$）である。そのため、[03](03-sigma1-elementary.md) §8 のとおり、ここでの $`\preccurlyeq_{\Sigma_1}`$ は次の意味である。すべての $`\Sigma_1`$ 論理式 $`\varphi`$ と、すべてのパラメータ $`\vec p \lt a`$ について、次が成り立つ。

```math
\mathfrak A^{a}_{\theta} \models \varphi(\vec p) \iff \mathfrak A^{b}_{\theta} \models \varphi(\vec p)
```

量化子の無い論理式に当てはめると、$`a`$ より下の点では、2 つの構造の原子式の真偽が一致する。上端の述語も、定義されているところでは一致する。

## 5. 再帰

右辺は $`R`$ 自身を読む。段 $`(b, \theta)`$（上端と鍵の組）の辞書式順序 $`\lhd`$（[02](02-well-founded.md) §3）で整礎再帰をする。1 つの段 $`(b, \theta)`$ で、すべての $`a`$ について一度に定義する。

**右辺が読む R.** 3 種類だけで、どれも段が小さい。

| 読むもの | 段 | 小さい理由 |
|---|---|---|
| 内部の関係 $`\mathrm{Rel}(\vec v)`$、つまり $`R(\kappa, x, y)`$ | $`(y, \kappa)`$ | 点は高さ（$`a`$ か $`b`$）より下なので $`y \lt b`$ |
| $`\mathfrak A^{a}_\theta`$ の上端の述語 $`R(\kappa, x, a)`$ | $`(a, \kappa)`$ | $`a \lt b`$ |
| $`\mathfrak A^{b}_\theta`$ の上端の述語 $`R(\kappa, x, b)`$ | $`(b, \kappa)`$ | 定義されるのは $`\kappa \lt \theta`$ のときだけ |

3 行目が要点である。$`\mathfrak A^{b}_\theta`$ の上端の述語を鍵 $`\theta`$ より下でだけ定義したので、右辺は段 $`(b, \theta)`$ 自身を読まない。

**再帰の式.** 段 $`(b, \theta)`$ で、段が $`(b, \theta)`$ より小さいところの $`R`$ はもう決まっているとする。読むところにはガード（[02](02-well-founded.md) §5）を付ける。ガードが偽のときは $`R`$ を読まず、偽とする。

| 解釈 | 式 |
|---|---|
| 内部の関係 | $`\mathrm{rel}(\kappa, x, y) :\iff y \lt b \text{ で、かつ } R(\kappa, x, y)`$ |
| 高さ $`a`$ の上端 | $`\mathrm{top}_A(\kappa, x) :\iff R(\kappa, x, a)`$（ガード $`a \lt b`$ は、次の式の先頭で要求する） |
| 高さ $`b`$ の上端 | $`\mathrm{top}_B(\kappa, x) :\iff \kappa \lt \theta \text{ で、かつ } R(\kappa, x, b)`$ |

$`\mathfrak C^{a}`$ を、高さ $`a`$ の構造で、内部の関係を $`\mathrm{rel}`$、上端の述語を $`\mathrm{top}_A`$ で解釈し、上端の述語を鍵 $`\lt \theta`$ でだけ定義したものとする。$`\mathfrak C^{b}`$ を、高さ $`b`$ の構造で、内部の関係を $`\mathrm{rel}`$、上端の述語を $`\mathrm{top}_B`$ で解釈し、同じく鍵 $`\lt \theta`$ でだけ定義したものとする。段 $`(b, \theta)`$ の定義は次である。

```math
R(\theta, a, b) :\iff a \lt b \ \land\ \mathfrak C^{a} \preccurlyeq_{\Sigma_1} \mathfrak C^{b}
```

ガードがあるので、この式は段が $`(b, \theta)`$ より小さいところの $`R`$ だけを読む。よって整礎再帰で $`R`$ が決まる。

## 6. ガードを外した式

証明には [03](03-sigma1-elementary.md) §8 の性質 5（読むところだけで決まる）を使う。高さ $`c`$ の構造の 2 つの解釈が、$`c`$ より下の点の間の内部の関係と、$`c`$ より下の点での鍵 $`\lt \theta`$ の上端の述語で一致すれば、どの論理式の真偽も一致する、という性質である。

**定理（定義の式）.**

```math
R(\theta, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

右辺の 2 つの構造は、§3 の本当の解釈（ガードの無い解釈）を持つ。

**証明.** 整礎再帰の定義の式から、左辺は $`a \lt b \land \mathfrak C^{a} \preccurlyeq_{\Sigma_1} \mathfrak C^{b}`$ と同値である。$`a \lt b`$ を仮定して、$`\mathfrak C^{a}`$ と $`\mathfrak A^{a}_\theta`$、$`\mathfrak C^{b}`$ と $`\mathfrak A^{b}_\theta`$ が、この性質の条件を満たすことを示す。

1. 内部の関係：読むのは第 2 の点 $`y`$ が高さより下のところだけである。高さは $`a`$ か $`b`$ で、どちらも $`b`$ 以下なので、ガード $`y \lt b`$ は真である。
2. 高さ $`a`$ の上端：ガードは $`a \lt b`$ で、仮定そのものである。
3. 高さ $`b`$ の上端：読むのは鍵 $`\kappa \lt \theta`$ のところだけである。そこではガード $`\kappa \lt \theta`$ は真である。

性質 5 から、$`a`$ より下のパラメータを持つ $`\Sigma_1`$ 論理式の真偽は、$`\mathfrak C^{a}`$ と $`\mathfrak A^{a}_\theta`$ で一致し、$`\mathfrak C^{b}`$ と $`\mathfrak A^{b}_\theta`$ で一致する。よって 2 つの $`\preccurlyeq_{\Sigma_1}`$ は同値である。$`\square`$

これ以降は、この定義の式だけを使う。

## 7. 定義から直接出る性質

**性質 1.** $`R(\theta, a, b)`$ なら $`a \lt b`$。定義の式の第 1 項である。

**定理（鍵の弱化）.** $`\theta \le \Theta`$ かつ $`R(\Theta, a, b)`$ なら $`R(\theta, a, b)`$。

証明には、次の 2 つの事実を使う。

- 事実 A：$`\theta \le \Theta`$ とする。上端の述語を鍵 $`\lt \theta`$ で定義した構造で成り立つリテラルは、同じ解釈で鍵 $`\lt \Theta`$ まで定義した構造でも成り立つ。上端のリテラルが成り立つなら、その鍵は $`\theta`$ より下で、したがって $`\Theta`$ より下だからである。ほかのリテラルは定義の範囲を読まない。
- 事実 B（[03](03-sigma1-elementary.md) §8 の性質 4）：$`\vec w \le \vec v`$ で $`\mathrm{eval}\ t\ \vec v \lt \theta`$ なら、$`\mathrm{eval}\ t\ \vec w \le \mathrm{eval}\ t\ \vec v \lt \theta`$ である。評価の単調性による。

**証明.** 定義の式から $`a \lt b`$ と $`\mathfrak A^{a}_{\Theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\Theta}`$ を得る。$`\Sigma_1`$ 論理式 $`\varphi`$ とパラメータ $`\vec p \lt a`$ について、2 つの向きを示す。

- 下から上：$`\mathfrak A^{a}_\theta \models \varphi(\vec p)`$ とし、証人を $`\vec w \lt a`$ とする。すべての変数をパラメータにした論理式 $`\varphi'`$ を作る。パラメータの値は、元のパラメータ $`\vec p`$ と証人 $`\vec w`$ である。事実 A から $`\mathfrak A^{a}_\Theta \models \varphi'`$ である。鍵 $`\Theta`$ での初等性から $`\mathfrak A^{b}_\Theta \models \varphi'`$ である。$`\varphi'`$ に量化子は無いので、同じ点でリテラルが成り立つ。上端のリテラルの鍵は点だけで決まり、$`\mathfrak A^{a}_\theta`$ で定義されていたので $`\theta`$ より下である。よって $`\mathfrak A^{b}_\theta`$ でも定義されていて、成り立つ。$`\vec w`$ が $`\mathfrak A^{b}_\theta`$ での証人になる。
- 上から下：$`\mathfrak A^{b}_\theta \models \varphi(\vec p)`$ とし、証人を $`\vec v \lt b`$ とする。値が $`a`$ より下の位置をすべてパラメータにした論理式 $`\varphi'`$ を作る。元のパラメータ $`\vec p`$ は $`a`$ より下なので、その位置もパラメータのままである。事実 A から $`\mathfrak A^{b}_\Theta \models \varphi'`$ である。鍵 $`\Theta`$ での初等性から、$`\mathfrak A^{a}_\Theta`$ での証人 $`\vec w \lt a`$ がある。値が $`a`$ より下の位置では $`w_i = v_i`$ である。ほかの位置では $`w_i \lt a \le v_i`$ である。よって $`\vec w \le \vec v`$ である。上端のリテラルは $`\vec v`$ で $`\mathfrak A^{b}_\theta`$ で定義されていたので、鍵は $`\theta`$ より下である。事実 B から、$`\vec w`$ での鍵も $`\theta`$ より下である。よって $`\mathfrak A^{a}_\theta`$ でも定義されていて、$`\mathfrak A^{a}_\Theta`$ と同じ真偽を持つ。$`\vec w`$ が $`\mathfrak A^{a}_\theta`$ での証人になる。$`\square`$

2 つめの向きで、証人を各点で下げることが要る。そのために評価の単調性を使う。

**性質 2（定義された上端の述語の一致）.** $`R(\theta, a, b)`$ で、$`\vec v \lt a`$ とする。$`\mathrm{eval}\ t\ \vec v \lt \theta`$ なら、次が成り立つ。

```math
R(\mathrm{eval}\ t\ \vec v,\ v_i,\ a) \iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ b)
```

**理由.** すべての変数がパラメータの論理式 $`\mathrm{Top}_{t,i}(\vec v)`$ を使う。高さ $`a`$ では左辺、高さ $`b`$ では右辺を意味する。§4 の初等性から、2 つは同値である。この性質は証明の本筋では使わない。[09](09-obligations.md) §3.1 で、似た形の性質を示す。

**性質 3（下の点は極限順序数）.** $`R(\theta, a, b)`$ なら、$`a`$ は 0 でない極限順序数である。

**理由.** [03](03-sigma1-elementary.md) §5 の例と同じである。

- $`a = 0`$ のとき：パラメータの無い $`\exists v_0\ \neg(v_0 \lt v_0)`$ は、高さ $`b`$ で真、高さ 0 で偽である。
- $`a = \gamma + 1`$ のとき：パラメータ $`\gamma \lt a`$ の $`\exists v_1\ (\gamma \lt v_1)`$ は、高さ $`b`$ で真（$`v_1 = \gamma + 1 \lt b`$）、高さ $`a`$ で偽である。

どちらも初等性に反する。この性質は証明の本筋では使わない。

## 8. 使わない性質

**推移性.** $`R(\theta, a, b) \land R(\theta, b, c) \implies R(\theta, a, c)`$ である。中間の構造 $`\mathfrak A^b_\theta`$ は 2 つの関係で同じものなので、パラメータ $`\vec p \lt a`$ の論理式について 2 つの同値をつなげばよい。この性質は証明では使わない。

## 9. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md) 冒頭 | Phyrion 氏の反映の定理をそのまま使うこと。この定理が要る関係 $`R`$ と鍵の弱化を、このノートの定義で与える |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §1 | 組合せの層が使う関係 $`R`$ と鍵の弱化 |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §2、§3.1 | 構造、定義、再帰の段、鍵の弱化の証明 |
