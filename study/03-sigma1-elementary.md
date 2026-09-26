[← Back](README.md) | [English](en/03-sigma1-elementary.md) | [Japanese](03-sigma1-elementary.md)

# 構造と Σ₁ 初等部分構造

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、極限順序数、$`\{x \mid x \lt \gamma\}`$、ラベル、$`\{0, \ldots, n-1\}`$、位置 |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 鍵 $`\mathrm{Key}_m`$ とその順序、$`\top`$、座標、上端 |

このノートは、関係 $`R`$ の定義（[07](07-relation-r.md)）に使うモデル論の言葉を説明する。一階の構造、$`\Sigma_1`$ 論理式、$`\Sigma_1`$ 初等部分構造、Tarski–Vaught の判定法である。§7 と §8 は、このリポジトリで使う言語と、2 つの構造の比べ方を説明する。

## 1. 言語と構造

**定義（言語）.** **言語** は関係記号の集まりで、各記号に引数の数が決まっている。このリポジトリでは関数記号と定数記号は使わない。

**定義（構造）.** 言語 $`L`$ の **構造** $`\mathfrak A`$ は、空でもよい集合 $`A`$（領域）と、各記号 $`P`$（引数の数 $`n`$）の解釈 $`P^{\mathfrak A} \subseteq A^n`$ の組である。

**記法.** 構造を $`(A; P_1, \ldots, P_k)`$ と書く。

- セミコロンの左 $`A`$ は領域である。
- セミコロンの右は、各記号の解釈を言語の順に並べたものである。記号とその解釈は同じ文字で書く。
- 左に順序数 $`\gamma`$ を書いたときは、領域は $`\{x \mid x \lt \gamma\}`$ である。
- 右の関係は領域に制限して読む。たとえば $`(\gamma; \le)`$ の $`\le`$ は $`\{(x, y) \mid x, y \lt \gamma,\ x \le y\}`$ である。

例：$`(4; \lt)`$ の領域は $`\{0, 1, 2, 3\}`$ で、関係は $`\{0, 1, 2, 3\}`$ の上の $`\lt`$ である。

| 言語 | 構造 | 領域 |
|---|---|---|
| $`\{\lt\}`$ | $`(\omega; \lt)`$ | 自然数 |
| $`\{\lt\}`$ | $`(\gamma; \lt)`$ | $`\{x \mid x \lt \gamma\}`$ |
| $`\{\lt, E\}`$（$`E`$ は引数が 2 つの記号） | $`(\omega; \lt, E)`$、$`E(x, y) :\iff y = x + 1`$ | 自然数 |

このリポジトリの構造は、どれも領域が $`\{x \mid x \lt \gamma\}`$ の形である。$`\gamma`$ を構造の **高さ** と呼ぶ。領域の元を **点** と呼ぶ。

## 2. 論理式と Σ₁ 論理式

**定義（論理式）.** 論理式は次のように作る。

- **原子式**：$`P(x_1, \ldots, x_n)`$（$`P`$ は引数が $`n`$ 個の記号、$`x_i`$ は変数）。
- 論理式を $`\neg, \land, \lor, \to`$ でつないだもの。
- 論理式に $`\exists x`$、$`\forall x`$ を付けたもの。

**定義（量化子の無い論理式）.** 量化子 $`\exists`$、$`\forall`$ を含まない論理式である。

**定義（Σ₁ 論理式）.** 量化子の無い論理式 $`\psi`$ に、存在量化子だけを前に付けた形

```math
\exists y_1 \cdots \exists y_k\ \psi(\vec p, y_1, \ldots, y_k)
```

の論理式を **$`\Sigma_1`$ 論理式** と呼ぶ。$`k`$ は自然数である。矢印を付けた文字 $`\vec p`$、$`\vec y`$ は、有限個の変数（または元）の列を表す。$`\vec p`$ は自由変数の列で、あとで領域の元を入れる。入れる元を **パラメータ** と呼ぶ。

| 論理式 | 種類 |
|---|---|
| $`p \lt q`$ | 量化子なし（$`\Sigma_1`$ でもある。$`k = 0`$） |
| $`\exists y\ (p \lt y)`$ | $`\Sigma_1`$ |
| $`\exists y\ \exists z\ (p \lt y \land y \lt z \land E(y, z))`$ | $`\Sigma_1`$ |
| $`\forall y\ (y \lt p \lor p \lt y \lor y = p)`$ | $`\Sigma_1`$ でない |

**定義（充足）.** 構造 $`\mathfrak A`$ と、パラメータの列 $`\vec p`$（各成分が $`A`$ の元。これを $`\vec p \in A`$ と書く）について、$`\mathfrak A \models \varphi(\vec p)`$ は「$`\varphi`$ が $`\mathfrak A`$ で $`\vec p`$ について真」を表す。これを「$`\mathfrak A`$ は $`\varphi(\vec p)`$ を **充足** する」と言う。量化子 $`\exists y`$ は領域 $`A`$ の元を走る。$`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$ のとき、$`\psi(\vec p, \vec y)`$ を真にする $`\vec y`$（$`A`$ の元の列）を **証人** と呼ぶ。

例（手で求めた）：$`(\omega; \lt) \models \exists y\ (3 \lt y)`$ は真で、$`y = 4`$ が証人である。$`(4; \lt) \models \exists y\ (3 \lt y)`$ は偽である。$`(4; \lt)`$ の領域は $`\{0, 1, 2, 3\}`$ だからである。

## 3. リテラルの連言

**定義（リテラル）.** 原子式か、原子式の否定を **リテラル** と呼ぶ。

**事実（選言標準形）.** 量化子の無い論理式は、リテラルの連言の有限個の選言と同値である。この形を **選言標準形** と呼ぶ。存在量化子は選言の上に配れる。

```math
\exists \vec y\ (\psi_1 \lor \psi_2) \iff \exists \vec y\ \psi_1 \ \lor\ \exists \vec y\ \psi_2
```

したがって、どの $`\Sigma_1`$ 論理式も、「存在量化子とリテラルの連言」の形の論理式の有限個の選言と同値である。2 つの構造で、この形の論理式の真偽がすべて一致すれば、すべての $`\Sigma_1`$ 論理式の真偽が一致する。

**例.** $`\exists y\ \bigl((p \lt y \land \neg(y \lt q)) \lor E(p, y)\bigr)`$ は $`\exists y\ (p \lt y \land \neg(y \lt q)) \lor \exists y\ E(p, y)`$ と同値である。

**等号.** $`\lt`$ が線形順序なら、等号の記号は要らない。$`x = y \iff \neg(x \lt y) \land \neg(y \lt x)`$ だからである。

このリポジトリの論理式は、この「存在量化子とリテラルの連言」の形だけである（§7）。

## 4. 部分構造と、上への保存

**定義（部分構造）.** $`\mathfrak A`$ が $`\mathfrak B`$ の **部分構造** であるとは、$`A \subseteq B`$ で、各記号の解釈が制限になっていることをいう。つまり $`\vec a \in A`$ について $`P^{\mathfrak A}(\vec a) \iff P^{\mathfrak B}(\vec a)`$ である。

**性質 1.** 部分構造では、$`A`$ の元についての量化子の無い論理式の真偽が一致する。原子式の真偽が同じだからである。

**性質 2（Σ₁ は上に保存される）.** 部分構造で、$`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$ なら $`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$ である。$`\mathfrak A`$ の証人 $`\vec y`$ は $`B`$ にもあり、性質 1 から $`\psi`$ の真偽も同じだからである。

**逆は成り立たない.** $`(4; \lt)`$ は $`(\omega; \lt)`$ の部分構造である。$`\exists y\ (3 \lt y)`$ は $`(\omega; \lt)`$ で真、$`(4; \lt)`$ で偽である（§2 の例）。

## 5. Σ₁ 初等部分構造

**定義（Σ₁ 初等部分構造）.** $`\mathfrak A`$ が $`\mathfrak B`$ の **$`\Sigma_1`$ 初等部分構造** であるとは、$`\mathfrak A`$ が $`\mathfrak B`$ の部分構造で、すべての $`\Sigma_1`$ 論理式 $`\varphi`$ とすべてのパラメータ $`\vec p \in A`$ について次が成り立つことをいう。

```math
\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)
```

これを $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$ と書く。

**意味.** $`A`$ の元だけを使って述べられる「こういう有限個の元がある」という主張は、$`\mathfrak B`$ で真なら $`\mathfrak A`$ でも真である。証人を $`A`$ の中で取り直せる。

**例（順序だけの言語）.** $`0 \lt \alpha \lt \beta`$ を順序数とする。

```math
(\alpha; \lt) \preccurlyeq_{\Sigma_1} (\beta; \lt) \iff \alpha \text{ は極限順序数}
```

**証明.**

- $`\alpha = \gamma + 1`$ のとき：パラメータ $`\gamma`$ の $`\exists y\ (\gamma \lt y)`$ は $`(\beta; \lt)`$ で真（$`y = \gamma + 1`$）、$`(\alpha; \lt)`$ で偽である。よって成り立たない。
- $`\alpha`$ が極限のとき：$`\Sigma_1`$ 論理式 $`\exists \vec y\ \psi(\vec p, \vec y)`$ が $`(\beta; \lt)`$ で真だとする。その証人 $`\vec y`$ を、パラメータとの大小関係を保ったまま $`\alpha`$ の中に置き直す。
  - $`\vec p`$ の最大値より下にある証人は、もともと $`\alpha`$ の中にある。そのままでよい。
  - 最大値より上にある証人は有限個である（パラメータが無いときは、すべての証人をこちらに数える）。$`\alpha`$ が極限なので、最大値より上に $`\alpha`$ の元は無限個ある（[01](01-ordinals.md) §2）。同じ順に並べて置き直せる。
  - 置き直しても、$`\lt`$ の真偽は変わらない。よって $`\psi`$ は $`(\alpha; \lt)`$ で真である。
  - 逆向きは §4 の性質 2 である。$`\square`$

$`\alpha = 0`$ も除かれる。$`\exists y\ \neg(y \lt y)`$ は空の構造 $`(0; \lt)`$ で偽、$`(\beta; \lt)`$ で真である。

## 6. Tarski–Vaught の判定法（Σ₁ 版）

$`\Sigma_1`$ 初等性を示すには、下向きだけを確かめればよい。

**定理（Tarski–Vaught の判定法、Σ₁ 版）.** $`\mathfrak A`$ を $`\mathfrak B`$ の部分構造とする。次の 2 つは同値である。

1. $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$。
2. 量化子の無い $`\psi`$ と $`\vec p \in A`$ について、$`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$ なら、ある $`\vec y \in A`$ で $`\mathfrak B \models \psi(\vec p, \vec y)`$ である。

**証明.** 1 から 2：$`\mathfrak A`$ で真になるので、$`A`$ に証人がある。§4 の性質 1 から $`\mathfrak B`$ でも $`\psi`$ が真である。2 から 1：上向きは §4 の性質 2 である。下向きは、2 の証人が $`A`$ にあり、性質 1 から $`\mathfrak A \models \psi(\vec p, \vec y)`$ となることから出る。$`\square`$

一般の Tarski–Vaught の判定法は、すべての論理式について同じことを言う。このリポジトリは $`\Sigma_1`$ だけを使う。

**使い方.** 2 の条件は「$`A`$ が証人で閉じている」ことである。[08](08-closure-chain.md) はこの形を使う。$`\gamma`$ から始めて、真の主張の証人を足していき、上限を取る。

## 7. 型板と、このリポジトリの言語

**定義（型板）.** $`m`$ と $`n`$ を自然数とする。長さ $`m`$、変数 $`n`$ 個の **型板** は、各座標 $`k \lt m`$ に、$`\{0, \ldots, n-1\}`$ の番号か $`\top`$ を置いた列 $`t = (t_0, \ldots, t_{m-1})`$ である。

**定義（評価）.** $`v = (v_0, \ldots, v_{n-1})`$ をラベルの列とする。型板 $`t`$ の **評価** $`\mathrm{eval}\ t\ v`$ は、次の座標を持つ長さ $`m`$ の鍵である。

```math
(\mathrm{eval}\ t\ v)_k = \begin{cases} v_i & (t_k = i) \cr \top & (t_k = \top) \end{cases}
```

**例（Python で計算した）.** $`m = 2`$、$`n = 3`$ とする。$`v = (3, 5, 8)`$、$`w = (2, 5, 7)`$ とする。

| 型板 $`t`$ | $`\mathrm{eval}\ t\ v`$ | $`\mathrm{eval}\ t\ w`$ |
|---|---|---|
| $`(1, \top)`$ | $`(5, \top)`$ | $`(5, \top)`$ |
| $`(2, 0)`$ | $`(8, 3)`$ | $`(7, 2)`$ |
| $`(\top, \top)`$ | $`(\top, \top)`$ | $`(\top, \top)`$ |

どの行でも $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v`$ である。次の性質がその理由である。

**性質 3（単調性）.** すべての $`i`$ で $`w_i \le v_i`$ なら、$`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v`$ である。

**証明.** 各座標で $`(\mathrm{eval}\ t\ w)_k \le (\mathrm{eval}\ t\ v)_k`$ である。$`t_k = i`$ なら $`w_i \le v_i`$、$`t_k = \top`$ なら両方 $`\top`$ だからである。各座標で小さいか等しいなら、最初に違う座標（[02](02-well-founded.md) §3）でも小さい。よって鍵として $`\le`$ である。$`\square`$

**このリポジトリの言語.** 論理式の変数を $`v_0, \ldots, v_{n-1}`$ とし、$`\vec v = (v_0, \ldots, v_{n-1})`$ と書く。番号 $`i`$ は変数の位置（[01](01-ordinals.md) §7）である。記号は 3 種類である。

- 順序 $`\lt`$。
- 型板 $`t`$ と位置 $`i, j`$ ごとの **内部の関係** $`\mathrm{Rel}_{t,i,j}(\vec v)`$。2 つの点 $`v_i, v_j`$ の間の関係で、鍵は $`\mathrm{eval}\ t\ v`$ である。
- 型板 $`t`$ と位置 $`i`$ ごとの **上端の述語** $`\mathrm{Top}_{t,i}(\vec v)`$。点 $`v_i`$ から構造の高さ $`c`$ への関係で、鍵は $`\mathrm{eval}\ t\ v`$ である。$`c`$ は上端（[02](02-well-founded.md) §3）の役をする。$`c`$ 自身は領域に無い。

鍵は変数の値で決まる。ここでは記号だけを決める。2 つの記号の解釈は [07](07-relation-r.md) で与える。

このリポジトリの論理式は、次の形の $`\Sigma_1`$ 論理式である。

```math
\exists \vec y\ (\ell_1 \land \cdots \land \ell_r)
```

- 各 $`\ell`$ はリテラルで、$`v_i \lt v_j`$、$`\mathrm{Rel}_{t,i,j}(\vec v)`$、$`\mathrm{Top}_{t,i}(\vec v)`$ のどれかか、その否定である。
- 変数の位置のうち、決めた位置がパラメータで、残りの位置の変数 $`\vec y`$ を存在量化する。
- §3 から、この形だけを考えれば十分である。

**例（手で求めた）.** $`n = 2`$ とし、位置 0 をパラメータ、位置 1 を存在量化する変数とする。リテラルは $`v_0 \lt v_1`$ の 1 つとする。この論理式は $`\exists v_1\ (p_0 \lt v_1)`$ である。高さ $`c`$ の構造では、$`p_0 \lt c`$ のパラメータについて、この論理式が真であることと $`p_0 + 1 \lt c`$ は同値である。

## 8. 2 つの構造の比べ方と、部分的な上端の述語

このリポジトリの比べ方には、教科書の定義と違う点が 2 つある。以下では、鍵 $`\theta`$ を 1 つ固定する。

**違い 1：同じ記号を別に解釈する.** 関係 $`R`$ の定義（[07](07-relation-r.md)）では、高さ $`a`$ の構造と高さ $`b`$ の構造を比べる（$`a \lt b`$）。内部の関係の解釈は 2 つの構造で共通である。上端の述語は、高さ $`a`$ では「$`a`$ への関係」、高さ $`b`$ では「$`b`$ への関係」と解釈する。したがって、前もって部分構造であるとは言えない。

そこで、2 つの構造 $`\mathfrak A`$（高さ $`a`$）と $`\mathfrak B`$（高さ $`b`$）について、$`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$ を次の意味で使う。

```math
\forall \varphi\ \forall \vec p \lt a\ \ \bigl(\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)\bigr)
```

$`\varphi`$ は §7 の形の論理式を動く。$`\vec p \lt a`$ は、パラメータがどれも $`a`$ より小さいことを表す。部分構造であることは仮定しない。

それでも、この条件から部分構造であることが出る。すべての変数がパラメータの論理式（量化子の無い論理式）を取ると、$`a`$ より下の点についてのリテラルの真偽が一致するからである。上端のリテラルも、定義されているところ（違い 2）で一致する。よって $`\mathfrak A`$ は $`\mathfrak B`$ の部分構造で、しかも §5 の意味で $`\Sigma_1`$ 初等である。

**違い 2：上端の述語は部分的である.** 上端の述語は、鍵が $`\theta`$ より小さいところでだけ定義する。つまり、リテラル $`\mathrm{Top}_{t,i}(\vec v)`$ とその否定 $`\neg\mathrm{Top}_{t,i}(\vec v)`$ は、どちらも $`\mathrm{eval}\ t\ v \lt \theta`$ のときだけ真になりうる。$`\mathrm{eval}\ t\ v \ge \theta`$ なら、どちらも偽である。このような上端の述語を **部分的な上端の述語** と呼ぶ。

**例（Python で確かめた）.** 鍵の長さを $`m = 1`$ とし、$`\theta = (5)`$（座標 0 がラベル 5 の鍵）とする。変数は $`v_0, v_1`$ の 2 つとする。型板 $`t = (0)`$ は鍵 $`(v_0)`$ を与え、型板 $`t' = (\top)`$ は鍵 $`(\top)`$ を与える。

| リテラル | $`v = (3, 10)`$ | $`v = (7, 10)`$ |
|---|---|---|
| $`\mathrm{Top}_{t,1}(\vec v)`$ | 鍵 $`(3) \lt \theta`$ なので定義される。真偽は解釈で決まる | 偽（鍵 $`(7)`$ は $`\theta`$ 以上） |
| $`\neg\mathrm{Top}_{t,1}(\vec v)`$ | 鍵 $`(3) \lt \theta`$ なので定義される。真偽は解釈で決まる | 偽 |
| $`\mathrm{Top}_{t',1}(\vec v)`$ | 偽（鍵 $`(\top)`$ は $`\theta`$ 以上） | 偽 |

**性質 4（証人を各点で下げても鍵は θ より小さいまま）.** すべての $`i`$ で $`w_i \le v_i`$ とする。$`\mathrm{eval}\ t\ v \lt \theta`$ なら $`\mathrm{eval}\ t\ w \lt \theta`$ である。したがって、$`v`$ で定義されている上端のリテラルは、$`w`$ でも定義されている。

**証明.** 性質 3 から $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v \lt \theta`$ である。$`\square`$

この性質は、証人を各点で小さい値に取り替えるところで使う（[07](07-relation-r.md) §7、[09](09-obligations.md)）。

**性質 5（読むところだけで決まる）.** 高さ $`c`$ の構造で §7 の形の論理式の真偽を決めるのは、次の 2 つだけである。$`c`$ より下の点の間の内部の関係の解釈と、$`c`$ より下の点での、鍵が $`\theta`$ より小さい上端の述語の解釈である。2 つの解釈がそこで一致すれば、どの論理式の真偽も一致する。論理式はそれ以外のところを読まないからである。

この性質は、[07](07-relation-r.md) で、ガード（[02](02-well-founded.md) §5）を外すのに使う。

**1-Y 版との違い.** 1-Y 版の study（[koteitan/1y-wo-por の study/](https://github.com/koteitan/1y-wo-por/tree/main/study)）では、上端の述語が定義されるかどうかを、変数の位置だけで決めた。このリポジトリでは、定義されるかどうかは鍵の値 $`\mathrm{eval}\ t\ v`$ で決まる。つまり変数の値に依る。そのため性質 4 が要る。

## 9. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §2.1 | 構造の領域、内部の関係、部分的な上端の述語（§1、§7、§8） |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §2.2 | 論理式はリテラルの連言に存在量化子を付けた形。上端のリテラルは鍵が $`\theta`$ より小さいときだけ真になりうる（§3、§7、§8） |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §2.3 | $`\preccurlyeq_{\Sigma_1}`$ をパラメータが $`a`$ より下の論理式の真偽の一致として読む（§5、§8） |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §3.1 | 証人を各点で下げても鍵は $`\theta`$ より小さいまま（§8 の性質 4） |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §3.3 | 閉じた点は、§6 の条件 2（証人で閉じている）の形で定める |
| [notes/00-survey.md](../notes/00-survey.md) §3.2 | 鍵の型板と、評価の単調性（§7） |
