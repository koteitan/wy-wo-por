[← Back](README.md) | [English](en/04-patterns-of-resemblance.md) | [Japanese](04-patterns-of-resemblance.md)

# Patterns of resemblance

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、後者順序数、極限順序数、ラベル、位置 |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎再帰、鍵 $`\mathrm{Key}_m`$、$`\top`$、座標、段、上端、ラベルの上界による停止 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 構造 $`(\gamma; \ldots)`$、領域、高さ、点、原子式、$`\Sigma_1`$ 論理式、パラメータ、証人、リテラル、$`\Sigma_1`$ 初等部分構造 $`\preccurlyeq_{\Sigma_1}`$、型板、評価 $`\mathrm{eval}\ t\ \vec v`$、単調性、内部の関係、上端の述語、部分的な上端の述語 |

このノートは、Carlson の patterns of resemblance の考え方を説明する。次に、[bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) が BMS（Bashicu 行列系。行列を展開する数列の系）でそれをどう使ったかを述べる。最後に、ω-Y でそのままでは足りない理由と、このリポジトリの変更点を述べる。

## 1. 自分自身を言語に持つ関係

**定義（Carlson の ≤₁）.** 順序数の上の関係 $`\le_1`$ を、順序数 $`\alpha, \beta`$ について次の式で定める。右辺の構造の書き方は [03](03-sigma1-elementary.md) §1 のとおりで、言語は $`\{\le, \le_1\}`$ である。

```math
\alpha \le_1 \beta \iff \alpha \le \beta \ \land\ (\alpha; \le, \le_1) \preccurlyeq_{\Sigma_1} (\beta; \le, \le_1)
```

$`\alpha \lt_1 \beta`$ は $`\alpha \lt \beta \land \alpha \le_1 \beta`$ のことである。

**読み方.** 「$`\alpha`$ より下の順序数の形は、$`\beta`$ より下まで広げても、$`\Sigma_1`$ 論理式では見分けられない」。ここで形とは、大小関係と、関係 $`\le_1`$ 自身である。

右辺は左辺の $`\le_1`$ を使う。循環に見えるが、$`\beta`$ についての整礎再帰で定義できる。

- 構造 $`(\beta; \le, \le_1)`$ の領域は $`\{x \mid x \lt \beta\}`$ である。そこで読む $`\le_1`$ は、$`x, y \lt \beta`$ の $`x \le_1 y`$ だけである。
- $`y \lt \beta`$ なので、$`x \le_1 y`$ の真偽は、$`\beta`$ より前の再帰で決まっている。
- 構造 $`(\alpha; \ldots)`$ も同じで、$`\alpha \le \beta`$ である。

Carlson はこれを $`\le_1, \ldots, \le_N`$（$`\Sigma_1, \ldots, \Sigma_N`$ の初等性）に広げた構造を調べた。

```math
\mathcal R_N = (\mathrm{Ord}; \le, \le_1, \ldots, \le_N)
```

$`\mathrm{Ord}`$ は順序数の全体である。$`N`$ は正の整数である。

文献：T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77。

## 2. 小さい例

次の 3 つの例は、手で定義をたどって求めた。

**例 1.** 自然数 $`n \lt \beta`$ について、$`n \le_1 \beta`$ ではない。

- $`n \ge 1`$ のとき：パラメータ $`n - 1`$ の $`\exists x\ (n - 1 \lt x)`$ は、$`\beta`$ で真（$`x = n`$）、$`n`$ で偽である。
- $`n = 0`$ のとき：$`\exists x\ (x \le x)`$ は、$`\beta`$ で真、空の構造 $`0`$ で偽である。

同じ理由で、後者順序数 $`\gamma + 1`$ も、それより大きい順序数と $`\le_1`$ の関係にない。パラメータ $`\gamma`$ の $`\exists x\ (\gamma \lt x)`$ を使えばよい。

**例 2.** $`\omega \lt_1 \omega + 1`$ である。

例 1 から、$`\omega + 1`$ より下の異なる 2 点は $`\le_1`$ の関係にない。自然数どうしは例 1 で、残りは $`\omega`$ 自身だけだからである。したがって $`(\omega; \le, \le_1)`$ と $`(\omega + 1; \le, \le_1)`$ では、$`x \le_1 y`$ は $`x = y`$ と同じである。すると比べるのは順序だけの構造 $`(\omega; \le)`$ と $`(\omega + 1; \le)`$ で、$`\omega`$ は極限順序数なので [03](03-sigma1-elementary.md) §5 の例から成り立つ。

**例 3.** $`\beta \ge \omega + 2`$ なら、$`\omega \le_1 \beta`$ ではない。$`\exists x\ \exists y\ (x \lt y \land x \le_1 y)`$ は、$`\beta`$ で真（例 2 の $`x = \omega`$、$`y = \omega + 1`$ はどちらも $`\beta`$ より下にある）、$`\omega`$ で偽（例 1）だからである。

$`\omega \le_1 \omega`$ は定義から成り立つ。以上から $`\{\beta \mid \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$ である。

順序だけの言語では、$`\omega`$ より大きいどの $`\beta`$ でも $`(\omega; \le) \preccurlyeq_{\Sigma_1} (\beta; \le)`$ だった。$`\le_1`$ 自身を言語に入れたので、関係が細かくなった。

## 3. 停止性の証明での使い方

数列の系の展開は、数列から新しい数列を作る操作である。展開の停止性の証明では、数列の各項に順序数のラベル（[01](01-ordinals.md) §6）を付け、展開でラベルが下がることを示す（[02](02-well-founded.md) §6 のラベルの上界による停止）。そこで要る性質は **有限反映** である。

**有限反映の形.** $`\alpha \lt_1 \beta`$ とする。$`\alpha`$ より下の点 $`\vec p`$ と、$`\beta`$ より下の点 $`\vec y`$ が、有限個の原子式の条件 $`\psi(\vec p, \vec y)`$ を満たすとする。すると、$`\alpha`$ より下の点 $`\vec y'`$ で、同じ条件 $`\psi(\vec p, \vec y')`$ を満たすものがある。

**理由.** $`\exists \vec y\ \psi(\vec p, \vec y)`$ は $`\Sigma_1`$ 論理式で、$`(\beta; \ldots)`$ で真である。$`\Sigma_1`$ 初等性から $`(\alpha; \ldots)`$ でも真である。その証人を $`\vec y'`$ とすればよい。

展開では、この形を次のように使う。

- 項を 1 つ選び、$`\alpha`$ をその項の古いラベルとする。
- 選んだ項より前の項の古いラベルを $`\vec p`$ とする。これらのラベルは反映で動かさない。
- ラベルを付け替える項の古いラベルを $`\vec y`$ とする。$`\vec y`$ はどれも $`\alpha`$ 以上である。
- $`\psi`$ には、項のラベルの間の関係を書く。例えば、BMS の行列で親と子の関係にある 2 つの列のラベルが、関係 $`\le_1`$ などを満たすことである。

有限反映で得た新しいラベル $`\vec y'`$ も同じ関係を満たし、どれも $`\alpha`$ より下にある。したがって新しいラベルは古いラベルより小さい。

**bms-elem-pattern での使い方.** [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) は、BMS の停止性を $`\mathcal R_N`$ で示した。BMS の行列の行 $`k`$ で親と子の関係にある 2 つの列のラベルが、関係 $`\lt_{k+1}`$ を満たすようにする（$`\lt_{k+1}`$ は $`\lt`$ かつ $`\le_{k+1}`$）。有限反映には、各 $`\le_n`$ についての連続性や共終性の補題を使う。$`\mathcal R_N`$ の定義と例は、同リポジトリのノート [proof/pss/03-patterns.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/pss/03-patterns.md) にある。

## 4. ω-Y で足りないもの

ω-Y の組合せの層（Phyrion 氏の証明のうち、数列の展開の組合せの形だけを扱う部分。[06](06-combinatorial-layer.md) で説明する）が要求するラベルの関係は、3 つの引数を持つ。

```math
R(\theta, a, b) \quad (\theta \in \mathrm{Key}_m,\ a, b \in \mathrm{Label})
```

$`\theta`$ は鍵、$`a, b`$ はラベルである。$`m`$ は鍵の長さである。鍵 $`\theta`$ は、ラベルか $`\top`$ を $`m`$ 個並べた列である（[02](02-well-founded.md) §3）。3 番目の引数 $`b`$ は上端である（[02](02-well-founded.md) §3）。このリポジトリでは $`R(\theta, a, b)`$ を次のように読む。「上端の述語を、鍵が $`\theta`$ より下のところでだけ定義した言語（§5）で、高さ $`a`$ の構造が高さ $`b`$ の構造の $`\Sigma_1`$ 初等部分構造である」。定義は [07](07-relation-r.md) で述べる。この読み方をすると、3 つの問題が起きる。

**問題 1：鍵が超限である.** 鍵は $`\mathrm{Key}_m`$ を辞書式に動く。座標はラベルなので、鍵の順序は超限である。$`\mathcal R_N`$ の $`\le_j`$ の $`j = 1, \ldots, N`$（$`\Sigma_1, \ldots, \Sigma_N`$ の初等性）は有限個で、自然数で数える。鍵をこの番号にできない。

**問題 2：上端への条件.** 有限反映は、点 $`x`$ から上端 $`b`$ への関係 $`R(\kappa, x, b)`$（$`\kappa`$ は鍵）も、新しいラベルで成り立たせる必要がある。

**定義（要求）.** 点 $`x`$ から上端 $`b`$ への条件 $`R(\kappa, x, b)`$ を **要求** と呼ぶ。

$`b`$ は構造 $`(b; \ldots)`$ の元ではない。$`R`$ の定義を展開して要求を書くと、$`\Sigma_1`$ 論理式にならない。

**問題 3：要求の鍵が、反映で動く点を名指しうる.** 数列の項 $`i`$ のラベルを $`f(i)`$ とする。要求は $`R(\mathrm{eval}\ t\ f, f(p), b)`$ の形である。$`p`$ は項の番号、$`t`$ は型板（[03](03-sigma1-elementary.md) §7）である。型板は、鍵の各座標にどの項のラベルを置くかを決める。これを「型板が項を名指す」と言う。Phyrion 氏の有限反映の定理（[Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)）は、鍵が名指す項が反映で動かさない点であることを要求しない。つまり鍵の中のラベルは、反映で付け替わる証人（[03](03-sigma1-elementary.md) §2）でもよい。証人を付け替えると、鍵の値も変わる。1-Y 版（[koteitan/1y-wo-por の study/](https://github.com/koteitan/1y-wo-por/tree/main/study)）は、上端の述語が定義されるかどうかを、変数の位置だけで決めた。その方法はここでは使えない。

## 5. このリポジトリの変更点

[notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §2 のとおり、次のように変えた。

1. **どの鍵でも $`\Sigma_1`$ 初等性にする.** 鍵による強さの違いは、量化子の複雑さではなく、どの上端の述語が定義されているかで決まる。
2. **上端の述語を原子記号にする.** 高さ $`c`$ の構造は、型板 $`t`$ と位置 $`i`$ ごとに記号 $`\mathrm{Top}_{t,i}`$（[03](03-sigma1-elementary.md) §7）を持ち、「$`R(\mathrm{eval}\ t\ \vec v, v_i, c)`$」と解釈する。要求は原子式になる（問題 2）。
3. **上端の述語は、鍵が $`\theta`$ より下のところでだけ定義する.** 定義されないところでは、上端のリテラルは偽である（[03](03-sigma1-elementary.md) §8）。定義されるかどうかは鍵の値で決まる（問題 3）。証人を各点で下げても、$`\mathrm{eval}`$ の単調性から鍵は $`\theta`$ より下のままである（[03](03-sigma1-elementary.md) §8）。
4. **内部の関係はすべての鍵で持つ.** 型板 $`t`$ と位置 $`i, j`$ ごとに記号 $`\mathrm{Rel}_{t,i,j}`$（[03](03-sigma1-elementary.md) §7）を持ち、$`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v, v_i, v_j)`$ と解釈する。
5. **段を（上端、鍵）にする.** 上端 $`b`$ を一番外に置く（[02](02-well-founded.md) §3）。鍵 $`\theta`$ の段の右辺は、鍵が $`\theta`$ より小さい上端の述語だけを読む。これは 3 の「定義される範囲」とちょうど一致する（問題 1）。

こうしてできた関係 $`R`$ は、Carlson の $`\mathcal R_N`$ そのものではない。$`\mathcal R_N`$ と同じだとは主張しない。定義は [07 関係 R](07-relation-r.md) で述べる。

| | $`\mathcal R_N`$（bms-elem-pattern） | 1-Y 版（1y-wo-por） | Phyrion 氏の ω-Y の元の意味の層 | このリポジトリ |
|---|---|---|---|---|
| 関係を区別する引数 | $`j = 1, \ldots, N`$ | $`(k, \eta) \in \mathbb N \times \mathrm{Ord}`$ | 鍵 $`\theta \in \mathrm{Key}_m`$ | 鍵 $`\theta \in \mathrm{Key}_m`$ |
| $`R(\cdot, a, b)`$ の中身 | $`\Sigma_j`$ 初等性 | $`\Sigma_1`$ 初等性 | $`b`$ より下の条件の組を $`a`$ より下へ縮められる | $`\Sigma_1`$ 初等性 |
| 上端との関係 | 連続性・共終性の補題 | 原子記号（定義されるかどうかは変数の位置で決まる） | 条件の組の中の要求 | 部分的な原子記号（鍵の値で定義される） |
| 再帰 | 上端 $`\beta`$ | （上端、$`k`$、$`\eta`$） | （上端、鍵） | （上端、鍵） |

表の言葉は次のとおりである（[notes/00-survey.md](../notes/00-survey.md) §3.1、§3.2）。

- 1-Y 版の $`(k, \eta)`$：$`k`$ は自然数の層の番号、$`\eta`$ は根のラベル（1-Y 版で、その層の根の列に付いたラベル）である。
- Phyrion 氏の条件の組：有限個の点の間の条件の組である。中身は、点の間の関係 $`R`$ の有限個の条件と、点から上端への有限個の要求である。どの条件も否定を含まない。
- 「$`b`$ より下の条件の組を $`a`$ より下へ縮められる」：$`b`$ より下の狭義増加なラベル付けで、組の中の点の間の関係が成り立ち、要求（鍵は $`\theta`$ より小さいもの）が上端 $`b`$ について成り立つとする。このとき、$`a`$ より下の狭義増加なラベル付けで、同じ関係が成り立ち、要求が上端 $`a`$ について成り立つものがある。もとのラベルのうち $`a`$ より下のものは動かさない。

Phyrion 氏の元の意味の層は [notes/00-survey.md](../notes/00-survey.md) §3.2 にまとめてある。このリポジトリには含めていない（[NOTICE](../NOTICE)）。

## 6. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md) 冒頭 | Phyrion 氏の反映の定理をそのまま使うこと。patterns of resemblance による weak-magma ω-Y の再証明（koteitan/wmwy-wo-por）への参照 |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §0、§2 | 設計の要約と、構造・論理式・関係の定義 |
| [notes/00-survey.md](../notes/00-survey.md) §3.1〜§3.4 | 1-Y での形、Phyrion 氏の元の関係、1-Y の方法を広げるときの問題 |
