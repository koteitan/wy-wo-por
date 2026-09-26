[← Back](README.md) | [English](en/09-obligations.md) | [Japanese](09-obligations.md)

# 3 つの定理の証明

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 極限順序数、$`\omega_1`$、$`\omega_1`$ の正則性、ラベル、$`\{0, \ldots, n-1\}`$ |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎帰納法、鍵、$`\top`$、上端 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 構造の高さ、$`\Sigma_1`$ 論理式、パラメータ、証人、リテラル、$`\preccurlyeq_{\Sigma_1}`$、型板、評価 $`\mathrm{eval}\ t\ v`$、単調性、内部の関係 $`\mathrm{Rel}_{t,i,j}`$、上端の述語 $`\mathrm{Top}_{t,i}`$、部分的な上端の述語 |
| [05 公式の ω-Y 数列と山](05-omegay-mountain.md) | 山 $`M(s)`$、次数の上界 $`D`$、$`s[n]`$、$`x_0`$、$`t`$、$`c_r`$、$`w`$、最終定理 |
| [06 組合せの層と脚の原子](06-combinatorial-layer.md) | 内部の原子、上端の原子、図式、表現、3 つの定理（鍵の弱化、有限反映、最初の表現）、切れ目、制御関係、列の番号で評価した鍵、新しいラベル、継ぎ合わせ、予備 $`F, T`$、状態、制御の原子と $`K_c`$、分類（基・予備・継ぎ目）、降下の定理、脚の原子 $`\mathrm{at}(u)`$、原子の系 $`E_D(M)`$、分類の補題 |
| [07 関係 R](07-relation-r.md) | 構造 $`\mathfrak A^c_\theta`$、関係 $`R`$、定義の式、鍵の弱化の証明 |
| [08 ω₁ より下の閉包と Good な点の列](08-closure-chain.md) | 周りの構造、Good、Good な点の列 $`p_0 \lt p_1 \lt \cdots`$ |

このノートは、[07](07-relation-r.md) の関係 $`R`$ が、[06](06-combinatorial-layer.md) §5 の 3 つの定理を満たすことを示す。中心は有限反映（§2）と最初の表現（§3）である。

## 1. 一覧

| 定理（[06](06-combinatorial-layer.md) §5） | 証明 |
|---|---|
| 鍵の弱化 | [07](07-relation-r.md) §7 |
| 有限反映 | §2 |
| 最初の表現 | §3（§3.1、§3.2 を使って §3.3 で示す） |

## 2. 有限反映

**記号.** [06](06-combinatorial-layer.md) §5 の有限反映の仮定を、次の記号で書く。

- $`n`$ は図式の点の数である。点は $`0, \ldots, n-1`$ である。
- $`f : \{0, \ldots, n-1\} \to \mathrm{Label}`$ は狭義増加のラベルで、すべての $`j`$ で $`f(j) \lt b`$ である。$`b`$ は上端である。
- $`G`$ は内部の原子の一覧である。内部の原子を [06](06-combinatorial-layer.md) §2 のとおり $`(i, j, K)`$（点 $`i \lt j`$、型板 $`K`$）と書く。$`t`$ は [05](05-omegay-mountain.md) の一番上の節点に使うので、このノートでは型板を $`K`$ と書く。[03](03-sigma1-elementary.md) §7 の記号 $`\mathrm{Rel}_{t,i,j}`$、$`\mathrm{Top}_{t,i}`$ も $`\mathrm{Rel}_{K,i,j}`$、$`\mathrm{Top}_{K,i}`$ と書く。$`G`$ が $`f`$ で成り立つとは、$`G`$ のすべての $`(i, j, K)`$ で $`R(\mathrm{eval}\ K\ f, f(i), f(j))`$ が成り立つことである。
- $`N`$ は上端の原子の一覧である。上端の原子を $`(i, K)`$ と書く。$`N`$ の鍵 $`\mathrm{eval}\ K\ f`$ はどれも $`\theta`$ より小さい。$`N`$ は上端 $`b`$ について成り立つ。つまり $`N`$ のすべての $`(i, K)`$ で $`R(\mathrm{eval}\ K\ f, f(i), b)`$ である。
- $`\mathrm{cut}`$ は切れ目で、制御関係 $`R(\theta, f(\mathrm{cut}), b)`$ が成り立つ。

**反映する論理式.** 変数を $`v_0, \ldots, v_{n-1}`$ とする。$`j \lt \mathrm{cut}`$ の位置 $`j`$ をパラメータにして、値を $`f(j)`$ とする。残りの位置は証人の変数である。論理式 $`\varphi`$ は、次のリテラルの連言の前に、証人の変数の $`\exists`$ を付けたものである。

```math
\varphi \;=\; \exists \vec v\ \Bigl[\ \bigwedge_{j \lt n-1} v_j \lt v_{j+1}\ \land \bigwedge_{(i,j,K) \in G} \mathrm{Rel}_{K,i,j}(\vec v)\ \land \bigwedge_{(i,K) \in N} \mathrm{Top}_{K,i}(\vec v)\ \Bigr]
```

ここで $`\exists \vec v`$ は証人の変数だけを束ねる。$`\mathrm{Rel}_{K,i,j}(\vec v)`$ は $`R(\mathrm{eval}\ K\ \vec v, v_i, v_j)`$ である。$`\mathrm{Top}_{K,i}(\vec v)`$ は、高さ $`c`$ の構造で $`R(\mathrm{eval}\ K\ \vec v, v_i, c)`$ である。これは $`\Sigma_1`$ 論理式である（[03](03-sigma1-elementary.md) §2）。

**証明.**

1. 定義の式（[07](07-relation-r.md) §6）から、$`f(\mathrm{cut}) \lt b`$ と $`\mathfrak A^{f(\mathrm{cut})}_\theta \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_\theta`$ を得る。
2. パラメータ $`f(j)`$（$`j \lt \mathrm{cut}`$）は、$`f`$ が狭義増加なので $`f(\mathrm{cut})`$ より小さい。よって $`\varphi`$ は $`\mathfrak A^{f(\mathrm{cut})}_\theta`$ でも読める。
3. 高さ $`b`$ で、$`\vec v = f`$ が $`\varphi`$ の証人である。
   - 領域：すべての $`j`$ で $`f(j) \lt b`$。
   - 順序のリテラル：$`f`$ は狭義増加。
   - $`\mathrm{Rel}`$ のリテラル：$`G`$ が $`f`$ で成り立つ。
   - $`\mathrm{Top}`$ のリテラル：鍵 $`\mathrm{eval}\ K\ f`$ は $`\theta`$ より小さいので、上端の述語は定義されている。そして $`N`$ が上端 $`b`$ について成り立つ。
4. 1 から、$`\varphi`$ は $`\mathfrak A^{f(\mathrm{cut})}_\theta`$ でも真である。その証人とパラメータを合わせた列を $`g`$ とする。
5. $`g`$ は次を満たす。
   - 順序のリテラルから、$`g`$ は狭義増加である。
   - すべての $`j`$ で $`g(j) \lt f(\mathrm{cut})`$（証人は領域の中にある）。
   - $`j \lt \mathrm{cut}`$ なら $`g(j) = f(j)`$（パラメータ）。
   - $`\mathrm{Rel}`$ のリテラルから、$`G`$ が $`g`$ で成り立つ。
   - $`\mathrm{Top}`$ のリテラルは高さ $`f(\mathrm{cut})`$ で真である。よって鍵は $`\theta`$ より小さく、$`R(\mathrm{eval}\ K\ g, g(i), f(\mathrm{cut}))`$ である。つまり $`N`$ は上端 $`f(\mathrm{cut})`$ について成り立つ。
   - 各点で $`g \le f`$：$`j \lt \mathrm{cut}`$ なら等しい。$`j \ge \mathrm{cut}`$ なら $`g(j) \lt f(\mathrm{cut}) \le f(j)`$。$`\square`$

**使わなかったもの.** $`b`$ が Good であること。$`b`$ や $`f(\mathrm{cut})`$ が極限順序数であること。

**例（形だけ）.** [06](06-combinatorial-layer.md) §7 のくり返しで、$`(1,3,3)[2] = (1,3,2,5,7,12)`$ の 0 回目の継ぎ合わせ（列 2 と列 3 を足す）を見る。原子の一覧は Python で計算した（脚の原子の系 $`E_D(M)`$、$`D = 1`$）。型板は列の番号で書き、$`f_j = f(j)`$ で評価した鍵は $`(f_0, f_0)`$ のように書く。

- $`x_0 = 2`$、$`c_r = 0`$、$`w = 2`$、$`K_c = (\top, \top)`$ である。
- $`M(1,3,3)`$ の脚の原子は 6 個である。子の列が $`x_0`$ より小さいもの（予備 $`F`$）は $`(0, 1, (0,0))`$、$`(0, 1, (0,\top))`$、$`(0, 1, (\top,\top))`$ である。子の列が $`x_0`$ のもの（予備 $`T`$）は $`(1, 2, (0,0))`$、$`(0, 2, (0,\top))`$、$`(0, 2, (\top,\top))`$ である。最後のものが制御の原子 $`\mathrm{at}(t)`$ である。

この反映では次のようにとる。

| 記号 | 値 |
|---|---|
| 点 | 列 0、1（ラベル $`f_0 \lt f_1`$） |
| 上端 $`b`$ | $`f_2`$ |
| 切れ目 | $`c_r = 0`$（パラメータは無い） |
| $`\theta`$ | $`K_c`$ を評価した $`(\top, \top)`$ |
| $`G`$ | 列 1 の 3 つの原子 |
| $`N`$ | 上端の原子 $`(1, (0,0))`$ と $`(0, (0,\top))`$。$`T`$ の $`(1, 2, (0,0))`$ と $`(0, 2, (0,\top))`$ から作る |

$`N`$ の鍵は $`(f_0, f_0)`$ と $`(f_0, \top)`$ で、どちらも $`\theta = (\top, \top)`$ より小さい。制御関係 $`R((\top,\top), f_0, f_2)`$ は、$`\mathrm{at}(t)`$ が $`f`$ で成り立つことである。反映する論理式は次のとおりである。$`\mathrm{Top}[\kappa](x)`$ は、鍵 $`\kappa`$ の上端の述語が点 $`x`$ で成り立つこと、つまり高さ $`c`$ で $`R(\kappa, x, c)`$ を表す（型板の代わりに鍵の値を書いた）。

```math
\exists v_0\ \exists v_1\ \bigl[\ v_0 \lt v_1 \land R((v_0,v_0), v_0, v_1) \land R((v_0,\top), v_0, v_1) \land R((\top,\top), v_0, v_1) \land \mathrm{Top}[(v_0,v_0)](v_1) \land \mathrm{Top}[(v_0,\top)](v_0)\ \bigr]
```

- 高さ $`f_2`$ では $`(v_0, v_1) = (f_0, f_1)`$ が証人である。$`\mathrm{Top}`$ のリテラルは $`R((f_0,f_0), f_1, f_2)`$ と $`R((f_0,\top), f_0, f_2)`$ で、$`T`$ の原子が $`f`$ で成り立つことである。
- 反映すると、$`g_0 \lt g_1 \lt f_0`$ で、同じ論理式を高さ $`f_0`$ で満たすものが得られる。$`\mathrm{Top}`$ のリテラルは $`R((g_0,g_0), g_1, f_0)`$ と $`R((g_0,\top), g_0, f_0)`$ になる。
- 新しいラベルは $`(g_0, g_1, f_0, f_1)`$ である。どれも $`f_2`$ より小さい。

出力の列 1〜3 の脚の原子は、新しいラベルで次のように成り立つ（原子と分類は Python で計算した）。

| 原子 | 分類 | 成り立つ理由 |
|---|---|---|
| 列 1 の 3 つ | 基 | $`G`$ が $`g`$ で成り立つ |
| $`(1, 2, (0,0))`$ | 継ぎ目 | $`R((g_0,g_0), g_1, f_0)`$（反映で得た上端のリテラル） |
| $`(0, 2, (0,\top))`$ | 継ぎ目 | $`R((g_0,\top), g_0, f_0)`$（同上） |
| $`(2, 3, (0,0))`$ | 予備 | $`F`$ の $`(0,1,(0,0))`$ から $`R((f_0,f_0), f_0, f_1)`$。$`(g_0,g_0) \le (f_0,f_0)`$ なので鍵の弱化 |
| $`(2, 3, (2,2))`$ | 予備 | $`R((f_0,f_0), f_0, f_1)`$ |
| $`(2, 3, (2,\top))`$ | 予備 | $`F`$ の $`(0,1,(0,\top))`$ から $`R((f_0,\top), f_0, f_1)`$ |
| $`(2, 3, (\top,\top))`$ | 予備 | $`F`$ の $`(0,1,(\top,\top))`$ から $`R((\top,\top), f_0, f_1)`$ |

次の 1 回目の継ぎ合わせ（列 4 と列 5 を足す）では、切れ目は $`c_r + w = 2`$（ラベル $`f_0`$）で、列 0、1 のラベル $`g_0, g_1`$ がパラメータになる。反映で $`g_1 \lt g'_2 \lt g'_3 \lt f_0`$ を得て、新しいラベルは $`(g_0, g_1, g'_2, g'_3, f_0, f_1)`$ になる。これが $`(1,3,2,5,7,12)`$ の表現で、どのラベルも $`f_2`$ より小さい。ラベルの具体的な値は分からない。ここで示したのは形だけである。

## 3. 最初の表現

[08](08-closure-chain.md) §1 のとおり、周りの構造（高さ $`\omega_1`$ で、上端の述語をすべての鍵で定義した構造）を $`\mathfrak B`$ と書く。$`\mathfrak B`$ の上端の述語は $`R(\mathrm{eval}\ K\ \vec v, v_i, \omega_1)`$ である。$`\mathrm{Good}(\alpha)`$ は、$`\alpha`$ より小さいパラメータを持つ $`\Sigma_1`$ 論理式が $`\mathfrak B`$ で真なら、$`\alpha`$ より小さい証人があることである。

### 3.1 上端の述語の絶対性

**補題 1.** ラベル $`\alpha`$ について $`\mathrm{Good}(\alpha)`$、$`\alpha \lt \omega_1`$ とする。鍵 $`\kappa`$ について、次を仮定する：すべての鍵 $`\kappa' \lt \kappa`$ とラベル $`x \lt \alpha`$ で $`R(\kappa', x, \alpha) \iff R(\kappa', x, \omega_1)`$。このとき、$`\alpha`$ より小さいパラメータ $`\vec y`$ を持つすべての $`\Sigma_1`$ 論理式 $`\varphi`$ について、次が成り立つ。

```math
\mathfrak A^{\alpha}_{\kappa} \models \varphi(\vec y) \iff \mathfrak A^{\omega_1}_{\kappa} \models \varphi(\vec y)
```

**証明.** 2 つの構造で、順序と内部の関係は同じである。違うのは上端の述語だけである。$`\mathfrak A^{\alpha}_{\kappa}`$ の上端の述語は $`R(\kappa', x, \alpha)`$、$`\mathfrak A^{\omega_1}_{\kappa}`$ の上端の述語は $`R(\kappa', x, \omega_1)`$ である。どちらも鍵 $`\kappa' \lt \kappa`$ のところでだけ定義される。

- 高さ $`\alpha`$ から高さ $`\omega_1`$：証人 $`\vec w`$ は $`\alpha`$ より小さく、したがって $`\omega_1`$ より小さい。$`\mathrm{Top}`$ のリテラルは鍵 $`\kappa' \lt \kappa`$、点 $`w_i \lt \alpha`$ のところで読むので、仮定から真偽は同じである。
- 高さ $`\omega_1`$ から高さ $`\alpha`$：証人 $`\vec v \lt \omega_1`$ を取る。
  1. 真のリテラルはどれも $`\mathfrak B`$ でも真である。$`\mathrm{Top}`$ のリテラルは、真なら定義されていて（鍵 $`\lt \kappa`$）、$`\mathfrak B`$ と同じ $`R(\cdot, \cdot, \omega_1)`$ を読むからである。よって $`\vec v`$ は $`\mathfrak B`$ で $`\varphi`$ の証人である。
  2. $`v_j \lt \alpha`$ となる位置 $`j`$ もパラメータにした論理式 $`\varphi'`$ を作る。パラメータはどれも $`\alpha`$ より小さい。$`\mathrm{Good}(\alpha)`$ から、$`\mathfrak B`$ での $`\varphi'`$ の証人 $`\vec w`$ で、$`\alpha`$ より小さいものがある。
  3. 各点で $`\vec w \le \vec v`$ である。パラメータの位置では等しい。ほかの位置では $`w_j \lt \alpha \le v_j`$ である。
  4. 単調性（[03](03-sigma1-elementary.md) §7）から $`\mathrm{eval}\ K\ \vec w \le \mathrm{eval}\ K\ \vec v \lt \kappa`$ である。よって $`\vec w`$ の $`\mathrm{Top}`$ のリテラルも鍵が $`\kappa`$ より小さく、$`\mathfrak A^{\omega_1}_{\kappa}`$ で定義されていて真である（[03](03-sigma1-elementary.md) §8）。
  5. 点 $`w_i \lt \alpha`$ と鍵 $`\lt \kappa`$ なので、仮定から $`\mathrm{Top}`$ のリテラルを高さ $`\alpha`$ のものに替えられる。よって $`\vec w`$ は $`\mathfrak A^{\alpha}_{\kappa}`$ での証人である。$`\square`$

**定理 2（上端の述語の絶対性）.** ラベル $`\alpha`$ について $`\mathrm{Good}(\alpha)`$、$`\alpha \lt \omega_1`$ とする。すべての鍵 $`\kappa`$ とラベル $`x \lt \alpha`$ について、次が成り立つ。

```math
R(\kappa, x, \alpha) \iff R(\kappa, x, \omega_1)
```

**証明.** $`\kappa`$ についての整礎帰納法（[02](02-well-founded.md) §2）で示す。鍵の順序は整礎である（[02](02-well-founded.md) §3）。$`\kappa`$ より小さい鍵で定理が成り立つとする。定義の式（[07](07-relation-r.md) §6）で両辺を開く。

```math
R(\kappa, x, \alpha) \iff x \lt \alpha \land \mathfrak A^{x}_{\kappa} \preccurlyeq_{\Sigma_1} \mathfrak A^{\alpha}_{\kappa}, \qquad R(\kappa, x, \omega_1) \iff x \lt \omega_1 \land \mathfrak A^{x}_{\kappa} \preccurlyeq_{\Sigma_1} \mathfrak A^{\omega_1}_{\kappa}
```

$`x \lt \alpha`$ と $`x \lt \omega_1`$ はどちらも真である。右の項は、$`x`$ より小さいパラメータの論理式について、$`\mathfrak A^{x}_{\kappa}`$ での真偽を $`\mathfrak A^{\alpha}_{\kappa}`$ または $`\mathfrak A^{\omega_1}_{\kappa}`$ での真偽と比べる。帰納法の仮定から補題 1 が使えるので、$`\mathfrak A^{\alpha}_{\kappa}`$ と $`\mathfrak A^{\omega_1}_{\kappa}`$ での真偽は同じである（パラメータは $`x \lt \alpha`$ より小さい）。よって右の項どうしも同値である。$`\square`$

**系 3.** $`\mathrm{Good}(\alpha)`$、$`\alpha \lt \omega_1`$ なら、すべての鍵 $`\kappa`$ と、$`\alpha`$ より小さいパラメータの $`\Sigma_1`$ 論理式 $`\varphi`$ について、$`\mathfrak A^{\alpha}_{\kappa} \models \varphi \iff \mathfrak A^{\omega_1}_{\kappa} \models \varphi`$。

**証明.** 定理 2 から、補題 1 の仮定がすべての $`\kappa`$ で成り立つ。$`\square`$

### 3.2 Good な点どうしは R の関係にある

**定理 4.** ラベル $`\alpha, \beta`$ について $`\mathrm{Good}(\alpha)`$、$`\mathrm{Good}(\beta)`$、$`\alpha \lt \beta \lt \omega_1`$ とする。このとき、すべての鍵 $`\kappa`$ で $`R(\kappa, \alpha, \beta)`$ である。

**証明.** 定義の式で示す。$`\alpha \lt \beta`$ である。鍵 $`\kappa`$ の論理式 $`\psi`$ と、$`\alpha`$ より小さいパラメータについて、系 3 を $`\alpha`$ と $`\beta`$ で使う（パラメータは $`\beta`$ よりも小さい）。

```math
\mathfrak A^{\alpha}_{\kappa} \models \psi \iff \mathfrak A^{\omega_1}_{\kappa} \models \psi \iff \mathfrak A^{\beta}_{\kappa} \models \psi
```

よって $`\mathfrak A^{\alpha}_{\kappa} \preccurlyeq_{\Sigma_1} \mathfrak A^{\beta}_{\kappa}`$ である。$`\square`$

鍵 $`\kappa`$ はどれでもよい。Good な点どうしは、どの鍵でも関係にある。

### 3.3 すべての有限の図式に表現がある

**定理 5（最初の表現）.** どの図式 $`(G, N)`$ にも、ラベル $`\beta \lt \omega_1`$ と狭義増加のラベル $`f`$（すべての点で $`f \lt \beta`$）があって、$`G`$ が $`f`$ で成り立ち、$`N`$ が上端 $`\beta`$ について成り立つ。

**証明.** $`n`$ を図式の点の数とする。Good な点の列（[08](08-closure-chain.md) §7）を使い、$`\beta := p_n`$、$`f(j) := p_j`$ とする。

- $`p_0 \lt p_1 \lt \cdots \lt p_n \lt \omega_1`$ なので、$`f`$ は狭義増加で、$`f \lt \beta \lt \omega_1`$ である。
- 内部の原子 $`(i, j, K)`$ は $`i \lt j`$ なので、定理 4 から $`R(\mathrm{eval}\ K\ f, p_i, p_j)`$ である。
- 上端の原子 $`(i, K)`$ は $`i \lt n`$ なので、定理 4 から $`R(\mathrm{eval}\ K\ f, p_i, p_n)`$ である。$`\square`$

1 つの列 $`p_0 \lt p_1 \lt \cdots`$ が、すべての図式を同時に表現する。鍵の条件は要らない。

**山の表現.** 山 $`M`$ の脚の原子の系 $`E_D(M)`$（[06](06-combinatorial-layer.md) §10）は有限個の原子 $`(p, c, K)`$（$`p \lt c`$）の一覧である。これを内部の原子の一覧 $`G`$ とし、$`N`$ を空にして定理 5 を使う。得られる $`f`$ は、[06](06-combinatorial-layer.md) §4 の意味で $`M`$ の表現である。よって、どの山にも表現がある。

**例.** $`(1,3,3)`$ の山（$`D = 1`$）の脚の原子は、§2 の例の 6 個である（Python で計算した）。$`f = (p_0, p_1, p_2)`$ とすると、成り立つべき関係は次の 6 つで、どれも定理 4 から成り立つ。

```math
R((p_0,p_0), p_0, p_1),\ R((p_0,\top), p_0, p_1),\ R((\top,\top), p_0, p_1),\ R((p_0,p_0), p_1, p_2),\ R((p_0,\top), p_0, p_2),\ R((\top,\top), p_0, p_2)
```

### 3.4 制御つきの最初の表現

**定理 6（制御つきの最初の表現）.** 図式 $`(G, N)`$ と、上端の原子 $`(q, K_c)`$ を 1 つ取る。これを制御の原子と呼ぶ。$`N`$ のどの原子 $`(i, K)`$ でも、列の番号で評価した鍵（[06](06-combinatorial-layer.md) §1）が $`K`$ のほうが $`K_c`$ より小さいとする。このとき、ラベル $`\beta \lt \omega_1`$ と狭義増加のラベル $`f \lt \beta`$ があって、次が成り立つ。

1. $`G`$ が $`f`$ で成り立ち、$`N`$ が上端 $`\beta`$ について成り立つ。
2. $`N`$ の鍵はどれも $`\mathrm{eval}\ K_c\ f`$ より小さい。
3. 制御関係 $`R(\mathrm{eval}\ K_c\ f, f(q), \beta)`$ が成り立つ。

**証明.** $`N`$ に $`(q, K_c)`$ を足した図式に定理 5 を使う。1 と 3 はそこから出る。2 は、$`f`$ が狭義増加で、列の番号で評価した鍵が小さければ $`f`$ で評価した鍵も小さいこと（[06](06-combinatorial-layer.md) §1）から出る。$`\square`$

[06](06-combinatorial-layer.md) §8 の降下は、定理 6 を使わない。くり返しの最初の状態（[06](06-combinatorial-layer.md) §7 の定理 5 の $`i = 0`$ の状態）は、$`s`$ の表現 $`f`$ から直接作れるからである。予備 $`F`$、予備 $`T`$、制御の原子 $`\mathrm{at}(t)`$ はどれも $`E_D(M(s))`$ の原子である。上端を $`\beta = f(x_0)`$ とすると、どれも $`f`$ で成り立つ。

## 4. まとめ

- 意味の層（[07](07-relation-r.md) の関係 $`R`$）は、[06](06-combinatorial-layer.md) §5 の 3 つの定理を満たす。鍵の弱化は [07](07-relation-r.md) §7、有限反映は §2、最初の表現は §3.3 の定理 5 である。
- [06](06-combinatorial-layer.md) §8 の降下の定理は、この 3 つの定理と分類から出る。分類は、[06](06-combinatorial-layer.md) §11 の分類の補題の形で [10](10-official-descent.md) で証明する。これで [05](05-omegay-mountain.md) §8 の最終定理が出る。
- **強さ.** 証明は選択公理を含む通常の集合論で行い、$`\omega_1`$ の正則性を使う。ラベルは $`\omega_1`$ より小さい Good な点で、具体的な値は分からない。そのため、この証明から順序数の上界は出ない。順序数の表記系（順序数を有限の記号列で表す方法）も得られない。

## 5. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md) の冒頭 | Phyrion 氏の反映の定理をそのまま使うこと |
| [README](../README.md)「状態」 | 最終定理と、使う公理 |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §1 | 組合せの層が意味の層から使う 3 つの定理 |
| [notes/02-wmwy-design.md](../notes/02-wmwy-design.md) §3.2、§3.3 | 有限反映（§2）、上端の述語の絶対性と Good な点の関係（§3） |
| [notes/04-official-design.md](../notes/04-official-design.md) §1.1、§1.2 | 最初の表現と、反映による降下 |
