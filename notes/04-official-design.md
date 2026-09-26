[← PLAN](../PLAN.md)

# 公式の ω-Y の整礎性の証明の設計

4 つ目のノートである。Phyrion 氏の証明の枠組みを公式の ω-Y に移す設計を書く。調べた日は 2026-09-23 である。

- 公式の展開規則は [03-official-rule.md](03-official-rule.md) にある。Lean の定義は `OmegaY.Official.expand` である。
- Phyrion 氏の証明は [omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)（リビジョン `33c16a8`、Apache-2.0）である。このリポジトリの `OmegaY/` にその写しがある。
- 数値の試験は [reference/official/reserve.cjs](../reference/official/reserve.cjs) で行った。

## 0. 要約

- Phyrion 氏の証明の核は、区画ごとの反映（splice）の定理 `Splice.iterated_reservoirs` である。この定理は、原子（2 つの列と鍵の組）の一覧についての一般的な定理で、展開の規則に依らない。そのまま使える。
- 展開の規則に依るのは、「新しい山の原子が、古い山の原子から 3 つの型のどれかで得られる」という分類だけである。Phyrion 氏は、原子として山の本物の辺だけを使った。公式の ω-Y では、この分類が 39090 回の標準形の展開のうち 2032 回で破れる（§2）。
- **新しい設計（§3）.** 原子を「節点ごとの脚の原子」に替える。列 $`c \ge 1`$ の節点 $`u`$ ごとに、$`u`$ の左の脚の列 $`\ell(u)`$ と $`c`$ の間に、$`u`$ から仮に辺を出したときの鍵をつけた原子をひとつ置く。制御（反映の強さを決める原子）は、末列の一番上の節点の脚の原子にする。
- **数値の結果（§4）.** この原子の系で、分類は試したすべての展開で成り立った。標準形 39090 回、合法な列 54498 回（重複を含む）、$`n = 4, 5`$ の 20102 回、weak の展開 46290 回で、失敗は 0 回である。脚の原子のどれかの種類を外すと、分類は破れる。
- **Lean（§5）.** 原子の系と分類の判定を定義し、474 個の展開で判定が真になることを確かめた。さらに、分類を仮定にして公式の展開の整礎性を証明した（`sorry` 無し）。ただし最初の仮定 `Descent.ClassificationHolds` は空の列のせいで偽だった（`not_classificationHolds`）ので、空でない列に限った `ClassificationHoldsNE` と、それを次数と原子の分類に分けた `DegreeAndAtomsHold` に直した（`Reconstruction.wellFounded_of_parts`、§6.1）。
- **未解決（§6）.** 分類がすべての展開で成り立つことは、証明していない。これが残る組合せの補題である。

## 1. Phyrion 氏の証明の枠組み

### 1.1 表現

記法は 01-feasibility §1.1 と同じである。$`s = (s_0, …, s_{x_0})`$ の山を $`M(s)`$ と書く。辺 $`e = (u, u^+)`$ の父を $`\pi(e)`$、尺度 $`k`$ の根を $`\rho_k`$ と書く。

鍵の型板は、尺度 $`D, D-1, …, 0`$ の順に並べた、列の番号か $`\top`$ の列である。比較は尺度 $`D`$ からの辞書式で、$`\top`$ が最大である。ラベル $`f`$ で評価した鍵を $`K(f)`$ と書く。

原子は組 $`(p, c, K)`$ である（$`p \lt c`$ は列、$`K`$ は鍵の型板）。ラベル $`f`$ で原子が成り立つとは、

```math
R\bigl(K(f),\ f(p),\ f(c)\bigr)
```

のことである。$`R`$ は意味の層の関係（[02-wmwy-design.md](02-wmwy-design.md) の $`\Sigma_1`$ 初等性）である。

$`s`$ の表現とは、狭義増加のラベル $`f : \{0, …, x_0\} \to [0, \omega_1)`$ で、決められた原子の一覧 $`\mathcal E(s)`$ がすべて成り立つものである。Phyrion 氏は $`\mathcal E(s)`$ を本物の辺の一覧にした（`Frame.KeyRepresentation`）。

整礎性は次の 2 つから出る（`DynamicsRepresentationRank.lean`）。

1. どの $`s`$ にも表現がある。閉じた点を使えば、どんな有限の原子の一覧も成り立つ（`OrdinalSupply.initial_finite_graph`）。
2. **降下.** $`s`$ の表現 $`f`$ から、$`s[n]`$ の表現 $`g`$ で、どのラベルも $`f(x_0)`$ より小さいものが作れる。

2 があれば、最後のラベルについての帰納法で、$`s`$ から始まる展開の列はどれも有限である。

### 1.2 反映による降下

$`s_{x_0} \gt 1`$、$`n \ge 1`$ とする。根の列を $`c_r`$、幅を $`w = x_0 - c_r`$、$`\beta = f(x_0)`$ とする。列の写像を

```math
\mu_b(c) = \begin{cases} c & (c \lt c_r) \cr c + bw & (c \ge c_r) \end{cases}
```

とする。$`s[n]`$ は長さ $`x_0 + nw`$ で、$`s[b]`$ はその接頭辞である。

降下は、区画をひとつずつ足す反映の繰り返しである（`Splice.iterated_reservoirs`）。$`b`$ 回目（$`b = 0, …, n-1`$）では、列 $`c_r + bw`$ 以上を $`f(c_r + bw)`$ の下へ反映し、境界の列 $`B = x_0 + bw`$ と新しい区画 $`[B, B+w)`$ に古いラベルを置く。定理が使うのは次のデータである。

- $`F`$（内部の予備）：$`\mathcal E(s)`$ の原子で、子が $`x_0`$ より小さいもの。
- $`T`$（上端の予備）：$`\mathcal E(s)`$ の原子で、子が $`x_0`$ のもの。$`R(K(f), f(\ell), \beta)`$ が成り立つ。
- 制御：$`T`$ の原子のひとつで、父が $`c_r`$ のもの。鍵を $`K_c`$ と書く。
- $`G_b`$：$`\mathcal E(s[n])`$ の原子で、子が $`x_0 + bw`$ より小さいもの。

定理の仮定は、$`\mathcal E(s[n])`$ の原子 $`(P, X, K)`$ のすべてが次のどれかであることである。これを**分類**と呼ぶ。

- **(基)** $`X \lt x_0`$ のとき：$`\mathcal E(s)`$ に $`(P, X, K')`$ があり、$`K \le K'`$。
- それ以外では $`b = \lfloor (X - x_0)/w \rfloor`$、$`B = x_0 + bw`$ とする。
- **(予備)** $`P \lt c_r`$ または $`P \ge B`$ である。$`P' = P`$（$`P \lt c_r`$）、$`P' = c_r + (P - B)`$（$`P \ge B`$）とすると、$`F`$ に $`(P', c_r + X - B, K')`$ があり、$`K \le \mu_{b+1}(K')`$。
- **(継ぎ目)** $`X = B`$ で、$`K \lt \mu_b(K_c)`$ であり、$`T`$ に $`(\ell, x_0, K')`$ があって $`\mu_b(\ell) = P`$、$`K \le \mu_b(K')`$。

$`\mu_b(K')`$ は、鍵の型板の各列に $`\mu_b`$ を当てたものである。予備の型は古いラベルの関係をそのまま写し、継ぎ目の型は制御の関係を反映して得る。継ぎ目の鍵は、制御の鍵より真に小さくなければならない。これが反映の定理の制約である。

分類は有限の組合せの主張で、ラベルも意味の層も使わない。$`s_{x_0} = 1`$ または $`n = 0`$ のときは、$`s[n]`$ は $`s`$ の末項を消したものなので、(基) だけでよい。

### 1.3 そのまま使えるもの

| 部分 | ファイル | 公式の ω-Y で |
|---|---|---|
| 行、正準の山 | `Rows`、`Canonical` | そのまま（01-feasibility の I7） |
| 尺度の根、鍵の型板 | `Geometry/MountainKeys.lean` | そのまま |
| 意味の層 | `Por/`、`OmegaY/Reflection*`、`Model`、`Keys`、`KeyReflection` | そのまま |
| 反映の繰り返し | `Splice.lean`、`Splice/*` | そのまま。原子の一覧についての一般的な定理である |
| 最初の表現 | `OrdinalSupply.initial_finite_graph` | そのまま。どんな有限の原子の一覧にも使える |
| ラベルについての帰納法 | `DynamicsRepresentationRank.lean` | 考え方はそのまま。公式の展開と新しい表現について書き直す |

### 1.4 壊れるもの

- `ActualCopiedKeyBound`（写した辺の鍵の上界、01-feasibility の I3）と、充填の辺を制御の辺に帰着させる補題（`ActualFillControlEdge`、`ActualFillCopiedKey`、I4）。
- これらを使って本物の辺の分類を示す `ActualSpliceRepresentation` と、その下の weak の実行の解析（`Expansion/Actual*` の大部分）。どれも weak の `expandDiagram` の定義に沿った証明なので、公式の展開には使えない。
- `ActualInitialReservoir` は $`F`$ を減一の山から読む。公式の展開の源は元の山 $`M(s)`$ なので、$`F = \mathcal E(s)`$ の形に書き直す。

## 2. 本物の辺だけでは足りない

$`\mathcal E(s)`$ を本物の辺にすると（Phyrion 氏の表現）、公式の展開で分類が破れる。

- 標準形の展開 39090 回（§4.1 の標本）のうち 2032 回で破れる。継ぎ目の型で破れるのが 1378 回、予備の型で破れるのが 1248 回である（重なりがある）。weak の展開では 0 回である。
- 最小の例は $`(1,3,3)[2] = (1,3,2,5,7,12)`$ である。出力の列 4 の辺 $`0 \to 1`$ は、父が列 3 にある（公式の充填、01-feasibility §2.3）。$`b = 1`$ の継ぎ目の型に入るには、$`T`$ に列 1 から列 2 への原子が要る。$`(1,3,3)`$ の列 2 の辺の父はどれも列 0 なので、そのような原子は無い。
- これは 01-feasibility §3.1 の型 A、型 B と同じ破れ方である。

## 3. 新しい原子の系

### 3.1 定義

$`M`$ を正準の山、$`D`$ を行の次数の上界とする。

- **脚.** 列 $`c`$ の節点 $`u`$ の左の脚の列 $`\ell(u)`$ は、$`u`$ へ下から入る辺の父の列である。$`u`$ が最下行なら $`\ell(u) = c - 1`$ とする。Phyrion 氏の格納の形では、どちらも $`u`$ のセルに記録された左の端点の列である（最下行の節点の左の端点は、ひとつ左の列の幻の節点である）。
- **脚の先.** $`p_u`$ を、列 $`\ell(u)`$ の節点で、行が $`\mathrm{row}(u)`$ 以下の最も高いものとする。最下行の節点があるので、いつも存在する。
- **仮の鍵.** 行 $`\mathrm{row}(u)`$ の節点から、父 $`p`$ への辺が出ているとしたときの Phyrion 氏の鍵を $`\kappa_D(u; p)`$ とする。すなわち $`d = \mathrm{jump}(\mathrm{row}(u), \mathrm{row}(p))`$ として、尺度 $`k = D, …, 0`$ の成分は

```math
\kappa_D(u; p)_k = \begin{cases} \mathrm{col}\,\rho_k(p) & (d \le k) \cr \top & (d \gt k) \end{cases}
```

  である。
- **脚の原子.** $`a(u) = \bigl(\ell(u),\ c,\ \kappa_D(u; p_u)\bigr)`$。
- **原子の系.**

```math
\mathcal E_D(M) = \{\, a(u) : u \text{ は列 } c \ge 1 \text{ の節点} \,\}
```

- **制御.** 末列 $`x_0`$ の一番上の節点 $`t`$ の脚は、$`t`$ へ入る辺の父、すなわち根 $`r`$ の列 $`c_r`$ である。制御を $`a(t) = (c_r, x_0, K_c)`$ とする。

### 3.2 性質

- **本物の辺を含む.** 本物の辺 $`e = (u, u^+)`$ の父の列は $`\ell(u^+)`$ である。その鍵は $`a(u^+)`$ の鍵以下である（試した 354559 本の辺のすべてで成り立った）。したがって $`\mathcal E_D`$ の表現は、鍵の弱化で Phyrion 氏の表現（本物の辺）を含む。
- **制御は最も強い.** $`a(t)`$ の鍵は、$`\mathcal E_D(M(s))`$ の原子で $`c_r`$ から $`x_0`$ へのものの中で最大である（標準形 13030 式のすべてで成り立った）。
- **一番上の節点の原子.** 一番上の節点 $`u`$ には上への辺が無い。$`a(u)`$ は「$`u`$ の列がもっと高かったら出たはずの辺」の鍵である。脚の先が低いと、跳び $`d`$ が大きくなり、鍵の成分の多くが $`\top`$ になる。例えば $`(1,3,3)`$ の列 2 の一番上の節点（行 $`\omega`$）では、$`a(u) = (0, 2, (\top, \top))`$ である。

### 3.3 例

$`D = 1`$ とする。鍵は $`(\rho_1, \rho_0)`$ の順に書く。

**$`(1,3,4)[1] = (1,3,3)`$.** $`M(1,3,4)`$ の列 2 は `0, 1←c1@0` である。根は $`c_r = 1`$、$`w = 1`$。

- 制御は $`a(t)`$、$`t = (2, 1)`$ である。$`\ell(t) = 1`$、$`p_t = (1, 1)`$、跳び 0 なので $`K_c = (\rho_1(1,1), \rho_0(1,1)) = (0, 1)`$。本物の辺 $`(2,0) \to (2,1)`$ の鍵 $`(0, 0)`$ より大きい。
- 出力 $`(1,3,3)`$ の列 2 は境界の列 $`B = 2`$ である。その最下行の節点の脚の原子は $`(1, 2, (0,0))`$ で、列 1 は反映される区画にある。継ぎ目の型で、$`(0,0) \lt \mu_0(K_c) = (0,1)`$ と、$`T`$ の原子 $`a(t)`$ で分類される。

**$`(1,3,3)[2] = (1,3,2,5,7,12)`$.** §2 で本物の辺では分類できなかった原子である。

- $`M(1,3,3)`$ の列 2 の最下行の節点 $`u = (2, 0)`$ の脚の原子は $`a(u) = (1, 2, (0,0))`$ である（脚は $`c - 1 = 1`$）。これが $`T`$ に入る。
- 出力の辺 $`(3, 4)`$（鍵 $`(0,0)`$、$`b = 1`$）は、$`\mu_1(a(u)) = (1+2, 2+2, (2,2))`$ で覆われる。制御は $`a((2,\omega)) = (0, 2, (\top,\top))`$ なので、継ぎ目の鍵の条件も成り立つ。

2 つの例をつなぐと、次のことがわかる。$`(1,3,3)`$ の表現には列 1 と列 2 の関係が要る。それを $`(1,3,4)`$ の表現から反映で作るには、$`(1,3,4)`$ の制御が、本物の辺 $`(0,0)`$ より強くなければならない。脚の原子 $`a(t)`$ がこの強さを与える。

## 4. 数値の試験

### 4.1 方法

[reference/official/reserve.cjs](../reference/official/reserve.cjs) で、原子の系の候補ごとに、§1.2 の分類をすべての展開と $`b`$ で確かめた。

- 展開は自前の実装 `omegay.cjs`（03-official-rule の §6 で公式のプログラムと照合したもの）で計算した。値は整数（BigInt）で扱う。
- $`D`$ は、$`M(s)`$ と $`M(s[n])`$ の行の次数の最大である。
- 制御は、断りが無ければ、系の原子で $`c_r`$ から $`x_0`$ へのものの中で鍵が最大のものである（`reserve.cjs` の既定）。脚の原子の系では、これは $`a(t)`$ と一致する（§3.2）。§4.3 の試験は、制御を $`a(t)`$ に固定して行った（`--top-control`）。Lean の判定（§5）も $`a(t)`$ を使う。
- 標本は 03-official-rule §6.2 と同じである。標準形は S1〜S3、S6（13030 式）、合法な列は S4、S5、R1 である。

### 4.2 候補の比較（標準形、$`n = 1,2,3`$、39090 回）

| 候補 | 原子 | 制御 | 失敗 | 最小の例 |
|---|---|---|---:|---|
| edges | 本物の辺 | 本物の上の辺 | 2032 | $`(1,3,3)[2]`$、継ぎ目 |
| legNoBottom | 本物の辺と、最下行でない節点の脚の原子 | $`a(t)`$ | 668 | $`(1,3,3)[2]`$、継ぎ目 |
| legNoTop | 本物の辺と、一番上でない節点の脚の原子 | 最大の原子 | 17106 | $`(1,2,3)[1]`$、継ぎ目 |
| legNoTop | 同上 | $`a(t)`$（系の外） | 18 | $`(1,3,2,5,7,12,19,25,30)[1]`$、予備 |
| leg | 本物の辺と、すべての脚の原子 | 本物の上の辺 | 35538 | $`(1,2)[1]`$、継ぎ目 |
| **legOnly** | **すべての脚の原子** | $`a(t)`$ | **0** | |
| **leg** | **本物の辺と、すべての脚の原子** | $`a(t)`$ | **0** | |

- legNoTop の 18 回は、03-official-rule §5 の性質 Q を満たす式の $`n = 1,2,3`$ である。標準形の標本で Q を満たす式は 6 つあり（[ascension-gap.cjs](../reference/official/ascension-gap.cjs) で数えた）、そのすべてで破れた。上がる列の一番上の節点の行が、充填で写される根の行になる場合である。一番上の節点の脚の原子が要る。
- 制御を本物の上の辺にすると、どの脚の原子の系でも、継ぎ目の型で大量に破れる。反映の強さが足りない。

### 4.3 脚の原子の系の試験

| 標本 | 式 | 展開 | 失敗 |
|---|---:|---:|---:|
| 標準形 S1〜S3、S6、$`n = 1,2,3`$ | 13030 | 39090 | 0 |
| 同、$`D`$ を 1 大きくする | 13030 | 39090 | 0 |
| S1〜S3、$`n = 4, 5`$ | 10051 | 20102 | 0 |
| 合法な列 S4（長さ 5 以下、項 7 以下） | 2400 | 7200 | 0 |
| 合法な列 S5（長さ 6 以下、項 5 以下） | 3124 | 9372 | 0 |
| 無作為な合法な列 R1 | 12642 | 37926 | 0 |
| weak の展開、S1〜S3、S6 | 13030 | 39090 | 0 |
| weak の展開、S4 | 2400 | 7200 | 0 |

- 標本は重なるが、表の数は標本ごとの数である。
- $`D`$ を次数より小さく固定すると破れる（$`D = 0`$ で 16932 回、$`D = 1`$ で 4734 回）。$`D`$ は行の次数の上界でなければならない。
- weak の展開でも同じ系で分類が成り立った。Phyrion 氏の本物の辺の系も weak では成り立つ（0 回）。

### 4.4 探索の経過

最初は制御を本物の上の辺に固定して探した。このときは、鍵に最も低い座標（父の列）を足し、行の中の辺の脚と仮の辺の脚を加えた系で、標準形の失敗が 0 回になった。制御は $`T`$ のどの原子でもよいことに気づき、$`a(t)`$ を制御にすると、§3 の単純な系で足りた。

制御を固定したまま、必要な鍵を子孫から逆にたどって計算する実験もした（深さ 6 まで）。$`(1,3,4)`$ の列 1 と列 2 の関係には、本物の辺より強い鍵 $`(0, 1)`$ が要ると出た。これは §3.3 の $`a(t)`$ の鍵と一致する。

## 5. Lean での形式化

### 5.1 済んだこと：定義と有限の判定

[OmegaY/Official/Reserve.lean](../OmegaY/Official/Reserve.lean)（名前空間 `OmegaY.Official.Reserve`）で、§3 の原子の系と §1.2 の分類を、計算できる関数として定義した。

| Lean の名前 | 内容 |
|---|---|
| `RawAtom`、`RawKey` | 原子 `(parent, child, key)`。鍵は尺度 $`D, …, 0`$ の成分の列で、`none` が $`	op`$ |
| `rawParent`、`scaleRoot`、`keyAt` | 生の父、尺度の根、Phyrion 氏の鍵の型板 |
| `highestAtMost`、`legAtom?`、`atoms` | 脚の先 $`p_u`$、脚の原子 $`a(u)`$、原子の系 $`\mathcal E_D`$ |
| `root?` | 根の列と制御 $`a(t)`$ |
| `keyLt`、`keyLe`、`mapKey` | 鍵の辞書式の比較（`Pi.Lex` と同じ形）、列の写像 $`\mu_b`$ |
| `baseOK`、`reserveOK`、`seamOK` | 分類の 3 つの型 |
| `classifiedWith`、`classifiedB` | 1 回の展開 $`s[n]`$ の分類の判定 |
| `edgeAtoms`、`classifiedEdgesB` | 比較のための、本物の辺だけの系 |

`classifiedB s n D` は、分類のほかに、分類を反映の定理へ渡すのに要る形も確かめる。出力の正準の山が作れること、出力の長さが $`x_0 + nw`$ であること、両方の山の行の次数が $`D`$ 以下であることである。

次の形の性質は判定に入れず、証明した（[OmegaY/Official/ReserveShape.lean](../OmegaY/Official/ReserveShape.lean)）。どれも、正しい形の山（`MountainValid`。正準の山はこれを満たす）についての定理である。

- `atoms_wellFormed`：すべての脚の原子は正しい形をしている（$`p \lt c \lt`$ 幅、鍵の長さ $`D+1`$、鍵の列が父以下）。
- `root?_spec`：`root?` が根を返すとき、末列は $`x_0 = `$ 幅 $`- 1`$、根の列は $`x_0`$ より左にあり、制御 $`a(t)`$ は脚の原子のひとつである。

[OmegaY/Official/ReserveCheck.lean](../OmegaY/Official/ReserveCheck.lean) で、`Check.lean` の 474 個の展開（公式のプログラムと照合したもの）について `#guard` で確かめた。

| 系 | 分類が成り立った展開 |
|---|---:|
| 脚の原子（`classifiedB`） | 474 / 474 |
| 本物の辺だけ（`classifiedEdgesB`） | 421 / 474 |

本物の辺だけで成り立った 421 個は、weak の規則が公式と同じ値を出す 421 個と数が一致する。

### 5.2 済んだこと：分類を仮定にした整礎性

[OmegaY/Official/Descent.lean](../OmegaY/Official/Descent.lean)（名前空間 `OmegaY.Official.Descent`）で、次を証明した。`sorry` は無く、公理は `propext`、`Classical.choice`、`Quot.sound` だけである。

| Lean の名前 | 内容 |
|---|---|
| `Rep D s` | 表現：狭義増加のラベル $`f`$（$`\omega_1`$ 未満）で、$`\mathcal E_D(M(s))`$ の原子がすべて成り立つもの |
| `rep_exists` | どの列にも表現がある（閉じた点、`initial_finite_graph`） |
| `atoms_wellFormed`、`root?_spec`（`ReserveShape.lean`） | 正準の山の脚の原子の形、根と制御の形 |
| `descent_delete` | 末項を消す展開の降下 |
| `initial_state`、`block_covered`、`block_keys`、`block_class` | 判定の真から、`Splice.iterated_reservoirs` の 4 つの仮定を作る |
| `descent_splice` | 区画を足す展開の降下 |
| `descent` | `classifiedB s n D = true` なら、$`s`$ の表現から $`s[n]`$ の表現で、ラベルがどれも $`f(x_0)`$ より小さいものが作れる |
| `Step` | `Step t s`：$`s`$ は空でなく、ある $`n`$ で `Official.expand s n = .ok t` |
| `ClassificationHolds` | すべての $`s, n`$ と、$`M(s)`$ の次数の上界 $`D`$ について `classifiedB s n D = true` |
| `wellFounded_of_classification` | `ClassificationHolds → WellFounded Step` |

整礎性の定理は、合法でない列も含むすべての有限の列について述べている。展開が失敗する列からは `Step` が無い。

### 5.3 これからすること

- 分類の補題 `ClassificationHolds` の証明（§6）。

## 6. 未解決の補題

Lean の形では、残る主張は次のひとつである（[OmegaY/Official/Descent.lean](../OmegaY/Official/Descent.lean)）。

```lean
def ClassificationHolds : Prop :=
  ∀ (s : List Nat) (n D : Nat), DegreeOK s D → classifiedB s n D = true
```

`DegreeOK s D` は「$`M(s)`$ の行の次数がどれも $`D`$ 以下」である。`classifiedB s n D`（[OmegaY/Official/Reserve.lean](../OmegaY/Official/Reserve.lean)）は、展開 $`s[n]`$ が成功したとき、次のすべてを確かめる。展開が失敗したときは真である。

1. **出力の山.** $`s[n]`$ の正準の山 $`M(s[n])`$ が作れる。
2. **次元の保存.** $`M(s[n])`$ の行の次数はどれも $`D`$ 以下である（01-feasibility の I1）。
3. **展開の長さ.** 末項が 1 か $`n = 0`$ なら、$`s[n]`$ は $`s`$ より 1 項短い。そうでなければ、$`s[n]`$ の長さは $`x_0 + nw`$ である。
4. **分類.** $`M(s[n])`$ の脚の原子のすべてが、$`\mathcal E_D(M(s))`$ と制御 $`a(t)`$ について §1.2 の分類（基、予備、継ぎ目のどれか）を満たす。

### 6.1 進み具合（2026-09-23）
- **4（脚の原子の分類）.** [OmegaY/Official/Classification/](../OmegaY/Official/Classification/) で、次の 3 つの未解決の命題に帰着した（`Bridge.wellFounded_of_block`）。上の部分で脚が根の列より左にある節点の場合は証明済み（`KeyUpper.keyOK_upper_low`）。
  1. `Dimension.BlockReconstruction`：組み立てた図が出力の正準の山に等しい（項目 1 の強い形）。
  2. `Control.ControlDominates`：入力の山だけについての命題。末列の一番上より下の節点の脚の原子の鍵は、制御の鍵より小さい。**証明済み**（`Proofs/ControlDominates.lean` の `controlDominates`）。脚の原子の鍵は、列を上るにつれて狭義に増える（`leg_lt_above`）。
  3. `Control.KeyLeRest`：写した列の各節点の出力の脚の原子の鍵は、写しの元の脚の原子の鍵を写したもの以下である（ブロックの境目では 1 つ前のブロックの量で写す）。
- **3（`KeyLeRest`）.** [OmegaY/Official/Classification/Proofs/](../OmegaY/Official/Classification/Proofs/) で、ずらす量がいつも $`w \cdot i`$ であることを示し（`keyLeRest_of_shift`）、ブロック 0（`keyLe_block0`）と、元の鍵がすべて $`\top`$ の場合（`keyLe_allTop`）を証明した。残りは 7 つの領域の補題に帰着した（`keyLeRest_of_regions`）。上の部分、帯の段、根の行の写し（$`b = 0`$ と、すき間の段 $`b = 1`$）のそれぞれで、境目の列 $`x = x_0`$ と中の列 $`x \lt x_0`$ に分けたものである。数値の試験では、約 720 万個の節点で失敗は 0 件だった。7 つはどれも、写した列の下の部分で、尺度の根の鎖が元の山の鎖とどう対応するかにかかっている。すき間の写しでない 5 つの領域は、鎖の対応の 5 つの命題（`StepInner`、`StartLeg`、`StartJump`、`StartCopy`、`StartRoot`）に帰着した（`Proofs/ChainCorrRegions.lean` の `keyLeRegion_of_chains`、`wellFounded_of_chains`）。境目の列では、元の山の鎖の列 `cr` の節点を写しと対応させず、次の節点に届けばよいとする。5 つの命題は、約 640 万回の検査で失敗 0 だった。道具として、正準の山で辺の父は「その列で、上の節点の行より真に下の最も高い節点」であることを証明した（`Proofs/ChainsCanonParent.lean` の `canonical_rawParent_highest_below`）。
- **1 の再構成（`BlockReconstruction`）.** [OmegaY/Official/Recon/](../OmegaY/Official/Recon/) で、新しい列についての 2 つの主張に帰着した（`Recon.reconstructionHolds_of_rowLaw_chain`）。行の法則 `RowLawHolds`（新しい列で上の節点の行が `B(下の行, 親の行)`）と、親の鎖 `ChainHolds`（`u⁺` の格納された親が、`Q u` から格納された親をたどって届き、途中の節点の値が `v(u⁺)` 以上）である。新しい列の底の節点は証明した（`bottomHolds`）。2 つの主張は、474 個の fixture と、JS の標本の新しい節点約 220 万個で反例が無い。親の鎖は、さらに 2 つに分けた（`Recon.chainHolds_of_split`）。親が上の節点より低いこと（`ParentBelowHolds`）と、候補 `Q u` が親の列にないときの鎖（`CrossChainHolds`）である。候補が親と同じ列にあるときは証明した（`Q_eq_of_same_column`）。親が上の節点より低いこと（`ParentBelowHolds`）は、上の部分と bump の指数が 0 の場合を証明し、残りを `LowerParentBelowHolds` に帰着した（`Recon/ParentBelow.lean`）。行の法則は、上の行が下の行の bump になること（`RowLaw.bumpChainHolds`、証明済み）と、その指数が親の行との jump に等しいこと（`RowLaw.JumpLawHolds`、未解決）に分けた（`RowLaw.rowLawHolds_of_jumpLaw`）。後者は、新しい列の約 656 万組で反例が無い。474 個の fixture の新しい節点 16085 個のうち、候補が親の列にないのは 1062 個だった。候補が親の列にないときの鎖（`CrossChainHolds`）は、値を使わない比較 `Lex`（格納された親と行だけで決まる）に言い換え（`Recon.crossChainHolds_of_lex`）、上の節点 `u⁺` の出所の種類（plain、clean、cut、upper）で 4 つに分けた（`Recon/CrossKinds.lean`）。cut の種類は、cut の emit の直前がいつも同じ出所の clean の emit であること（`CutPredHolds`）から出る（`crossLexFor_cut`）。残りは plain、clean、upper の 3 つの `CrossLexFor` と `CutPredHolds` で、どれも JS の標本の交差の場合の節点約 31 万個で反例が無い。行の法則の jump の部分（`JumpLawHolds`）は、ブロック 0、上の部分、継ぎ目（最初の上の行がちょうど τ の場合も）を証明し、両方の節点がブロック $`i \ge 1`$ の列の下の部分にある組 `LowerPairsHolds` に帰着した（`Recon/JumpLawSeam.lean` の `jumpLawHolds_of_lowerPairs`）。これは試験した約 758 万組の 85% にあたる。
- **3 の鎖の対応（2026-09-23 の続き）.** 5 つの命題と 2 つのすき間の領域を、さらに小さい命題に帰着した。どれも数値の試験で失敗 0 である。
  - 写した列の形：どの写した列でも、元の山の各節点はちょうど 1 回、すき間の写しでない写しになり、その後はすき間の写しだけが続く（`CopyEmitted`、`CopyFirst`）。行の写し方はブロックの中で 1 つの狭義単調な写像になる（`CopyOrder`）。起源の行が減らないこと（`CopyMono`、`PlainOnce`）は証明した（`ChainCorrCopyMono.lean`、`ChainCorrStepInner.lean`）。
  - `StepInner`：上の 3 つと、`LegLookup`、`BumpCopyLower`、`CleanNext`、`CleanLookup`、`CleanParent` に帰着した（`ChainCorr.Inner.stepInner_of_rest`）。
  - `StartLeg` と `StartJump`：上の形と、`LegBelowTop`（元の山だけの事実）、`LegRowMatchRootLower` に帰着した（`ChainCorr.LegJump.startLeg_startJump`）。jump が写しで増えないこと（`stepJumpLe`）は証明した。
  - `StartCopy` と `StartRoot`：上の形と、`CutTop`、`BoundaryChain`、`OriginReach` に帰着した（`startCopy_of_open`、`startRoot_of_parts`）。
  - **偽の仮定（2026-09-23）.** `LegBelowTop`（元の山の列 `c`、`c_r < c ≤ x_0` の節点 `u` で `row u < row t` なら、脚の列は `c_r` 以上）は偽である。反例は $`s = (1,2,4,8,10,8)`$ で、`u = (4,3)` の脚は列 1 だが `c_r = 2`（`Proofs/LegBelowTopFalse.lean` の `not_legBelowTop`、`decide +kernel`）。値が 9 以下の列では破れないので、それまでの数値の試験では見つからなかった。長さ 6 以下・値 12 以下の 248831 列のうち 64 列で破れ、最短は $`(1,3,9,11,9)`$。同じ 64 列で、鎖の対応の仮定 `StartLeg` と、`LegRight`（`Recon/ParentBelowLowerProfile.lean`）も数値の上で破れる（どちらも 402 回）。一方、`KeyLeRest`、`StartJump`、`StartCopy`、`StartRoot`、`StepInner` は同じ入力で失敗 0 である。だから、これらを仮定に使う道筋（`ChainCorrRegions` の `wellFounded_of_chains`、`LegJump.startLeg_startJump`、`InnerLookup.legLookup_left`、`JumpLawLowerLeg`、`ParentBelowLowerLeg`）は、脚が `c_r` より左の場合を別に扱うように直す必要がある。境目の列が τ より下の `c_r` の行をすべて持つこと（`boundaryRootRows`）と `LegRowMatchRootLower` は証明した。
  - **値の大きい列での監査（[05-large-value-audit.md](05-large-value-audit.md)）.** 目標の命題（降下、分類、`BlockReconstruction`、`KeyLeRest`、`RowLawHolds`、`ChainHolds`、`CrossChainHolds` など）はどの集合でも失敗 0 だった。一方、帰着に使った仮定のうち `StartCopy`（最短の反例 $`(1,3,8,10,13,8)[1]`$）、`StepInner`（$`(1,3,8,10,15,8)[1]`$）、`CopyOrder` と MA（$`(1,3,6,13,15,13)[1]`$）、`NonCutOrder`、`CutBetween` は偽である。だから下の鎖の対応による `KeyLeRest` の道筋は、このままでは完成しない。弱い形 `StepInnerSkip`、`StartCopySkip` は失敗 0 だった。
  - **段 A（2026-09-24）.** 依存の順に、土台と道筋を先に決めた。
    - 写した列の形の土台を無条件で証明した（`CopyShape*.lean`）：`Emitted`、`CopyEmitted`、`CopyFirst`、MH。偽の MA・`CopyOrder`・`NonCutOrder`・`CutBetween` の代わりに、脚の形 `CopyOrderLeg`、`NonCutOrderLeg`、`CutBetweenLeg` を証明した。鍵は、脚 $`\ell \ge c_r`$ の節点では列 $`x`$ と脚 $`\ell`$ が同じ region で同時に上がること（`ascLeg`）と、行の写像 Ψ が狭義単調なこと（`Ψ_strictMono`）である。
    - `KeyLeRest` の道筋を作り直した（`LowerChain*.lean`）。鎖の対応を、一番上の写しの 1 歩 `TopStep` と出発 `TopStart` の 1 組にまとめ、親の鎖の側（`CopyStepLow`、`CopyQLower`、`CrossLexFor` の plain・clean・upper）と `KeyLeRest` の側の両方で使う。関係 `Rel = CopyNode ∨ TopNode` で、元の `bound_of_sim` がそのまま使え、skip は要らない。`KeyLeRest` は `TopStep`、`TopStart`、`NonTopStep`、`StartRelNT`、`StartRootNT`、`StepCut`、`CutJump`、`CutStartCopyNT`、`CutStartRootNT` から出る（`keyLeRest_of_lower_main`）。どれも値の大きい列を含めて失敗 0 である。「region の節点ではいつも一番上の写し」は偽だった。
  - **段 B（2026-09-24）.** 互いに独立な 6 つのパッケージを並べて進めた。
    - 行の法則の jump の部分 `JumpLawHolds` を無条件で証明した（`Recon/LRC*.lean` の `jumpLawHolds`）。残っていた `LowerRowsCopy`（脚が同じブロックの写し）と `LowerRowsBoundary`（脚が境目の列）を示した。写しの場合は、Y の項目の木が λ への道にそって X の木を真似ること、境目の場合は、境目の列の頂上の高さが $`h_\kappa + (h_\kappa - h_\rho) \cdot i`$ であることを使う。
  - **段 C（2026-09-24）.**
    - 共有の `TopStart` は偽である（`TopStartLoRightFalse.lean`、`#guard` による計算）。脚が `c_r` より右の場合の反例は $`(1,20,15,23,3,10,28,22)[1]`$、脚が `c_r` の場合の反例は $`(1,13,29,4,18,25,15)[1]`$。どちらも plain の出所で、`pa` が `o` と同じ行にある。o は根の頂上と同じ行にあり、その行で脚の列だけが上がる判定を通るので、`pa` の一番上の写しは clean の写しの上のすき間の写しになる。目標の命題（`KeyLeRest`、親の鎖）はこの入力でも成り立つ。弱めた `TopStart'` への道筋の直しを進めている。
    - `TopStart` を弱めた `TopStart'` に直した（`TopStartFix*.lean`）。脚が `c_r` より右では `TopNode` を `Rel` に、脚が `c_r` では上の行の条項を「o の上の節点の行が τ 未満」のときだけにした。`KeyLeRest` の側と、親の鎖の plain・clean の帰着は、すべて `TopStart'` で作り直した。組み立ては `wellFounded_of_stageC'`。新しく偽とわかったのは、`CrossLexFor IsUpper` の帰着に使っていた `CopyQLower` と `InnerHolds`（反例 $`(1,21,5,20,30,23,20)[1]`$）。この入力でも目標の親の鎖と `CrossLexFor` は成り立つ。したがって `CrossLexFor IsUpper` は、また開いた命題になった。
    - 継ぎ目（`Proofs/Seam*.lean`）：`BoundaryChain` は `CutParentNT` から、`TopStepLoRoot` は `CutParentNT` と `StepRootTop` から出る。どちらの命題も値 40 以下の列で失敗 0。`StartRootTop` は偽（`TopStartLoRoot` と同じ反例）。
    - すき間の写しの行 `CutJumpRootRow`、`CutRunTop` を無条件で証明した（`Proofs/P3T*.lean`）。パッケージ 3 に残るのは `TopStep`、`NonTopStep`、`BoundaryChain` だけ（`package3_of`）。
    - `ParentBelowHolds` と `LowerParentBelowHolds` を無条件で証明した（`Recon/PBStageB*.lean`）。`Profile7` の `CutOrder`、`CutLeg`、`Lift` を証明した。`Boundary` は偽である。根の列が 0 のとき、根の列の（作られない）写しで `leftColumn` が失敗する（最小の例 $`(1,3)[1]`$、`not_boundary_of_check`。`#guard` による計算）。根の列 1 以上の `BoundaryPos` を証明し、`Boundary` を使っていた 1 か所を置き換えた。
    - `StartRelNT`、`StartRootNT` を無条件で証明し、`NonTopStep` を再構成から出した（`NonTop*.lean`）。
    - `CutStartCopyNT` を無条件で証明し、`StepCut`、`CutJump`、`CutStartRootNT` を `BoundaryChain`、`CutJumpRootRow`、`CutRunTop` に帰着した（`Pkg3*.lean`）。
    - 親の鎖の plain と clean：`EmitBelow`、`CleanFirst`、`PairAbove`、`PairOld`、`RootPass IsClean` を証明した（`Recon/Pk4*.lean`）。`CrossLexFor IsPlain` は `TopStep`、`TopStart`、`RootPass IsPlain`、`LexImg IsPlain` から、`CrossLexFor IsClean` は `TopStep`、`TopStart`、`LexImg IsClean` から出る。
    - `TopStep`、`TopStart` を、継ぎ目の 3 つの場合 `TopStepLoRoot`、`TopStartLoRoot`、`TopStartLoRight` に帰着した（`TopChain*.lean`）。
  - **段 E（2026-09-26）.**
    - `SeamChainX`、`QRootRowGe` を無条件で証明した（`Recon/SCXMain.lean`）。`QRootSeam` も出る。`CutRightTopHi` を無条件で証明した（`Recon/CrossUpperQHiCut.lean`）。`TopStep` を無条件で証明した（`Recon/FinalStageE.lean` の `topStep_final`）。
    - `RootValueIn` は偽である。反例は $`(1,4,18,56,18)`$（`TSQRootValueInFalse.lean`、`#guard` による計算）。`P(o)` の探索が `pa` と根 `g` を捨てて列 0 で止まり、o の上の節点が行 $`\omega^2`$ に跳ぶ。`TopStartPaOUp` と `TopStart'` の強い条項も、この入力で数値では偽。
    - `PaONoGapHi` は偽である。反例は $`(1,21,5,20,59,20)[1]`$（`CrossUpperQHiFalse.lean`、`#guard` による計算）。`CopyQLowerW` も同じ入力で数値では偽で、内側の場合の `TopCopy` を弱める必要がある。
    - 組み立て `wellFounded_of_stageE`（`FinalStageE.lean`）は、`RootValueIn`、`PaONoGapHi`、`CutRightTopHi`、`SeamChainX`、`QRootRowGe` だけを仮定にするが、2 つが偽なので中身が無い。目標の命題（ChainHolds、CrossChain、RowLaw、ParentBelow、KeyLeShift、CrossLex）は、2 つの反例の入力でも成り立つ。
  - **段 D（2026-09-26）.**
    - 継ぎ目の `CutParentNT` と `StepRootTop` を無条件で証明した（`Proofs/CPN*.lean`、`Proofs/SRTMain.lean`、`Recon/SRTTree.lean`）。ここから `BoundaryChain`、`StepCutNT`、`TopStepLoRoot` が出る。
    - 親の鎖：`CopyCountLe` を無条件で証明した（`Recon/CCL*.lean`）。`SeamStep`、`SeamStart` は `CutParentNT` から出る（`Recon/SeamPass*.lean`、`Recon/RPL*.lean`）。`LexImg IsPlain`、`LexImg IsClean` は無条件、`RootPass IsPlain` は `TopStep`、`TopStart'`、`CutParentNT` から出る。
    - `TopStart'` の部品：`StartRootTopUp`（`BiTopLow`）と `TopStartCutRight`（`CutTopGap`）を無条件で証明した。`TopStartLoRootW` は `CutParentNT` から出る。`TopStartPaOUp` は `RootValueIn` に帰着した（`Proofs/TSQ*.lean`）。
    - `CrossLexFor IsUpper` の新しい帰着：`PaONoGapHi`、`CutRightTopHi`、`SeamChainX`、`QRootRowGe` から出る（`Recon/CrossUpperW*.lean`、`Recon/CrossUpperQ*.lean`）。1 歩だけの形の `SeamChainX` は偽（反例 $`(1,3,9,11,16,8)[1]`$）で、使っていない。
    - 数値の試験は、この段から 1 回 60 秒以内・小さい入力だけにした。
  - **`LiftLegRight`、`LegRowMatchInner`、`StartJump`、`LowerPairsLeft` は無条件で証明した**（2026-09-24、`Proofs/LiftLegRightProof.lean`、`Recon/JumpLawLowerLeftDone.lean`）。偽の `CopyOrder` の代わりに、2 つの列で上がるかどうかが一致すること（`ascAgree`）を使う。行の法則に残る仮定は `LowerRowsCopy` と `LowerRowsBoundary` だけになった（`jumpLawHolds_of_lowerRowsCases`）。
  - `CrossLexFor IsUpper`（`SeamLastPosHolds`、`InnerHolds`）は、土台の `Emitted` と、写した列の下の部分の鎖の対応 `CopyQLower`、`CopyStepLow` から出る（`Recon/CrossUpperSim*.lean` の `crossLexFor_upper_of_low`）。上の節点の行が τ 以上の場合は証明した。
  - **偽の `LegBelowTop` を使わない道筋（`ChainCorrLegLeft*.lean`、`Recon/JumpLawLowerLeft.lean`）.** `StartLeg` を、脚が `c_r` 以上の場合と、脚が `c_r` より左で出所が plain の場合に分けた（`startLeg_split`）。後者では行が動かず、親も同じである（`legLeft_same`）。これは元の山の事実 `LiftLegRight` から出る。`StartJump` は `LegRowMatchInner` から出る。行の法則は `LowerRowsCopy`、`LowerRowsBoundary`、`LowerPairsLeft` から出る（`jumpLawHolds_of_lowerCases_left`）。この 3 つと `LiftLegRight`、`LegRowMatchInner` は、値の大きい列でも失敗 0 である。ただし `KeyLeRest` の側の整礎性の定理（`wellFounded_of_lift_inner` など）は、まだ偽の `StepInner` と `StartCopy` を仮定している。
  - 続きの帰着（どれも Lean で証明。数値の試験は値 9 以下で失敗 0。値の大きい列での結果は上の監査を見よ）：
    - 写した列の形 `CopyOrder`、`CopyEmitted`、`CopyFirst` は、元の山の事実 MA、MH から出る（`CopyShape*.lean`）。MD は証明した（`CopyShapeMD.lean` の `mdHolds`）。
    - `BumpCopyLower` は `CopyFirst` から出る。`LegLookup` は `LegGapTop`、`LegOriginReach` などに帰着した（`StepInnerLookup*.lean`）。
    - `StartCopy`、`StartRoot` は `BoundaryStepLower`、`BoundaryCutChain`、`PaLookup`、`X0Reach`、`GapTop` に帰着した（`StartRootParts*.lean`）。`BoundaryChain` はブロック 1 で証明した。
    - すき間の 2 つの領域は `CutRunLow`、`CutRunHigh`、`CutOriginReach`、`CutJumpTop`、`CutBump`、`CutLegLookup` に帰着した（`CutParts*.lean`）。
    - `CleanNext` は無条件で証明した。`CleanParent` は `ViaRoot`（値だけの命題、例が少ない）に、`CleanLookup` は `LookupInner`、`LookupRoot` に帰着した。境目の列が τ より下の `c_r` の行をすべて持つこと（`boundaryRows`）と、帯で `x_0` の頂上が `c_r` の頂上より高いこと（`liftLast`）も証明した（`StepInnerClean*.lean`）。
    - `CutPredHolds` は無条件で証明した（`Recon/CutPred*.lean`）。
    - `CrossLexFor IsPlain`、`IsClean` はブロック 0 で証明し、残りを `CrossLexPos` に帰着した（`Recon/CrossPlain*.lean`）。`CrossLexFor IsUpper` は `SeamLastPosHolds`、`InnerHolds` に帰着した（`Recon/CrossUpper*.lean`）。
    - `LowerParentBelowHolds` は、ブロック 0 を無条件で証明し（`ColData.emitted0`）、ブロック `i ≥ 1` を写し方の 7 つの性質 `Profile7`（`NonCutOrder`、`CutBetween`、`CutOrder`、`CutLeg`、`Emitted`、`Lift`、`Boundary`）と `LegRight` に帰着した（`Recon/ParentBelowLower*.lean`）。ただし `LegRight` は偽で（`not_legRight_of_check`、`#guard` による計算）、脚が `ℓ < c_r` のときは親の列がずれない `q = ℓ` の場合を足す必要がある。
    - `LowerPairsHolds` は `LowerLegGe`（`LegBelowTop` から出していた）、`LowerRowsCopy`、`LowerRowsBoundary` に帰着した（`Recon/JumpLawLower*.lean`）。
  - すき間の 2 つの領域：鍵を辞書式に比べる厳密な版（`keyLe_keyAt_of_lex`）を作り、`StepCut`、`CutJump`、`CutStartCopy`、`CutStartRoot` に帰着した（`ChainCorrCut.lean`）。根の行の写しの脚が `cr` 以上であること（`cutLeg`）は証明した（`ChainCorrCutLeg.lean`）。

- **仮定の誤り.** 上の `ClassificationHolds` は偽である。`expand [] n = .ok []` で、長さの検査 $`0 + 1 = 0`$ が偽になる（`Reconstruction.not_classificationHolds`）。`Step` は $`s \ne []`$ を要求するので、空でない列に限った `ClassificationHoldsNE` で足りる（`wellFounded_of_classificationNE`）。さらにそれを、次数と原子の分類の 2 つ（`DegreeAndAtomsHold`）に分けた（`wellFounded_of_parts`）。
- **1 と 3（出力の山、出力の長さ）.** [OmegaY/Official/Reconstruction.lean](../OmegaY/Official/Reconstruction.lean)。出力の長さは証明済み（`expand_length_delete`、`expand_length_splice`）。出力の山が作れることも証明済み（`expand_build_ok`）。組み立てた図が出力の正準の山に等しいこと（`ReconstructionHolds`）は、削除の展開と、$`x_0`$ より左の列でだけ証明した（`expand_build_eq_delete`、`expand_build_prefix`）。$`n \ge 1`$ の $`x_0`$ から右の列が残る。

- **2（次元の保存）.** [OmegaY/Official/Dimension.lean](../OmegaY/Official/Dimension.lean) で証明した。出力の図の行はどれも、入力の山の行（`official` をかけたもの）、末列の一番上の行 τ から作った区画の slot（`stored` をかけたもの）、または 0 の行である。slot の次数は、τ の次数と level の小さいほうの上界（どちらも $`D`$ 以下）を超えない。
  - 出力の図の次数：`expandDiagram_degree`（仮定なし）。
  - 削除の展開の出力の山：`output_degree_delete`（仮定なし）。
  - ブロックを足す展開の出力の山：`output_degree`。これは 1 の再構成（`BlockReconstruction`：組み立てた図が出力の正準の山に等しい）を仮定する。この仮定は、長さ 5 以下・値 0〜5 の全部の列と $`n \in \{1,2\}`$（18662 通り）で反例が無かった。

原子の形、根が末列より左にあること、制御が脚の原子であることは証明済みである（`atoms_wellFormed`、`root?_spec`）。1、2、3 は公式の展開の規則についての性質で、weak の規則では Phyrion 氏が同じ種類の定理を証明している（`ActualCanonicalReconstruction`、`SupportedDimension`）。中心は 4 で、公式の展開の規則（03-official-rule §2）の場合分けに沿って示すことになる。Phyrion 氏の weak の証明で同じ役目を果たした部分は約 8 万行である。規模はそれに近いと見込む（推測）。

## 7. 限界

- 分類の補題の根拠は、有限の標本での試験だけである。
- 標準形の標本は、値と長さに上限がある。
- 試験は、自前の公式の展開の実装を使った。この実装は公式のプログラムと、試したすべての展開で一致した（03-official-rule §6）。
