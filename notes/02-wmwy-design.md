[← PLAN](../PLAN.md)

# 設計（weak-magma ω-Y、wmwy-wo-por から写した）：patterns of resemblance による整礎性

対象は Phyrion 氏の [omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)（リビジョン [`33c16a8`](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/tree/33c16a8ce8f7e01bb3794881f3ff9109474beaed)、Apache-2.0）の weak-magma ω-Y（weak magma、no extraction）である。展開の定義は変えない。

## 0. 要約

- Phyrion 氏の証明は二層に分かれる。組合せの層（`OmegaY/` の大部分）と、意味の層（`OmegaY/Reflection.lean`、`OmegaY/Reflection/{Skolem,Stability,OrdinalSupply}.lean`、約 630 行）である。
- 意味の層は、もともと許容順序数も $`L`$ も使わない。関係 $`R(θ,a,b)`$ は「$`b`$ より下の有限の正の図式を $`a`$ より下へ圧縮できる」ことで、（上端、鍵）の辞書式の再帰で定義する。
- このリポジトリは、意味の層を patterns of resemblance の形に取り替える。$`R(θ,a,b)`$ を「高さ $`a`$ の構造が高さ $`b`$ の構造の $`Σ_1`$ 初等部分構造である」ことにする。1y-wo-por（1-Y）と同じ方法である。
- 組合せの層は変えずに使う。ただしライセンスの無い YesMetaZFC への依存を外す。0-Y の層（`ZeroY/`）と BMS の層（`Por/BMS/`）は 1y-wo-por のものを使う。

## 1. コアが意味の層から使うもの

コアが使う名前は次だけである（`grep` で確かめた）。

| 名前 | 内容 |
|---|---|
| `KeySyntax`、`InternalAtom`、`TopAtom`、`Bounded`、`InternalHolds`、`TopHolds`、`KeysBelow` | インターフェースの定義 |
| `Reflection.R S θ a b` | 関係 |
| `Reflection.key_weaken` | $`θ ≤ Θ`$ かつ $`R(Θ,a,b)`$ なら $`R(θ,a,b)`$ |
| `Reflection.finite_reflection` | 有限反映（下に式を書く） |
| `OrdinalSupply.Label`、`OrdinalSupply.top`、`OrdinalSupply.initial_finite_graph` | ラベル $`\{o ≤ ω_1\}`$、上端 $`ω_1`$、最初の表現 |

鍵は $`\mathrm{Key}_m = \mathrm{Lex}(\mathrm{Fin}\ m → \mathrm{Label} ∪ \{⊤\})`$、鍵の型板 $`t`$ は各座標に列の番号か $`⊤`$ を置いたもので、$`\mathrm{eval}\ t\ v`$ は単調である。

有限反映（Phyrion 氏の文をそのまま使う）：$`f`$ が狭義単調、$`f \lt b`$、内部の辺 $`G`$ が $`f`$ で成り立ち、上端への要求 $`N`$ の鍵が $`θ`$ 未満、$`N`$ が $`b`$ へ成り立ち、$`R(θ, f(\mathrm{cut}), b)`$ とする。このとき次を満たす $`g`$ がある。$`g`$ は狭義単調、$`g \lt f(\mathrm{cut})`$、$`i \lt \mathrm{cut}`$ で $`g(i) = f(i)`$、$`g ≤ f`$、$`G`$ が $`g`$ で成り立ち、$`N`$ が $`f(\mathrm{cut})`$ へ成り立つ。

## 2. 定義

### 2.1 構造

鍵 $`θ`$ と高さ $`c`$ について、構造 $`\mathfrak A^c_θ`$ を次で決める。

- 領域は $`\{x : x \lt c\}`$。
- 順序 $`\lt`$。
- 内部の関係：型板 $`t`$ と位置 $`i, j`$ ごとに $`\mathrm{Rel}_{t,i,j}(\vec v) :⟺ R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$。
- 上端の述語：型板 $`t`$ と位置 $`i`$ ごとに $`\mathrm{Top}_{t,i}(\vec v) :⟺ R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$。ただし $`\mathrm{eval}\ t\ \vec v \lt θ`$ のときだけ定義される（部分的な述語）。

### 2.2 論理式

$`Σ_1`$ 論理式は $`∃ \vec y\ (ℓ_1 ∧ ⋯ ∧ ℓ_k)`$ で、各 $`ℓ`$ は上の原子論理式かその否定である。上端のリテラルは、その鍵が $`θ`$ 未満のときだけ真になりうる（肯定でも否定でも）。論理式の変数のうち、決まった位置がパラメータである。

### 2.3 関係

```math
R(θ,a,b) \;:⟺\; a \lt b \;∧\; \mathfrak A^a_θ \preccurlyeq_{Σ_1} \mathfrak A^b_θ
```

すなわち、$`a`$ 未満のパラメータを持つすべての $`Σ_1`$ 論理式について、$`\mathfrak A^a_θ`$ で真であることと $`\mathfrak A^b_θ`$ で真であることが同値である。

再帰の段は（上端、鍵）の辞書式順序である。$`\mathfrak A^a_θ`$ の上端の述語は段 $`(a, ·)`$、$`\mathfrak A^b_θ`$ の上端の述語は段 $`(b, κ)`$（$`κ \lt θ`$）、内部の関係は段 $`(v_j, ·)`$（$`v_j \lt b`$）を読む。どれも $`(b, θ)`$ より前である。

## 3. 証明

### 3.1 鍵の弱化

$`θ ≤ Θ`$、$`R(Θ,a,b)`$ とする。

- 下から上：$`\mathfrak A^a_θ`$ での証人 $`\vec w`$ を全部パラメータにした論理式を $`Θ`$ で移す。上端の述語は $`\vec w`$ の上で一致する。
- 上から下：$`\mathfrak A^b_θ`$ での証人 $`\vec v`$ のうち $`a`$ 未満のものをパラメータにし、残りを $`Θ`$ で下へ移す。新しい証人 $`\vec w`$ は $`\vec w ≤ \vec v`$（各点）である。$`\mathrm{eval}`$ が単調なので、鍵は $`θ`$ 未満のままである。

### 3.2 有限反映

$`i \lt \mathrm{cut}`$ の $`f(i)`$ をパラメータ、残りを証人とする論理式 $`⋀_{i \lt j} v_i \lt v_j ∧ ⋀_{e ∈ G} \mathrm{Rel}_e ∧ ⋀_{e ∈ N} \mathrm{Top}_e`$ は、$`\mathfrak A^b_θ`$ で $`f`$ に満たされる。$`R(θ, f(\mathrm{cut}), b)`$ で $`\mathfrak A^{f(\mathrm{cut})}_θ`$ へ移す。

### 3.3 閉じた点

$`\mathrm{Good}(α)`$：上端の述語をすべて定義した高さ $`ω_1`$ の構造で、$`α`$ 未満のパラメータを持つ $`Σ_1`$ 論理式が真なら、$`α`$ 未満の証人がある。

- 型板は可算個なので、論理式も可算個である。可算の $`γ`$ から、$`γ`$ 未満のパラメータの全部の論理式の証人を上から押さえる操作を $`ω`$ 回くり返し、上限を取る。$`\mathrm{Good}`$ な点は $`ω_1`$ の中で共終である。
- top_abs：$`\mathrm{Good}(α)`$ なら、すべての鍵 $`κ`$ と $`x \lt α`$ について $`R(κ,x,α) ⟺ R(κ,x,ω_1)`$。鍵についての帰納法である。証人を下ろすところは 3.1 の「各点で小さくなる」を使う。
- $`\mathrm{Good}(α)`$、$`\mathrm{Good}(β)`$、$`α \lt β \lt ω_1`$ なら、すべての鍵 $`κ`$ で $`R(κ,α,β)`$。
- 閉じた点の列 $`p_0 \lt p_1 \lt ⋯`$ が、すべての有限の図式を表す（最初の表現）。

## 4. 実装

状態（2026-09-23）：全部緑。`sorry` は無く、公理は `propext`、`Classical.choice`、`Quot.sound` だけである。

| ファイル | 中身 |
|---|---|
| `OmegaY/Reflection/Interface.lean` | Phyrion 氏のインターフェースの定義（変えない） |
| `Por/Formula.lean` | リテラル `Lit`、論理式 `Form`、真偽 `Lit.Holds`、`Sat`、初等性 `ElemL`、合同の補題、各点で下げても鍵の条件が残る `Lit.holds_of_le` |
| `Por/Relation.lean` | 段 `StageLT`、再帰 `stepF`、関係 `R`、`R_iff`、`R_lt`、`key_weaken`（3.1）、`finite_reflection`（3.2） |
| `Por/Supply.lean` | `Good`、閉包 `next`・`tower`・`lam`、`good_cofinal`、`top_abs`、`good_R`、閉じた点の列 `points`、`initial_finite_graph`（3.3） |
| `OmegaY/Reflection.lean`、`OmegaY/Reflection/OrdinalSupply.lean` | コアが呼ぶ名前を、上の定理で与える薄いファイル。Phyrion 氏の `Skolem.lean`、`Stability.lean` は含めない |
