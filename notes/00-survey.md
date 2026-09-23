# 調査：ω-Y 数列の定義、証明の現状、1-Y の方法の移し方

最初のノートである。weak-magma ω-Y のリポジトリ [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por)（当時の名前は wy-wo-por）で書いたものを写した。ω-Y 数列の定義と規範のプログラム（§1）、停止性の証明と強さ（§2）、1-Y の証明の構造を ω-Y に移すときに変わるところ（§3）、計画（§4）を書く。調べた日は 2026-09-23 である。

1-Y の側の前提は、姉妹プロジェクト [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por)の設計である。Phyrion 氏の 1-Y の組合せの層（[Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) の `formalization/OneY`、`formalization/ZeroY`、Apache-2.0）は、インターフェース `FiniteReflection lt D R` だけを仮定する。1y-wo-por は、その $`R(k,η,a,b)`$（$`(k,η) ∈ ω × ω_1`$）を、順序数の上の Σ₁ 初等性の関係で与えた。

## 0. 要約

- 公式の定義：ω-Y は Yukito 氏が 2021 年 7 月に考えた。2021-09-01 に、Naruyoko 氏のプログラム [Study and Expand Sequence(仮)](https://naruyoko.github.io/StudyAndExpandSequence/) の `expand` を公式の定義とした。ソースは [Naruyoko/StudyAndExpandSequence](https://github.com/Naruyoko/StudyAndExpandSequence) にあり、ライセンスは無い。
- 形式的な証明は 1 つある。Phyrion 氏の [omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)（2026-09-14、Apache-2.0）である。対象は「weak magma、no extraction」の ω-Y である。
- **この weak ω-Y は公式の ω-Y と一致しない。** 標準形 3001 個で展開を比べると、9003 回のうち 480 回で結果が違った（§1.6）。最小の例は $`(1,3,3)[2]`$ である。公式は $`(1,3,2,5,7,12)`$、weak は $`(1,3,2,5,4,9)`$ を返す。よって、公式の ω-Y の停止性は未解決である。
- weak ω-Y の証明の意味の層は、すでに順序数だけで書かれている。構成的宇宙 $`L`$ も許容順序数も使わない。ラベルは $`ω_1`$ 以下の順序数、関係は「有限の正の図式を下へ圧縮できる」ことで、（上端、鍵）の辞書式の再帰で定義する。1y-wo-por の案 B（写し）に、ベクトルの鍵を付けた形である。
- 層について：ω-Y の山の行は $`ω^ω`$ 未満の順序数である。しかし関係 $`R`$ の添字に超限の層は要らない。Phyrion 氏の証明では、鍵は長さ $`m`$ のベクトル $`\mathrm{Lex}(\mathrm{Fin}\ m → \mathrm{Label} ∪ \{⊤\})`$ である。$`m`$ は始めの式ごとに決まり、展開で増えない。
- 強さ：厳密な結果は無い。コミュニティの主張として、$`ω\text{-}Y(1,4) = Y(1,ω)`$ がある（§2.3）。
- 最初に決めること：対象を公式の ω-Y にするか、weak ω-Y にするか。weak ω-Y は Phyrion 氏がすでに証明した。公式の ω-Y は未解決で、組合せの層の新しい仕事が要る（§4）。

## 1. ω-Y の定義

### 1.1 出典と経緯

| 日付 | できごと | 出典 |
|---|---|---|
| 2021-07-17 | Yukito 氏が ω-Y を発表。同じ日に Naruyoko 氏がプログラムを公開 | [Yukito のツイート](https://twitter.com/Y_Y_Googology/status/1416060505337126912)、[Study and Expand Sequence(仮)](https://naruyoko.github.io/StudyAndExpandSequence/) |
| 2021-08-17 | Yukito 氏：最初は $`Y^n(1,ω) = Y^{n+1}(1,3)`$ となる $`Y^n`$ 数列を作ろうとしたが、致命的なバグがあってやめた。ω-Y はすべての次元を一度に開く | [ツイート](https://twitter.com/Y_Y_Googology/status/1427557834850377734) |
| 2021-09-01 | Yukito 氏が ω-Y の完成を宣言。定義は Naruyoko 氏のプログラムとする。ω-Y 数列数を命名 | [ツイート 1](https://twitter.com/Y_Y_Googology/status/1433046241881911309)、[ツイート 2](https://twitter.com/Y_Y_Googology/status/1433047827559583746) |
| 2021-09-01 | Naruyoko/StudyAndExpandSequence の最初のコミット `ccd9620` | [GitHub](https://github.com/Naruyoko/StudyAndExpandSequence) |
| 2024-08-31 | 同 v1.1（`b26ba7e`）。「leg-based test for ascension」の選択肢を追加。既定では切れている。入れると結果が変わる | 同 |
| 2025-03-22 | 中国語の解説。行の添字、magma の 4 つの変種、提取（extraction）を外すこと | [洛谷专栏「ω-Y」](https://www.luogu.com.cn/article/n9oy9wuo) |
| 2026-09-13/14 | test_alpha0 氏と Phyrion 氏が weak magma、no extraction の ω-Y の停止性の Lean 証明を発表 | [omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) |

wiki の記事：

- 英語版：[Googology Wiki (Miraheze)](https://googology.miraheze.org/wiki/%5C(%5Comega%5C)-Y_sequence)、[Googology Wiki (Fandom)](https://googology.fandom.com/wiki/Omega-Y_sequence)。本文は Miraheze 版の生テキストで読んだ。Fandom 版は取得できなかった（HTTP 402）。
- 日本語版：[巨大数研究 Wiki](https://googology.fandom.com/ja/) の記事とゆきと氏のブログは、Fandom のため取得できなかった。この調査は日本語版の内容を確かめていない。

### 1.2 規範となるプログラム

- 規範は Naruyoko 氏の [`expand(s,n,…)`](https://github.com/Naruyoko/StudyAndExpandSequence/blob/master/script.js#L399-L771) である（Miraheze の記事の「Expansion rule」の節）。
- ページには「Inspired by ω-Y sequence by Yukito」とある。入力欄に「Max dimensions」（既定 10）がある。次元の上限に達すると計算を止める。数学的な定義では、上限は無いものと読む。
- v1.0（2021）と v1.1 の既定の設定は、無作為な 800 回の展開で全部一致した（§1.6）。
- リポジトリにライセンスは無い。コードを写さない。読むことと、手元で実行して結果を比べることだけをする。
- 描画のプログラム [MEGA whY mountain](https://naruyoko.github.io/MEGAwhYmountain/) もある。

### 1.3 山の形と、ω の入り方

ω は項の値には入らない。項はいつも正の整数である。ω は次の 2 か所に入る。

1. 山の行の添字。1-Y の山の行は自然数 $`k`$ である。ω-Y の山の行は $`ω^ω`$ 未満の順序数 $`\sum_i c_i ω^i`$（$`c_i ∈ ℕ`$、有限個だけ 0 でない）である。
2. 極限の記法。$`ω\text{-}Y(1,n)`$ の山は $`n`$ 次元の単体の形になる。$`ω\text{-}Y(1,ω)`$ は $`(1,n)`$ の極限で、ω-Y 数列数は $`f^{2000}(1)`$、$`f(n) = ω\text{-}Y(1,ω)[n]`$ である。

山の作り方（Phyrion 氏の参照実装 [reference/engine.js](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/reference/engine.js) の `makeMountain` と、[OmegaY/Canonical/Build.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Canonical/Build.lean) を読んでまとめた。Apache-2.0）：

- 各列の一番下に、値 $`s_c`$ の節点を置く。
- 値が 1 より大きい節点 $`u`$ の上に、次の節点を積む。親の候補は、左の列へ移りながら探す。左へ移るたびに、行が上限（今の候補の行）以下である限り上へ登る。値が $`u`$ の値より小さい候補で止まる。これを親 $`p`$ とする。
- 新しい節点の値は $`\mathrm{val}(u) - \mathrm{val}(p)`$ である。行は次の式で決める。

```math
\mathrm{row}(u^{+}) = \mathrm{row}(u) + ω^{e},\qquad e = 1 + \max\{ i : c_i(\mathrm{row}(p)) ≠ c_i(\mathrm{row}(u)) \}
```

  $`\mathrm{row}(p) = \mathrm{row}(u)`$ のときは $`e = 0`$ で、行は $`+1`$ になる。これは 1-Y と同じ動きである。親が別の行にあると、行は $`ω^{e}`$ 飛ぶ。ここで新しい次元が開く。
- Naruyoko 氏のプログラムは、同じ構造を入れ子の配列と整数の座標のベクトルで表す。差の列を取り、1 つ低い次元の山を作って積み重ねる（`calcMountain`、`calcDifference`）。座標のベクトル $`(c_0, c_1, …)`$ が順序数 $`\sum c_i ω^i`$ に当たる、と読める。この対応は確かめていない。

Miraheze の記事の言い方では、1-Y は対角線の列そのものを次の富士山の底にする。ω-Y は対角線の列の「差の列」を底にする。さらに、富士山の左下の角から取る「銀河の差の列（渦巻きの差の列）」がある。富士山、銀河、銀河群、第 6 の構造、… と限りなく続く。

### 1.4 展開

公式の規則は Naruyoko 氏のプログラムそのもので、文章の定義は無い。ここでは、weak ω-Y の展開を [洛谷の解説](https://www.luogu.com.cn/article/n9oy9wuo) と Phyrion 氏の [Build.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Expansion/Build.lean) から大まかに書く。

- 1-Y と同じ部品：根の要素、根の列、悪い部分、$`N`$ 個のコピー。
- 作用区域（作用区域）：根の列のある要素から次の要素までの範囲。展開はこの区域を単位に行う。
- 末尾の列の値を 1 減らす。
- 辺の 3 種類：輪郭の辺（噴火の辺、轮廓边）、輪郭でない辺（野火の辺、非轮廓边）、magma の辺（充填の辺、填充边）。
- 行の持ち上げ：コピーの中で行 $`δ`$ の節点は行 $`γ + δ`$ に移る。$`γ`$ は根の要素と末尾の列の一番上の要素の行の差である。順序数の加法なので、左の項は吸収されうる。
- magma の辺は、持ち上げでできた行のすき間を埋める。weak magma では、埋める辺の親を、参照の列の行 $`[\mathrm{row}(\mathrm{marker}), \mathrm{gapTop})`$ の節点から取る。
- 最後に、一時的な末尾の列を切り、項の列を読む。

### 1.5 変種：magma と提取

[洛谷の解説](https://www.luogu.com.cn/article/n9oy9wuo) によると、magma の定義には 4 つの変種がある。

| 名前 | magma | 再帰 |
|---|---|---|
| weak magma | weak | weak |
| actual magma | weak | weak のときと strong のときがある |
| medium magma | weak | strong |
| strong magma | strong | strong |

- 解説は「後のものほど強いが、極限はみな同じ MHO」と書く。MHO が何の略で、どの順序数かは書いていない。
- 一番よく使われ、一番分かりやすいのは weak magma だという。
- 解説は、提取（extraction）の規則を外すと強くなる、とも書く。1-Y の提取が何をするかは、この調査では確かめていない。
- 公式の（Naruyoko 氏の）プログラムがどの変種に当たるかは、書いた出典が見つからなかった。「actual」は公式のプログラムの動きを指すのかもしれないが、推測である。
- MrredsharkFan 氏の [w-Y-global-lngi](https://github.com/MrredsharkFan/w-Y-global-lngi)（ライセンス無し）の `weak_w-Y.js` は weak ω-Y の実装である。履歴に「changed strong w-Y to weak」というコミットがある。

### 1.6 比較の実験

手元で 3 つのプログラムを Node.js で動かし、出力を比べた。コードはどれも写していない。作業用の場所で実行しただけである。

- N：Naruyoko 氏のプログラム（公式）。v1.1 の既定（leg-based なし）。
- P：Phyrion 氏の参照実装 `reference/engine.js`（weak magma、no extraction）。Lean の定義 `OmegaY.Expansion.expand` の元である。
- M：MrredsharkFan 氏の `weak_w-Y.js`。

結果：

| 比較 | 対象 | 回数 | 違った回数 |
|---|---|---:|---:|
| N v1.0 と N v1.1 の既定 | 無作為な式、$`n ∈ \{1,2\}`$ | 800 | 0 |
| N と P | 試験用の 21 式、$`n ∈ \{0,1,2,3\}`$ | 84 | 21 |
| N と P | N で $`(1,3), (1,4), (1,5)`$ から届く標準形 3001 個、$`n ∈ \{1,2,3\}`$ | 9003 | 480 |
| N（leg-based あり）と P | 同じ | 9003 | 486 |
| M と P | P で届く標準形 1500 個、$`n ∈ \{1,2\}`$ | 3000 | 0（後述の規約の差を除く） |
| N の辞書式の減少 | $`(1,3)`$〜$`(1,6)`$ から届く標準形 5000 個、$`n ∈ \{0,1,2,3\}`$ | 20000 | 0（どれも $`s[n] \lt s`$） |

- 標準形は、展開の結果の接頭辞（長さ 6 以下、値 200 以下）をたどって集めた。$`(1,3,3)`$ は N でも P でも、$`(1,4) → (1,3,10) → (1,3,9) → ⋯ → (1,3,4) → (1,3,3)`$ で届く。
- M は P の出力に項を 1 つ足した列を返す（2898 回）。残りの 102 回は完全に一致した。$`n`$ の数え方の規約の差である。値の食い違いは 1 つも無かった。
- 最小の食い違い：

```math
\begin{aligned}
\text{N}: (1,3,3)[2] &= (1,3,2,5,7,12), & (1,3,3)[3] &= (1,3,2,5,7,12,19,31),\cr
\text{P}: (1,3,3)[2] &= (1,3,2,5,4,9), & (1,3,3)[3] &= (1,3,2,5,4,9,8,17).
\end{aligned}
```

- Miraheze の記事は、「Y 数列と ω-Y の最初の違いは $`(1,3,2,5,4,9,8,17,…)`$ の極限で、Y では $`(1,3,3)`$、ω-Y では $`(1,3,2,5,5)`$」と書く。N はこのとおりに動く（$`(1,3,2,5,5)[n]`$ がこの列を出す）。P では $`(1,3,3)`$ がこの列を出し、$`(1,3,2,5,5)`$ には届かない。この点では、P は 1-Y と同じに動く。
- 食い違う場合、N の値の方が大きい。例：$`(1,4,6,4)[2]`$ は N で $`(…,108,292,787)`$、P で $`(…,10,38,156)`$。

結論：Phyrion 氏の証明が扱う weak ω-Y は、公式の ω-Y と別の系である。Phyrion 氏のリポジトリは、自分の参照実装とだけ照合している（`verification/expansion-fixtures-source.json`）。公式のプログラムとの一致は主張していない。

## 2. 停止性の証明と強さ

### 2.1 weak ω-Y：Phyrion 氏の Lean 証明

[Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)（コミット `33c16a8`、2026-09-14、Apache-2.0）。README は OpenAI Codex が大きく手伝ったと書く。

- 最終定理（名前空間 `OmegaY.Expansion`、[WellFounded.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Expansion/WellFounded.lean)）：
  - `omegaY_step_wellFounded`：合法な入力（空列、または先頭が 1 で残りが正の整数の列）の上で、実際の展開の関係は整礎である。コピーの数は各段で任意の自然数でよい。
  - `omegaY_trajectory_terminates`：どの軌道も有限回で空列に着く。
  - `omegaY_generated_isWellOrder`：標準の種 $`(1,n+2)`$ から生成される集合は辞書式で整列している。
  - `omegaY_descendants_isWellOrder`：合法な式ごとに、その子孫の集合は辞書式で整列している。
  - 合法な式の全体は辞書式で整列しない（$`(1,2) \gt (1,1,2) \gt (1,1,1,2) \gt ⋯`$）。これも形式化されている。
- 規模：OmegaY は 550 ファイル、83,107 行。ほかに 1-Y のリポジトリから写した ZeroY の 21 モジュール、3,173 行。1-Y の `OneY` は使わない。
- 依存：Lean 4.33.1、Mathlib `eba3d88`（v4.33.1、1y-wo-por と同じ）。YesMetaZFC（[EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean) `bae7e3d`、ライセンス無し）の 12 モジュールを Lake で取ってくる。OmegaY が直接使う YesMetaZFC の名前は `transGen_head` だけ（3 か所）である。ほかは ZeroY の `Forest.Blocker` と `Forest.AncestorMonotone` を通して使う。
- 公理：README と監査の記録によれば、`propext`、`Classical.choice`、`Quot.sound` だけである。GitHub Actions の実行（2026-09-14）は成功している。この調査では手元でビルドしていない。
- 範囲の注意：README は、一階の ZFC への移行、$`Z_2`$/$`Z_3`$ での分類、`PTO(ZFC)` との比較を主張しないと書く。「no-extraction 1-Y」とこの ω-Y の同値も主張しない。

### 2.2 公式の ω-Y

- 停止性の証明は、論文でも形式化でも見つからなかった。
- §1.6 のとおり、Phyrion 氏の証明は公式の ω-Y を覆わない。Miraheze の記事は「weak magma、no-extraction の定義で」と限定を書いているが、公式の定義と違うことは書いていない。
- 公式のプログラムは、試した 20000 回の展開でいつも辞書式に減った。これは停止性の証拠ではない。

### 2.3 強さ

厳密な結果は無い。知られている主張を並べる。

| 主張 | 出典 | 状態 |
|---|---|---|
| $`ω\text{-}Y(1,4) = Y(1,ω)`$ | [洛谷](https://www.luogu.com.cn/article/n9oy9wuo) | 主張だけ。証明は無い |
| $`ω\text{-}Y(1,n+3) = \text{C } n\text{-}Y(1,ω)`$、$`ω\text{-}Y(1,4,20) = \text{C } 2\text{-}Y(1,4)`$ | 同 | 同。「C n-Y」の定義は確かめていない |
| magma の 4 つの変種の極限はみな MHO | 同 | MHO の定義は出典に無い |
| Y と ω-Y の最初の違いは $`(1,3,2,5,4,9,8,17,…)`$ の極限 | [Miraheze](https://googology.miraheze.org/wiki/%5C(%5Comega%5C)-Y_sequence) | 公式の N で確認した（§1.6）。weak では成り立たない |
| 1-Y の $`(1,3)`$ は BMS の極限に当たる、SYO は omega back gear ordinal より大きい | [Miraheze の Y sequence](https://googology.miraheze.org/wiki/Y_sequence) | 予想 |
| 1-Y の整列性の証明は $`\mathrm{KP}_ω`$ ＋「非可算順序数が存在する」で足りる（test_alpha0 氏） | [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy) の README | 同 README は ω-Y との順序型の比較は未解決と書く |

1-Y の側の事実：Phyrion 氏の 1-Y の変種は、Naruyoko 氏の [YNySequence](https://github.com/Naruyoko/YNySequence)（1-Y の公式の定義）と同値であることが示されている（[koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv)）。ω-Y には、この同値に当たるものが無い。§1.6 から、weak ω-Y と公式の ω-Y の同値は偽である。

証明の強さについて：Phyrion 氏の ω-Y の証明は、ラベルに $`ω_1`$ 以下の順序数を使い、$`ω_1`$ の正則性と選択を使う。順序数の上界や表記系は出ない。1y-wo-por と同じ性質である。

## 3. 1-Y の証明の構造を ω-Y に移すと、何が変わるか

### 3.1 1-Y での形（1y-wo-por の前提）

- 図式の辺は `Atom (layer root parent child : Nat)` で、層 $`k ∈ ℕ`$ は山の行である。
- 関係は $`R(k, η, a, b)`$ で、$`η = f(\mathrm{root})`$ は根のラベルである。添字 $`(k,η) ∈ ω × ω_1`$ に辞書式の順序を入れる。
- 有限反映 `FiniteReflection` の要求（TopAtom）は `Admissible` でなければならない：層が $`K`$ より低いか、層が $`K`$ で根のラベルが $`θ`$ より小さい。
- 1y-wo-por の関係：（上端、層、添字）の辞書式の再帰で、段 $`(k,η)`$ の言語の Σ₁ 初等性として定義する。内部の辺はすべての層の原子 $`\mathrm{Rel}_j`$、上端への要求は $`(j,ξ) ≺ (k,η)`$ の原子 $`\mathrm{Top}_j`$ で書く。同じ層の上端の述語は「名前付き」にする（見えるかどうかが位置だけで決まるようにするため）。

### 3.2 Phyrion 氏の ω-Y の証明での形

行が $`ω^ω`$ 未満の順序数になるので、層 $`k ∈ ℕ`$ はそのままでは使えない。Phyrion 氏の証明は、層を関係の添字から外し、根のベクトルに置き換えた。

- 鍵（[Keys.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Keys.lean)）：

```math
\mathrm{Key}_m = \mathrm{Lex}\bigl(\mathrm{Fin}\ m → \mathrm{Label} ∪ \{⊤\}\bigr)
```

  $`⊤`$ はすべてのラベルより大きい。$`\mathrm{Label}`$ が整礎なら、$`\mathrm{Key}_m`$ も整礎である。
- 鍵の型板（template）：$`\mathrm{Fin}\ m → \mathrm{Option}(\mathrm{Fin}\ n)`$。各座標は、図式の頂点か $`⊤`$ を指す。ラベル付け $`f`$ で評価すると鍵になる（`eval`）。評価は $`f`$ について単調である。
- 山の辺の鍵（[Geometry/MountainKeys.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Geometry/MountainKeys.lean) と監査の文書）：行の Cantor 次数の上限を $`D`$ とする。尺度 $`k`$ の根 `scaleRoot k u` は、跳び $`\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\mathrm{parent})) ≤ k`$ の親の辺だけをたどった根である。跳びの指数が $`d`$ の辺の鍵は、尺度 $`D, D-1, …, d`$ の親側の根の列と、そのあとの $`⊤`$ である。したがって $`m = D + 1`$ である。
- 次元の保存（[SupportedDimension.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Expansion/SupportedDimension.lean)）：展開のあとの行は、展開の前の行の上限を超えない。よって $`D`$ は軌道の中で一定である。$`D`$ は始めの式ごとに選ぶ。すべての合法な式に共通の $`D`$ は要らない。
- 関係（[Reflection.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Reflection.lean)）：$`R : \mathrm{Key} → \mathrm{Label} → \mathrm{Label} → \mathrm{Prop}`$。

```math
R(θ,a,b) \iff a \lt b \ ∧\ \mathrm{Reflects}(R)(θ,a,b)
```

  $`\mathrm{Reflects}(R)(θ,a,b)`$ の意味：$`b`$ より下の狭義増加なラベル付け $`f`$ で、内部の辺の集合 $`G`$（鍵は任意）がすべて成り立ち、上端への要求の集合 $`N`$（鍵は $`\lt θ`$）が $`b`$ へ成り立つなら、$`a`$ より下の狭義増加な $`g`$ がある。$`g`$ は $`a`$ より下のラベルを動かさず、$`G`$ を保ち、$`N`$ を $`a`$ へ成り立たせる。再帰は（上端、鍵）の辞書式の順序による。
- ラベルと供給（[Reflection/OrdinalSupply.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Reflection/OrdinalSupply.lean)、[Reflection/Stability.lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/OmegaY/Reflection/Stability.lean)）：$`\mathrm{Label} = \{o : o ≤ ω_1\}`$。有限の問い合わせごとに証人を選ぶ Skolem 関数で閉じた点を、$`ω_1`$ の下に共終に作る（型板は有限なので、関数は可算個）。閉じた点 $`a`$ で、上端を $`a`$ と $`ω_1`$ で取り替えても $`R`$ が変わらないことを、鍵の帰納法で示す（`endpoint_stability`）。これが 1y-wo-por の O7（初期の表現）と `top_abs` に当たる。

### 3.3 層を ℕ より大きくする必要はあるか

- 山の行は $`ω^ω`$ 未満の順序数なので、「行」は $`ℕ`$ を超える。
- しかし関係の添字に、超限の層は要らない。Phyrion 氏の証明では、行の情報は鍵のベクトルの長さ（有限の座標の数）と、各尺度の根のラベルに入る。鍵の型 $`\mathrm{Key}_m`$ の順序型は $`(ω_1 + 2)^m`$ 程度で、$`m`$ は軌道ごとに有限である。
- 1-Y の $`(k,η)`$ が、ω-Y の鍵のどの特別な場合に当たるかは、確かめていない。Phyrion 氏の ω-Y の証明は 1-Y の証明を含まない（`OneY` を import しない）。1-Y の鍵は（層の番号、根のラベル 1 つ）、ω-Y の鍵は（尺度ごとの根のラベルの列、⊤ の尾）で、形が違う。

### 3.4 1y-wo-por の関係は一般化できるか

もっともらしいが、確かめていない。

- 置き換え：$`(k,η) ∈ ω × ω_1`$ を $`θ ∈ \mathrm{Key}_m`$ にし、再帰の鍵を（上端、$`θ`$）にする。1y-wo-por の再帰の鍵（上端、層、添字）は、そのまま（上端、鍵）の辞書式になる。
- 内部の辺：鍵が頂点のラベルで決まるので、$`\mathrm{Rel}_j(x,y,z)`$ の代わりに、型板の形ごとの原子 $`\mathrm{Rel}_t(\vec r, y, z)`$（$`\vec r`$ は根の頂点）を置けばよい。形は有限個なので、論理式の全体は可算のままである。
- 上端への要求：条件が「鍵 $`\lt θ`$」になる。辞書式なので、「最初に違う座標 $`i`$ で小さい」と場合を分ける。座標 $`i`$ より前は $`θ`$ の座標と等しい。1y-wo-por の名前付きの述語の工夫（§3.8 の 3）を、この「前の座標は名前、座標 $`i`$ は名前より小さい」に広げる必要がある。見えるかどうかを位置だけで決められるかは、未確認である。ここが O7 の証明（見えないビットを偽にする翻訳）の要である。
- 実際には、この一般化は要らないかもしれない。Phyrion 氏の正の図式の版（1y-wo-por の案 B に当たる）が、ω-Y で本物の組合せの層と組み合わさって Lean で通っている。正の図式の版では、「鍵 $`\lt θ`$」は定義の中の意味の条件なので、位置による見え方の問題が起きない。
- Phyrion 氏の意味の層は、鍵の構文 `KeySyntax` を引数に取る。型板と評価と単調性さえあれば使える。したがって、公式の ω-Y に移るときも、意味の層は変えずに済む見込みが高い。変わるのは組合せの層である。

### 3.5 組合せの層で変わるところ

Phyrion 氏の ω-Y の組合せの層は、1-Y の `OneY` を使わない新しい 8 万行である。1-Y の層との対応は次のとおりに読める（監査の文書 [FINAL-DESCENT-AUDIT.md](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/docs/FINAL-DESCENT-AUDIT.md) から）。

| 1-Y | weak ω-Y |
|---|---|
| 有限の層を持つ図式 `Diagram`、辺 `Atom` | 実際に格納された辺 `RealStoredEdge` の全体。鍵は型板 |
| 層 $`k`$ の辺 | 跳びの指数 $`d`$ の辺。鍵は尺度 $`D..d`$ の根と $`⊤`$ |
| コピーの補題（BMS の補題 2.5） | 複写の辺の出どころの分類（普通の出どころ／magma の充填）、鍵の上界の運搬 |
| 抽出（Extraction） | 無い（no extraction） |
| ブロックごとの有限反映 | 反復する予備（reservoir）を持つ有限反映。移る列は古いラベルを使い回す |
| 末尾ラベルの Acc の帰納法 | 同じ（順序数のラベルの帰納法） |

公式の ω-Y で変わるところ（推測）：

- magma の辺の規則。weak magma の性質は、`ActualFillCopiedKey`（充填の辺の鍵は制御の辺の鍵より小さい）と `ActualFillControlEdge` で使われる。公式の規則で充填の辺がどこから親を取るかが分かるまで、この上界が成り立つかは分からない。
- 次元の保存。公式の規則で、展開のあとの行が展開の前の行の上限を超えないかは、確かめていない。超えるなら $`m`$ が軌道の中で増え、鍵の型が一定でなくなる。
- 提取。公式のプログラムが提取に当たる操作を持つかは確かめていない。

## 4. 計画の案（当時）

### 4.1 最初に決めること

1. **対象.** 次のどれかにする。
   - (A) 公式の ω-Y（Naruyoko 氏のプログラム）の整礎性。未解決で、価値が一番高い。組合せの層の大きな新しい仕事が要る。成り立つかも分からない。
   - (B) weak ω-Y。Phyrion 氏がすでに Lean で示した。残る仕事は、ライセンスの無い YesMetaZFC を外すことと、意味の層を 1y-wo-por の Σ₁ の版に取り替えることくらいで、新しい数学は少ない。
   - (C) weak と公式の関係。同値は偽である（§1.6）。公式の展開を weak の展開で上から抑える埋め込みのようなものがあるかは分からない。
2. **Phyrion 氏の ω-Y のコードに依存するか.** Apache-2.0 なので、取り込んで直してよい。1y-wo-por と同じく、`NOTICE` に出どころと変更点を書く。
3. **YesMetaZFC の扱い.** ω-Y のリポジトリが使う部分は小さい（`transGen_head` と ZeroY の森の 2 モジュール経由）。1y-wo-por の移植（`Por.BMS`）で書く部分と重なる。1y-wo-por の結果を使い回せる。
4. **公式の仕様の書き方.** Naruyoko 氏のコードはライセンスが無いので写さない。規則を数学の言葉で書き直し、プログラムは実行して結果を比べるだけにする。

(A) を選ぶなら、次の手順にする。

### 4.2 手順（(A) の場合）

| # | 手順 | 成果 | 判定 |
|---|---|---|---|
| 0 | Phyrion 氏の ω-Y を `leanman build` で再現する | 最終定理と公理の記録 | 緑、公理 3 つ |
| 1 | 公式の ω-Y の規則を、Naruyoko 氏のプログラムの挙動から数学の文章に書き起こす。山、根、コピー、持ち上げ、充填 | `notes/01-rules.md` | 自前の実装が N と全部一致 |
| 2 | 自前の実装（JavaScript、次に Lean の実行できる定義）を書き、N と差分試験をする。§1.6 の標準形の集合を使う | 試験の記録 | 一致 |
| 3 | weak と公式の違いを分類する。最小の食い違い $`(1,3,3)[2]`$ から、違うのが magma の規則か、再帰（weak/strong）か、提取かを特定する | [`notes/01-feasibility.md`](01-feasibility.md) | 違いを 1 つの規則の差で説明できる |
| 4 | Phyrion 氏の証明が使う組合せの不変量を、公式の規則で数値的に試す。次元 $`D`$ の保存、複写の辺の鍵の上界、充填の辺の鍵 $`\lt`$ 制御の鍵、境界の辺の分類。鍵の比較は列の番号の上の型板の比較（`templateKey`）で決まるので、ラベルを選ばずに計算で試せる | 反例または通過の記録 | 反例が無い |
| 5 | 4 が通ったら、紙の上で証明の筋を書く。どこが weak の証明と同じで、どこが新しいかを分ける | `notes/03-proof.md` | 査読 |
| 6 | Phyrion 氏の組合せの層を取り込み、展開の定義を公式のものに替えて、壊れたモジュールを直す | Lean | 緑 |
| 7 | 意味の層は Phyrion 氏のもの（または 1y-wo-por の一般化）をそのまま使う。YesMetaZFC を自前の補題に替える | Lean | 公理 3 つ |

### 4.3 リスク

1. **公式の ω-Y が停止しないかもしれない.** 証明も反例も知られていない。手順 4 で反例が出たら、無限の減少列を探す方向に切り替える。
2. **仕様の書き起こし.** 公式の定義はライセンスの無いコードだけである。書き起こしの誤りは差分試験でしか見つからない。1-Y では [1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) が同じ役をした。ω-Y ではこれを最初から作る必要がある。
3. **規模.** weak ω-Y の組合せの層だけで 8.3 万行ある。多くが AI の生成で、直すときに読むのが重い。公式の規則で magma の部分が変わると、`ActualFill*`、`Actual*Copied*`、境界の分類の多くのモジュールに波及しうる。
4. **次元の保存が破れる場合.** 鍵の型 $`\mathrm{Key}_m`$ の $`m`$ が軌道の中で増えると、今の枠組み（$`m`$ を固定した $`R`$）が使えない。そのときは、全次元の和 $`\bigsqcup_m \mathrm{Key}_m`$ に順序を入れて、$`m`$ を変えても鍵が下がることを示す必要がある。これが超限の層に当たるものになりうる。
5. **強さ.** 証明ができても、ラベルは $`ω_1`$ の下の閉じた点で、順序数の上界は出ない。
6. **ライセンス.** Phyrion 氏のコードは Apache-2.0 で問題ない。YesMetaZFC、Naruyoko 氏と MrredsharkFan 氏のコードはライセンスが無い。写さない。

### 4.4 分からないこと

- 公式のプログラムが、洛谷の解説の 4 つの magma の変種のどれに当たるか。
- 1-Y の「提取」が何で、公式の ω-Y に含まれるか。
- MHO が何か。$`ω\text{-}Y(1,ω)`$ の順序数の大きさ。
- 日本語版の wiki（Fandom）の記事の内容。この調査では取得できなかった。
- Naruyoko 氏の座標のベクトルと Phyrion 氏の Cantor の行の対応が、一般に正しいか。
