# 値の大きい列での数値の監査

2026-09-24。[04-official-design.md](04-official-design.md) §6.1 の続き。

`LegBelowTop` が値の大きい列 $`(1,2,4,8,10,8)`$ で破れた（値 9 以下の試験では見つからなかった）。そこで、開いている命題、コミット済みの帰着の仮定、目標の命題のすべてを、値の大きい列で試し直した。この文書は JS の試験だけで、Lean の証明は増えていない。

## 1. 要約

- **目標の命題は、どの標本でも失敗 0 だった。** 降下 $`s[n] \lt s`$、分類 `classifiedB`、`BlockReconstruction`、`WitnessHolds`、`KeyLeRest`、`RowLawHolds`、`JumpLawHolds`、`ChainHolds`、`ParentBelowHolds`、`CrossChainHolds`。
- **コミット済みの帰着の仮定のうち、次のものが数値の上で偽である。**

| 仮定 | 最短の反例（見つかった中で） | 最初に見つかった標本 |
|---|---|---|
| `LegBelowTop`（Lean で偽） | $`(1,3,9,11,9)`$ | A |
| `StartLeg`、`LegRight`、`LowerLegGe` | $`(1,3,9,11,9)[1]`$ | A |
| `StartCopy`、`CutTop`、`GapTop`（`GapTop` は Lean で偽） | $`(1,3,8,10,13,8)[1]`$ | D、F、K |
| `StepInner`（$`m' \gt c_r`$ の場合）、`LegLookup`（$`p_a \gt c_r`$ の場合）、`LegGapTop` | $`(1,3,8,10,15,8)[1]`$ | F、K |
| `MAHolds`（MA）、`CopyOrder`、写しの行の式（Formula） | $`(1,3,6,13,15,13)[1]`$ | D、F、K |
| `Profile7` の `NonCutOrder`、`CutBetween`（`NonCutOrder` は Lean で偽） | $`(1,3,6,13,15,13)[1]`$ | D、K |

- 「Lean で偽」の意味：`LegBelowTop` の反証（`LegBelowTopFalse.lean`、コミット済み）はカーネルの評価だけで閉じている。`GapTop`（と `CutTop`、`StartCopy`）の反証 `StartRootPartsGapTopFalse.lean` と、`NonCutOrder` の反証 `ParentBelowLowerFixFalse.lean` は未追跡のファイルで、展開の事実を Bool の検査（`gCheck`、`nonCutCheck`）にまとめ、それが `true` であることを仮定する形（`gCheck = true → ¬ GapTop` など）である。検査は `#guard`（コンパイルした評価）で確かめていて、カーネルの証明ではない。
- 上の表の後ろ 4 行の仮定は、長さ 5 以下・値 20 以下（A と E）と、長さ 6 以下・値 12 以下（A）では破れなかった（`Profile7` は E の約 1/4 だけ試した）。長さ 6・値 15 以下（F、$`n = 1`$）では、`StartCopy` は 10 回、`StepInner` は 3 回、MA と `CopyOrder` は $`(1,3,6,13,15,13)`$ の 1 列だけで破れた。破れる列はまれである。
- 偽の仮定を使うコミット済みの定理は §4 に挙げた。`KeyLeRest` への道筋（`wellFounded_of_chains`、`wellFounded_of_local`、`wellFounded_of_all_chains`、`wellFounded_of_cut_*`）は、どれも `StartLeg`、`StartCopy`、`StepInner` のどれかを仮定するので、今の形では使えない。`KeyLeRest` 自身は成り立っている。
- ほかのエージェントの作業中の帰着（未追跡のファイル）では、`CopyAsc`（$`(1,3,11,12,11)[1]`$）、`LegGapTopLow` と `GapKidRow`（$`(1,3,9,11,16,8)[1]`$。F の $`(1,3,8,10,15,8)[1]`$ でも破れることを個別に確かめた）、`PosChainImg` の最初の形（像の種類が $`u^+`$ と同じことを求める形。$`(1,3,10,20,10)[1]`$）が破れた。`PosChainImg` は、この監査の終わりごろ（2026-09-24 04:54）に、像の種類が違ってもよい形に直された（`CrossPlainPos.lean`、`cross-plain-pos-img.cjs`）。直した形は $`(1,3,10,20,10)[n]`$（$`n = 1,2,3`$）で失敗 0 である。表の数は最初の形のものである。`StepInner` と `StartCopy` を弱めた `StepInnerSkip`、`StartCopySkip`（`LegPartsSkip.lean`）は、どの標本でも失敗 0 だった。

## 2. 標本

どの列も 1 で始まり、1 で終わらない（末項が 1 の展開は末項を消すだけなので除いた）。展開は $`n = 1, 2, 3`$。

| 名前 | 列 | 列の数 | 展開（300 節点以下） |
|---|---|---:|---:|
| A | 長さ 6 以下、値 12 以下の合法な列すべて | 248831 | 688652 |
| B | A のうち `LegBelowTop` が破れる 64 列（[samples/legbelowtop-bad64.json](../reference/official/samples/legbelowtop-bad64.json)） | 64 | 192 |
| C | 長さ 7、値 10 以下の合法な列から、種を決めた無作為の 1/8（長さ 6 以下、値 10 以下の列は A に含まれるので C には入れない） | 113149 | 324880 |
| D | 長さ 2〜8、値 20 以下の無作為の合法な列 | 30000 | 72098 |
| E | 長さ 5 以下、値 20 以下で、最大の値が 13 以上の合法な列すべて | 139264 | 326636 |
| F | 長さ 6、値 15 以下で、最大の値が 13 以上の列すべて。$`n = 1`$ だけ、ハーネスは `chain-corr`、`copy-shape`、`startcopy-root-parts`、`step-inner-lookup` だけ | 480654 | 480654 |
| K | この監査と Lean の反証で見つかった反例 17 列（[samples/known-counterexamples.json](../reference/official/samples/known-counterexamples.json)） | 17 | 51 |

- 出力の山が 300 節点を超える展開（「大きい展開」）は、ハーネスによっては 1 回に数十分かかる。A、C、D、E の大きい展開は、それぞれ $`n`$ ごとに、300 節点を超え 1500 節点以下のものを種を決めた無作為で 200 個選んで試した（表の A、C、D、E に含めた。各 600 展開）。大きい展開の数は A 57841、C 14567、D 17902、E 91156 で、試したのはその一部である。
- `parent-below-lower.cjs`（`Profile7` と `LegRight`）は重いので、E は 4 チャンクに 1 つ（約 1/4）、大きい展開は $`n`$ ごとに 5 個だけ試した。
- `cut-regions.cjs` は 1 つの入力で $`n = 1,2,3`$ をまとめて試すので、$`n = 3`$ で 300 節点以下の列だけを入力にした。

## 3. 方法

- ハーネスは [reference/official/](../reference/official/) にあるもの（この repository のコード）をそのまま使った。展開は `omegay-trace.cjs`（`omegay.cjs` と同じ規則）である。
- 実行と集計は [reference/official/large-value-audit.cjs](../reference/official/large-value-audit.cjs) で行った（`gen`、`run`、`table`）。
- 「回数」はハーネスごとの検査の数で、単位はハーネスによって違う（節点、節点の組、写しの組など）。2 つのハーネスの回数は比べられない。
- 失敗は、ハーネスが `FAIL`（または `fails`、`false`）と報告したものである。情報のための行（例えば「上がる条件を外すと偽」）は表に入れていない。
- 最短の反例は、ハーネスが報告した例（チャンクごとに最初の 3 つまで）の中で、長さ、最大の値、和の順に最小のものである。`cross-plain-pos-img.cjs` と `cross-upper-sim.cjs` は `-v` を付けないと例を出さないので、`PosChainImg` の例は `-v` で再実行して得た。

## 4. 偽の仮定を使うコミット済みの定理

（定理の仮定に命題が現れるものを、コミット済みのファイルから機械的に拾った。）

- `StartLeg`（15 個）、`StartCopy`（13 個）：`wellFounded_of_chains`、`wellFounded_of_local`、`wellFounded_of_all_chains`、`wellFounded_of_chains_cut`、`wellFounded_of_cut_rest`、`wellFounded_of_cut_parts`、`wellFounded_of_cut_final`、`keyLeRegion_of_chains`、`region*_of_chains` など。
- `StepInner`（26 個）：上の整礎性の定理のほか、`regionCutBoundary_of_chains`、`regionCutInner_of_chains`、`stepCut_of_rest`、`cut_statements*`、`startRoot_of_open`、`boundaryChain_of_parts` など。
- `CopyOrder`（20 個）：`startCopy_of_parts`、`startCopy_of_open`、`startJump_of_open`、`startLeg_startJump`、`legLookup_of_parts`、`stepInner_of_open`、`cutStartCopy_of_parts`、`cut_statements*` など。
- `MAHolds`（11 個）：`column_shape`、`copyOrder_of_facts`、`copyEmitted_of_facts`、`copyFirst_of_facts`、`copyOrder_of_MA_MH` など。`CopyEmitted`、`CopyFirst` 自身は成り立っているが、MA からの導き方は使えない。
- `LegLookup`（4 個）、`LegGapTop`（3 個）：`stepInner_of_lookups`、`stepInner_of_rest`、`stepInner_of_profile`、`legLookup_of_parts`、`stepInner_of_open` など。
- `CutTop`、`GapTop`：`startCopy_of_parts`、`startCopy_of_open`、`startCopy_of_gapTop`、`cutTop_of_gapTop`。
- `LegBelowTop`（11 個）、`LowerLegGe`（3 個）、`LegRight`、`Profile7`：`jumpLawHolds_of_lowerRows`、`lowerPairsHolds_of_parts`、`jumpLawHolds_of_lowerCases`、`lowerParentBelowHolds_of_parts`、`parentBelowHolds_of_parts` など。

これらの定理そのものは正しい（仮定が偽なら結論について何も言わない）。直すべきは道筋である。

## 5. 全体の表

表の各欄は「回数」、失敗があるときは「回数 / **失敗**」である。「-」は、その標本で検査の場面が無かったか、そのハーネスを走らせなかった（F）こと。k = 千、M = 百万、G = 十億。「Lean の状態」は PLAN.md、04-official-design.md、ハーネスの注記と、コミット済みのファイルの定理による。「開（未追跡）」は、ほかのエージェントが作業中の、まだコミットされていないファイルの命題である。

### 目標

| 命題 | Lean の状態 | ハーネス | A | B | C | D | E | F | K | 最短の反例 |
|---|---|---|---|---|---|---|---|---|---|---|
| 降下 s[n] < s（辞書式） | 目標 | check | 689k | 192 | 325k | 73k | 327k | - | 51 |  |
| 分類 classifiedB（ClassificationHoldsNE の中身） | 目標 | reserve | 689k | 192 | 325k | 73k | 327k | - | 51 |  |
| BlockReconstruction = ReconstructionHolds | 目標 | check | 689k | 192 | 325k | 73k | 327k | - | 51 |  |
| WitnessHolds（KeyWitnessRest） | 目標 | classification-witness | 29.8M | 7578 | 12.2M | 4.8M | 22.5M | - | 2956 |  |
| KeyLeRest（KeyLeShift） | 目標 | keylerest-regions | 28.9M | 7578 | 11.8M | 4.7M | 21.9M | - | 2884 |  |
| RowLawHolds | 目標 | recon-targets | 26.3M | 6294 | 10.4M | 4.4M | 20.9M | - | 2608 |  |
| JumpLawHolds | 目標 | recon-targets | 26.3M | 6294 | 10.4M | 4.4M | 20.9M | - | 2608 |  |
| ChainHolds | 目標 | recon-targets | 26.3M | 6294 | 10.4M | 4.4M | 20.9M | - | 2608 |  |
| ParentBelowHolds | 目標 | recon-targets | 26.3M | 6294 | 10.4M | 4.4M | 20.9M | - | 2608 |  |
| CrossChainHolds | 目標 | recon-targets | 2.1M | 918 | 1.0M | 255k | 1.0M | - | 192 |  |

### 再構成の帰着（Recon/）

| 命題 | Lean の状態 | ハーネス | A | B | C | D | E | F | K | 最短の反例 |
|---|---|---|---|---|---|---|---|---|---|---|
| BumpChainHolds | 証明済み | recon-targets | 26.3M | 6294 | 10.4M | 4.4M | 20.9M | - | 2608 |  |
| LowerPairsHolds | 開 | jump-law-split | 17.2M | 4968 | 6.6M | 2.8M | 13.9M | - | 2005 |  |
| LowerRowsCopy | 開 | jump-law-lower | 7.2M | 1092 | 2.7M | 1.3M | 7.0M | - | 529 |  |
| LowerRowsBoundary | 開 | jump-law-lower | 10.1M | 3474 | 4.0M | 1.5M | 6.9M | - | 1434 |  |
| LowerLegGe | 開（LegBelowTop から） | jump-law-lower | 17.2M / **402** | 4968 / **402** | 6.6M / **6** | 2.8M / **315** | 13.9M / **681** | - | 2005 / **42** | (1,3,9,11,9)[1] X=6 k=3 |
| SameColumnBelowHolds | 開 | recon-targets | 24.3M | 5376 | 9.4M | 4.1M | 19.9M | - | 2416 |  |
| LowerSameColumnBelowHolds | 開 | recon-targets | 7.6M | 956 | 2.8M | 1.4M | 6.6M | - | 660 |  |
| LowerParentBelowHolds | 開 | recon-targets | 8.0M | 1322 | 3.0M | 1.4M | 6.9M | - | 762 |  |
| Profile7: NonCutOrder | 開 | parent-below-lower | 110.8M | 97k | 48.1M | 18.3M / **120** | 20.3M | - | 35k / **180** | (1,3,6,13,15,13)[1] i=1 3 4 |
| Profile7: CutBetween | 開 | parent-below-lower | 406.8M | 54k | 135.9M | 91.6M / **212** | 119.5M | - | 42k / **295** | (1,3,6,13,15,13)[1] i=1 2 4 |
| Profile7: CutOrder | 開 | parent-below-lower | 6.7G | 39k | 2.0G | 1.9G | 2.4G | - | 105k |  |
| Profile7: CutLeg | 開 | parent-below-lower | 82.0M | 8180 | 28.6M | 14.9M | 19.7M | - | 5510 |  |
| Profile7: Emitted（i ≥ 1） | 開 | parent-below-lower | 8.8M | 4896 | 3.9M | 1.2M | 1.3M | - | 1482 |  |
| Profile7: Lift | 開 | parent-below-lower | 10.7M | 6048 | 4.8M | 1.4M | 1.6M | - | 1806 |  |
| Profile7: Boundary | 開 | parent-below-lower | 8.8M | 1957 | 3.6M | 1.1M | 1.4M | - | 790 |  |
| LegRight | 開（LegBelowTop から） | parent-below-lower | 33.9M / **402** | 6082 / **402** | 12.4M / **6** | 5.7M / **312** | 7.4M / **351** | - | 2691 / **42** | (1,3,9,11,9)[1] i=1 y=3 ω |
| CrossLexHolds | 開 | cross-lex | 2.1M | 918 | 1.0M | 255k | 1.0M | - | 192 |  |
| CutPredHolds | 証明済み | cut-pred | 13.3M | 1980 | 5.0M | 2.3M | 11.3M | - | 1096 |  |
| LiftPosHolds | 証明済み | cut-pred | 1.3M | 9 | 478k | 211k | 1.1M | - | 99 |  |
| CleanGapHolds | 証明済み | cut-pred | 1.3M | 9 | 478k | 211k | 1.1M | - | 99 |  |
| CrossLexPos IsPlain | 開 | cross-plain-pos | 805k | 426 | 360k | 105k | 461k | - | 51 |  |
| CrossLexPos IsClean | 開 | cross-plain-pos | 75k | 300 | 38k | 11k | 28k | - | 36 |  |
| SeamLastPosHolds | 開 | cross-upper | 163k | - | 81k | 17k | 70k | - | 15 |  |
| InnerHolds | 開 | cross-upper | 420k | - | 254k | 47k | 136k | - | 36 |  |

### KeyLeRest の帰着（Classification/Proofs/）

| 命題 | Lean の状態 | ハーネス | A | B | C | D | E | F | K | 最短の反例 |
|---|---|---|---|---|---|---|---|---|---|---|
| RegionUpper | 開 | keylerest-regions | 6.7M | 702 | 2.8M | 1.2M | 5.3M | - | 306 |  |
| RegionPlainBoundary | 開 | keylerest-regions | 1.5M | 579 | 683k | 181k | 814k | - | 198 |  |
| RegionPlainInner | 開 | keylerest-regions | 3.3M | 2286 | 1.6M | 467k | 2.0M | - | 666 |  |
| RegionCleanBoundary | 開 | keylerest-regions | 415k | 237 | 177k | 49k | 233k | - | 78 |  |
| RegionCleanInner | 開 | keylerest-regions | 1.4M | 978 | 623k | 190k | 816k | - | 264 |  |
| RegionCutBoundary | 開 | keylerest-regions | 4.7M | 325 | 1.8M | 654k | 3.0M | - | 238 |  |
| RegionCutInner | 開 | keylerest-regions | 8.6M | 1655 | 3.2M | 1.6M | 8.3M | - | 858 |  |
| StepInner | 開 | chain-corr | 66.9M | 17k | 25.9M | 16.7M | 72.4M | 50.3M / **3** | 5826 / **36** | (1,3,8,10,15,8)[1] X=8 v=3 k=1 |
| StartLeg | 開 | chain-corr | 20.1M / **402** | 6060 / **402** | 8.0M / **6** | 3.2M / **315** | 15.1M / **681** | 18.3M / **578** | 2302 / **42** | (1,3,9,11,9)[1] X=6 |
| StartJump | 開 | chain-corr | 13.4M | 4380 | 5.9M | 2.1M | 9.2M | 6.6M | 1470 |  |
| StartCopy | 開 | chain-corr | 3.4M | 1140 | 1.7M | 495k / **6** | 1.7M | 1.4M / **10** | 576 / **30** | (1,3,8,10,13,8)[1] X=8 u=3 |
| StartRoot | 開 | chain-corr | 10.1M | 3240 | 4.2M | 1.6M | 7.5M | 5.2M | 894 |  |
| MAHolds（MA） | 開 | copy-shape | 300 | 138 | 6 | 1152 / **12** | 2396 | 1248 / **1** | 114 / **24** | (1,3,6,13,15,13)[1] i=1 x=4 S=3:0 rho=2 |
| MA の M(s) だけの形（MASourceTop） | 偽（Lean） | copy-shape | 315 | 72 | 3 | 598 / **6** | 1257 | 1620 / **1** | 60 / **12** | (1,3,6,13,15,13) x=4 S=3:0 |
| MHHolds（MH） | 開 | copy-shape | 1.3M | 9 | 478k | 211k | 1.1M | 1.1M | 99 |  |
| MDHolds（MD） | 証明済み | copy-shape | 12.4M | 1238 | 4.4M | 2.7M | 12.5M | 18.2M | 817 |  |
| 写しの行の式（Formula、CopyShape） | 開 | copy-shape | 14.0M | 4782 | 6.1M | 2.2M / **12** | 9.5M | 6.6M / **1** | 1563 / **24** | (1,3,6,13,15,13)[1] i=1 x=4 src=ω row=ω want=ω·2 |
| CopyOrder | 開 | startcopy-root-parts | 250.0M | 64k | 106.7M | 60.0M / **96** | 234.6M | 168.4M / **3** | 30k / **141** | (1,3,6,13,15,13)[1] i=1 y=3 y'=4 ω+1 ω |
| CopyEmitted | 開 | startcopy-root-parts | 11.6M | 3966 | 5.1M | 1.9M | 8.2M | 6.6M | 1266 |  |
| CopyFirst | 開 | startcopy-root-parts | 11.6M | 3966 | 5.1M | 1.9M | 8.2M | 6.6M | 1266 |  |
| CopyMono | 証明済み | startcopy-root-parts | 18.0M | 4721 | 7.1M | 3.2M | 15.6M | 21.0M | 1878 |  |
| CutTop | 開 | startcopy-root-parts | 395 | - | 288 | 377 / **6** | - | 339 / **10** | 84 / **30** | (1,3,8,10,13,8)[1] X=8 u=3 |
| BoundaryChain | 開 | startcopy-root-parts | 14.3M | 7812 | 5.7M | 3.1M | 13.2M | 6.6M | 3324 |  |
| OriginReach | 開 | startcopy-root-parts | 7.1M | 9000 | 2.9M | 1.5M | 5.7M | 2.2M | 2175 |  |
| LegLookup | 開 | step-inner | 8.0M | 2112 | 3.3M | 1.4M | 6.4M | - | 774 / **12** | (1,3,9,11,16,8)[1] X=8 v=3 plain(4,2)。F の (1,3,8,10,15,8)[1] でも偽（個別に確かめた。F では step-inner を走らせていない） |
| BumpCopyLower | 開 | step-inner | 3.1M | 1878 | 1.5M | 447k | 1.9M | - | 606 |  |
| NextCopyPlain | 開 | step-inner | 3.1M | 1878 | 1.5M | 447k | 1.9M | - | 606 |  |
| CleanNext | 開 | step-inner | 1.4M | 978 | 623k | 190k | 816k | - | 264 |  |
| CleanLookup | 開 | step-inner | 1.4M | 978 | 623k | 190k | 816k | - | 264 |  |
| CleanParent | 開 | step-inner | 1.4M | 954 | 618k | 189k | 815k | - | 246 |  |
| PlainOnce | 証明済み | step-inner | 3.3M | 2286 | 1.6M | 467k | 2.0M | - | 666 |  |
| LegGapTop | 開 | step-inner-lookup | 978k | 432 | 529k | 194k | 547k | 467k / **1** | 282 / **12** | (1,3,8,10,15,8)[1] X=8 v=3 plain m=(4,2) |
| LegOriginReach | 開 | step-inner-lookup | 540k | 936 | 276k | 78k | 250k | 210k | 198 |  |
| LegLeft（legLookup_left、LegBelowTop から） | 開（LegBelowTop から） | step-inner-lookup | 104k | 36 | 43k | 19k | 77k | 46k | 30 |  |
| BoundaryStepLower | 開 | start-root-parts | 15.2M | 4920 | 6.1M | 2.6M | 12.2M | - | 1581 |  |
| BoundaryCutChain | 開 | start-root-parts | 405k | 1272 | 100k | 182k | 931k | - | 396 |  |
| PaLookup | 開 | start-root-parts | 9.6M | 3240 | 3.9M | 1.5M | 7.2M | - | 852 |  |
| X0Reach | 開 | start-root-parts | 4.0M | 3192 | 1.6M | 818k | 3.5M | - | 942 |  |
| GapTop | 偽（Lean） | start-root-parts | 395 | - | 288 | 377 / **6** | - | - | 84 / **30** | (1,3,8,10,13,8)[1] X=8 u=3 |
| OriginUpper | 証明済み | start-root-parts | 460k | - | 249k | 76k | 233k | - | 42 |  |
| BoundaryChain（i = 1） | 証明済み | start-root-parts | 6.9M | 3270 | 2.8M | 1.5M | 6.2M | - | 1464 |  |
| StepCut | 開 | cut-regions | 31.8M | 6145 | 10.4M | 6.8M | 39.2M | - | 4124 |  |
| CutJump | 開 | cut-regions | 9.3M | 1980 | 3.5M | 1.1M | 5.7M | - | 1096 |  |
| CutLeg（cutLeg） | 証明済み | cut-regions | 9.3M | 1980 | 3.5M | 1.1M | 5.7M | - | 1096 |  |
| CutStartCopy | 開 | cut-regions | 3.6M | 660 | 1.2M | 460k | 2.9M | - | 232 |  |
| CutStartRoot | 開 | cut-regions | 5.7M | 1320 | 2.3M | 623k | 2.7M | - | 864 |  |
| CutRunLow | 開 | cut-parts | 6.2M | 660 | 2.3M | 1.2M | 6.3M | - | 232 |  |
| CutRunHigh | 開 | cut-parts | 6.2M | 660 | 2.3M | 1.2M | 6.3M | - | 232 |  |
| CutOriginReach | 開 | cut-parts | 495k | 3058 | 113k | 270k | 1.2M | - | 564 |  |
| CutJumpTop | 開 | cut-parts | 13.3M | 1980 | 5.0M | 2.3M | 11.3M | - | 1096 |  |
| CutBump | 開 | cut-parts | 1.4M | 954 | 618k | 189k | 815k | - | 246 |  |
| CutLegLookup | 開 | cut-parts | 1.4M | 954 | 618k | 189k | 815k | - | 246 |  |
| CutTopLookup | 開（CutBump などから） | cut-parts | 1.4M | 954 | 618k | 189k | 815k | - | 246 |  |
| CutTopNext | 開（CopyOrder などから） | cut-parts | 1.4M | 954 | 618k | 189k | 815k | - | 246 |  |
| CutPaRow | 証明済み | cut-parts | 13.3M | 1980 | 5.0M | 2.3M | 11.3M | - | 1096 |  |
| CutGenReach | 証明済み | cut-parts | 60.7M | 6145 | 20.1M | 18.5M | 93.7M | - | 4124 |  |
| LegBelowTop | 偽（Lean） | startleg-jump | 4.7M / **201** | 2448 / **201** | 2.1M / **3** | 683k / **166** | 3.0M / **351** | - | 741 / **21** | (1,3,9,11,9) x=3 ω |
| LegRowMatchRootLower | 証明済み | startleg-jump | 1.6M | 1704 | 756k | 182k | 760k | - | 363 |  |
| StepJumpLe（StepJump） | 証明済み | startleg-jump | 11.1M | 3690 | 4.7M | 1.8M | 8.3M | - | 1266 |  |
| BoundaryRootRows | 証明済み | legrowmatch-lower | 1.9M | 1152 | 891k | 212k | 921k | - | 324 |  |
| RowFixed（emitsT_fixed） | 証明済み | legrowmatch-lower | 3.4M | 3246 | 1.7M | 399k | 1.5M | - | 750 |  |
| TopAboveRoot | 証明済み | legrowmatch-lower | 1.6M | 438 | 620k | 286k | 1.3M | - | 285 |  |
| LiftLast | 証明済み | step-inner-clean | 1.1M | 240 | 443k | 155k | 746k | - | 111 |  |
| LiftTwo | 証明済み | step-inner-clean | 936k | 972 | 455k | 110k | 374k | - | 228 |  |

### ほかのエージェントの作業中の帰着（未追跡のファイル）

| 命題 | Lean の状態 | ハーネス | A | B | C | D | E | F | K | 最短の反例 |
|---|---|---|---|---|---|---|---|---|---|---|
| CrossPlainPos: PosChainImg（最初の形。今は直されている、§1） | 開（未追跡） | cross-plain-pos-img | 880k | 726 | 398k | 116k | 490k / **12** | - | 87 | (1,3,10,20,10)[1] X=6 u=3 |
| CrossPlainPos: PosLexAt | 開（未追跡） | cross-plain-pos-img | 880k | 726 | 398k | 116k | 490k | - | 87 |  |
| CrossPlainPosColumn: BelowSrc | 開（未追跡） | cross-plain-pos-img | 3.9M | 2988 | 1.6M | 573k | 2.6M | - | 909 |  |
| CrossPlainPosColumn: EmitBelow | 開（未追跡） | cross-plain-pos-img | 3.9M | 2988 | 1.6M | 573k | 2.6M | - | 909 |  |
| CrossPlainPosColumn: CleanFirst | 開（未追跡） | cross-plain-pos-img | 1.9M | 1215 | 800k | 239k | 1.0M | - | 342 |  |
| CrossPlainPosLex: LexImg | 開（未追跡） | cross-plain-pos-img | 1.8M | 1686 | 820k | 271k | 1.1M | - | 297 |  |
| CrossUpperSim: CopyTop | 開（未追跡） | cross-upper-sim | 2.8M | 1092 | 1.4M | 314k | 1.3M | - | 297 |  |
| CrossUpperSim: CopyStepLower | 開（未追跡） | cross-upper-sim | 4.6M | 2832 | 2.1M | 620k | 350k | - | 852 |  |
| CrossUpperSim: CopyQLower | 開（未追跡） | cross-upper-sim | 2.6M | 660 | 1.3M | 293k | 1.2M | - | 219 |  |
| LegPartsGap: LegGapTopLow | 開（未追跡） | leg-parts | 339k | - | 150k | 94k | 266k | - | 90 / **12** | (1,3,9,11,16,8)[1] X=8 v=(8,3:3) m=(4,2:2) |
| LegParts: GapKidRow | 開（未追跡） | leg-parts | 264k | - | 119k | 40k | 148k | - | 36 / **6** | (1,3,9,11,16,8)[1] i=1 p=(3,1:1) m=(4,2:2) |
| LegPartsOrigin: LegPaLookup | 開（未追跡） | leg-parts | 482k | 936 | 251k | 66k | 209k | - | 198 |  |
| LegPartsSkip: LegGapSkip | 開（未追跡） | leg-parts | - | - | - | - | - | - | 12 |  |
| LegPartsSkip: StepInnerSkip | 開（未追跡） | leg-parts | 66.9M | 17k | 25.9M | 16.7M | 72.4M | - | 5826 |  |
| LegPartsSkip: StartCopySkip | 開（未追跡） | leg-parts | 3.4M | 1140 | 1.7M | 495k | 1.7M | - | 576 |  |
| ChainCorrLegLeftItems: LiftLegRight | 開（未追跡） | lift-leg-right | 5.8M | 1281 | 2.1M | 1.3M | 6.2M | - | 693 |  |
| ChainCorrLegLeftItems: 項目の不変条件 | 開（未追跡） | lift-leg-right-items | 7.1M | 852 | 2.7M | 1.2M | 5.9M | - | 681 |  |
| ChainCorrLegLeft: StartJumpGe | 開（未追跡） | startleg-left | 13.4M | 4380 | 5.9M | 2.1M | 9.2M | - | 1470 |  |
| ChainCorrLegLeft: LegLeftRow など 5 つ | 開（未追跡） | startleg-left | 2010 | 2010 | 30 | 1575 | 3405 | - | 210 |  |
| JumpLawLowerLeft: LowerPairsLeft | 開（未追跡） | startleg-left | 402 | 402 | 6 | 315 | 681 | - | 42 |  |
| LowerBndMore: BndCutRow2 | 開（未追跡） | lower-rows-parts | 15.0M | 34 | 5.3M | 3.0M | 12.7M | - | 859 |  |
| LowerBndMore: BndTop3 | 開（未追跡） | lower-rows-parts | 1.2M | 9 | 446k | 192k | 999k | - | 99 |  |
| LowerBndMore: BndRest2 | 開（未追跡） | lower-rows-parts | 1.8M | 3399 | 824k | 227k | 917k | - | 643 |  |
| LowerCopyClean: CopyAsc | 開（未追跡） | lower-rows-parts | 6.9M / **170** | 660 | 2.5M | 1.3M / **1149** | 6.9M / **2778** | - | 396 / **60** | (1,3,11,12,11)[1] X=6 k=2 e=0 |
| LowerCopyClean: CopyRest | 開（未追跡） | lower-rows-parts | 477k | 432 | 212k | 93k | 344k | - | 225 |  |
| StepInnerClean: GapTwo | 開（未追跡） | step-inner-clean | 503k | 6 | 168k | 80k | 442k | - | 36 |  |
| StepInnerClean: ChainRoot | 開（未追跡） | step-inner-clean | 1.4M | 978 | 623k | 190k | 816k | - | 264 |  |
| StepInnerCleanParent: ViaRoot | 開（未追跡） | step-inner-viaroot | 810 | 366 | 78 | 228 | 639 | - | 42 |  |

### LegBelowTop の一般形（参考、legbelowtop-parts.cjs）

| 命題 | Lean の状態 | ハーネス | A | B | C | D | E | F | K | 最短の反例 |
|---|---|---|---|---|---|---|---|---|---|---|
| NoCross | 参考 | legbelowtop-parts | 21.8M / **1673** | 4360 / **587** | 7.7M / **25** | 6.0M / **4613** | 31.4M / **5108** | - | 1316 / **199** | (1,3,9,11,9) a=(4,3) v=(3,1) |
| LowerIT | 参考 | legbelowtop-parts | 360.7M / **1673** | 28k / **587** | 133.1M / **25** | 105.6M / **4613** | 398.5M / **5136** | - | 27k / **299** | (1,3,9,11,9) a=(4,3) v=(3,1) |
| NC1 | 参考 | legbelowtop-parts | 73.9M / **4754** | 24k / **144** | 34.5M / **653** | 12.6M / **6955** | 49.4M / **8622** | - | 7905 / **311** | (1,3,9,10,9) a=(4,3) c=3 |


## 6. 読み取れること

- 破れた仮定は、どれも「写しの形」か「脚の列」についての強い形である。値が大きいと、根の行の写し（gap の写し）や、脚が $`c_r`$ より左の節点が、値の小さい列には無い並び方をする。一方で、目標の命題と、それを直接言い換えた命題（`LowerPairsHolds`、`LowerParentBelowHolds`、`CrossLexHolds`、7 つの領域の補題 `Region*`）は失敗 0 である。偽の仮定は証明の道筋が強すぎたためで、目標が偽である兆しは見つからなかった。
- `StepInner` と `StartCopy` が破れる入力（K）では、弱い形 `StepInnerSkip`、`StartCopySkip`（`LegPartsSkip.lean`、未追跡）が成り立っている。弱い形では、$`m' \gt c_r`$ の写しの節点に届く代わりに、$`\varphi(\mathrm{col}\, m')`$ かそれより左の列の節点で、そこから $`m'`$ の先の元の山の一歩がすべて対応するものに届けばよい。`KeyLeRest` の道筋は、この弱い形に置き換えるのが一つの候補である。
- `CopyEmitted`、`CopyFirst`、`MH` は成り立つが、それらを MA から出す証明（`CopyShape*.lean`）は MA が偽なので使えない。`CopyOrder` は偽なので、それを使う `StartCopy`、`LegLookup`、`CutPartsTop` の道筋も直す必要がある。
- `Profile7` は `NonCutOrder` と `CutBetween` が偽なので（`NonCutOrder` の Lean の反証 `ParentBelowLowerFixFalse.lean` は $`(1,5,16,11,29,32,26)[1]`$ を使うが、より短い $`(1,3,6,13,15,13)[1]`$ でも破れる）、`LowerParentBelowHolds` への道筋も直す必要がある。`LowerParentBelowHolds` 自身は失敗 0 である。

## 7. 限界

- 大きい展開（300 節点超）は一部しか試していない（§2）。値の大きい列の多くはここに入る。
- `parent-below-lower.cjs` は E の約 1/4 と、大きい展開の 60 個だけである。
- 長さ 6 で値 16〜20 の列と、長さ 7 以上で値 11 以上の列は、D の無作為の列と K でしか試していない。F は $`n = 1`$ と 4 つのハーネスだけである。
- 最短の反例は、見つかった例の中での最短であり、最短であることの証明ではない。
