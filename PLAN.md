# PLAN — wy-wo-por

公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）。`ControlProof.wellFounded_of_block_keys` の残りの仮定は、出力の山の再構成 `BlockReconstruction` と `KeyLeRest` の 2 つ。

作業は依存の順に進める。葉が仮定にしてよいのは、証明済みの命題か、値の大きい列で真と確かめ済みで文面が決まった命題だけ（[notes/05-large-value-audit.md](notes/05-large-value-audit.md)）。段 A（土台と道筋）は済んだ。段 B の葉は互いに独立で、文面は決まっている。

- 段 B
  - 🤖 鎖の対応（共有。`KeyLeRest` と親の鎖の両方が使う）：`TopStep`、`TopStart`（`LowerChain.lean`）
  - `KeyLeRest` だけが使う（`keyLeRest_of_lower_main`）
    - 🤖 一番上の写しでない節点：`NonTopStep`、`StartRelNT`、`StartRootNT`
    - 🤖 すき間の写し：`StepCut`、`CutJump`、`CutStartCopyNT`、`CutStartRootNT`
  - 出力の山の再構成 `BlockReconstruction`
    - 🤖 行の法則の残り `LowerRowsCopy`、`LowerRowsBoundary`（`LowerPairsLeft` は証明済み、`jumpLawHolds_of_lowerRowsCases`）
    - 親の鎖
      - 🤖 `LowerParentBelowHolds`：`caseLower` に脚が `ℓ < c_r` の場合を足し、`Profile7` の残り `CutOrder`、`CutLeg`、`Lift`、`Boundary` を証明する（`NonCutOrderLeg`、`CutBetweenLeg` は証明済み）
      - 🤖 `CrossLexFor` の plain と clean の残り：`EmitBelow`、`CleanFirst`、`PairAbove`、`PairOld`、`RootPass`、`LexImg`（`crossLexFor_plain_lower`、`crossLexFor_clean_lower`）
