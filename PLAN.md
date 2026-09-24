# PLAN — wy-wo-por

公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）。`ControlProof.wellFounded_of_block_keys` の残りの仮定は、出力の山の再構成 `BlockReconstruction` と `KeyLeRest` の 2 つ。

作業は依存の順に進める。葉が仮定にしてよいのは、証明済みの命題か、値の大きい列で真と確かめ済みで文面が決まった命題だけ（[notes/05-large-value-audit.md](notes/05-large-value-audit.md)）。段 A（土台と道筋）は済んだ。

- 段 D（残りの命題。文面は決まっている）
  - 継ぎ目：`CutParentNT`（`BoundaryChain` はここから出る）、`StepRootTop`（`TopStepLoRoot` は `CutParentNT` とこれから出る）（`Seam*.lean`）
  - 親の鎖の plain と clean：`SeamStep`、`SeamStart`、`CopyCountLe`（`RootPass IsPlain`、`LexImg` はここから出る。`RPL*.lean` は未追跡）
  - `TopStart'` の残り：`TopStartLoRootW`、`StartRootTopUp`、`TopStartPaOUp`（または `PaONoGap`）、`TopStartCutRight`（`TopStartFixParts.lean`）
  - `CrossLexFor IsUpper`：古い帰着（`CopyQLower`、`InnerHolds`）は偽（反例 `(1,21,5,20,30,23,20)[1]`）。新しい帰着を作る
- 組み立て：`wellFounded_of_stageC'`（`TopStartFixAssembly.lean`）の仮定は、上の命題と `TopStepLoRoot`、`BoundaryChain`、`CutJumpRootRow`、`CutRunTop`（証明済み）など
