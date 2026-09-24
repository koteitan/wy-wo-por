# PLAN — wy-wo-por

公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）。`ControlProof.wellFounded_of_block_keys` の残りの仮定は、出力の山の再構成と `KeyLeRest` の 2 つ。

作業は依存の順に進める。葉が仮定にしてよいのは、証明済みの命題か、値の大きい列で真と確かめ済みで文面が決まった命題だけ（[notes/05-large-value-audit.md](notes/05-large-value-audit.md)）。

- 段 A：土台と道筋、それに依存しない葉
  - 🤖 写した列の形：`LowerPB.Emitted`、`CopyEmitted`、`CopyFirst`、MH と、偽の MA・`CopyOrder`・`NonCutOrder`・`CutBetween` に代わる真の命題の文面を決めて証明する（`CopyShape*.lean`）
  - 🤖 `KeyLeRest` の道筋を作り直す：偽の `StepInner`、`StartCopy` を弱い形 `StepInnerSkip`、`StartCopySkip` に置き換える。写した列の下の部分の鎖の対応を 1 組の補題にまとめ、`KeyLeRest` の側と親の鎖の側（`CopyQLower`、`CopyStepLow`、`CrossLexPos`）の両方で使う
  - 🤖 `LowerPairsLeft`（脚が `c_r` より左の組の jump の法則。使うのは証明済みの `LiftLegRight` だけ）
  - 🤖 検証：`LiftLegRight`、`LegRowMatchInner`、`StartJump` の証明（`LiftLegRightProof.lean`、`LegRowMatchInner*.lean`）
  - 🤖 検証：`SeamLastPosHolds`、`InnerHolds` の帰着（`CrossUpperSim*.lean`）
- 段 B：写した列の形が決まってから
  - 行の法則の `LowerRowsCopy` と `LowerRowsBoundary`
  - `LowerParentBelowHolds`：`caseLower` に脚が `ℓ < c_r` の場合を足し、`Profile7` の偽の 2 つを真の命題に替える（`ParentBelowLower*.lean`）
- 段 B：`KeyLeRest` の新しい道筋と鎖の補題が決まってから
  - 親の鎖：`CrossLexPos IsPlain`、`IsClean`、`CopyQLower`、`CopyStepLow`
  - `StepInner` の部品：`LegOriginReach` と `LegGapTop` の代わり、`ViaRoot`、`LookupInner`、`LookupRoot`
  - `StartCopy`、`StartRoot` の部品：`BoundaryStepLower`、`BoundaryCutChain`、`PaLookup`、`X0Reach`、`GapTop` の代わり
  - すき間の 2 つの領域の部品：`CutRunLow`、`CutRunHigh`、`CutOriginReach`、`CutJumpTop`、`CutBump`、`CutLegLookup`
