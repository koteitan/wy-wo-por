# PLAN — wy-wo-por

公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）。`ControlProof.wellFounded_of_block_keys` の残りの仮定は、出力の山の再構成と `KeyLeRest` の 2 つ。

作業は依存の順に進める。葉が仮定にしてよいのは、証明済みの命題か、値の大きい列で真と確かめ済みで文面が決まった命題だけ（[notes/05-large-value-audit.md](notes/05-large-value-audit.md)）。

- 段 1：土台と道筋（ほかの葉がこれを使う）
  - 写した列の形：`LowerPB.Emitted`、`CopyEmitted`、`CopyFirst`、MH と、偽の MA・`CopyOrder`・`NonCutOrder`・`CutBetween` に代わる真の命題（`CopyShape*.lean`、`LegRowMatchInner*.lean` の行の式）
  - `KeyLeRest` の道筋を作り直す：偽の `StepInner`、`StartCopy` を、失敗 0 の弱い形 `StepInnerSkip`、`StartCopySkip` に置き換え、要る命題の文面を決める（`ChainSkip*.lean`）
  - `LiftLegRight`、`LegRowMatchInner`、`StartJump` の証明の検証（`LiftLegRightProof.lean`、`LegRowMatchInner*.lean`）
- 段 2：土台の文面だけを仮定にする葉（今進めてよい）
  - 出力の山の再構成 `ReconstructionHolds`（`Recon.reconstructionHolds_of_rowLaw_chain`）
    - 行の法則 `JumpLawHolds`（`jumpLawHolds_of_lowerCases_left`）
      - `LowerRowsCopy` と `LowerRowsBoundary`
      - `LowerPairsLeft`（`LiftLegRight` は証明済み）
    - 親の鎖 `ChainHolds` の `CrossChainHolds`（`CutPredHolds` は証明済み）
      - `CrossLexPos IsPlain`、`CrossLexPos IsClean`
      - `SeamLastPosHolds`、`InnerHolds` の帰着の検証（`CrossUpperSim*.lean`、残りは `Emitted`、`CopyQLower`、`CopyStepLow`）
- 段 3：段 1 が終わってから始める葉
  - 写した列の形が決まってから
    - `LowerParentBelowHolds`：`caseLower` に脚が `ℓ < c_r` の場合を足し、`Profile7` の偽の 2 つを真の命題に替える（`ParentBelowLower*.lean`）
  - `KeyLeRest` の新しい道筋が決まってから
    - `StepInner` の部品：`LegOriginReach` と `LegGapTop` の代わり（`StepInnerLookup*.lean`）、`ViaRoot`、`LookupInner`、`LookupRoot`（`StepInnerClean*.lean`）
    - `StartCopy`、`StartRoot` の部品：`BoundaryStepLower`、`BoundaryCutChain`、`PaLookup`、`X0Reach`、`GapTop` の代わり（`StartRootParts*.lean`）
    - すき間の 2 つの領域の部品：`CutRunLow`、`CutRunHigh`、`CutOriginReach`、`CutJumpTop`、`CutBump`、`CutLegLookup`（`CutParts*.lean`）
