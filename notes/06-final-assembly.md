# 最後の組み立て

2026-09-24。[04-official-design.md](04-official-design.md) §6.1、[05-large-value-audit.md](05-large-value-audit.md) の続き。

## 追記（2026-09-26、段 F）

- 下の組み立ての仮定のうち偽のものは、すべて弱めた命題に置き換えて証明した。最後の組み立ては [OmegaY/Official/Recon/FinalStageF.lean](../OmegaY/Official/Recon/FinalStageF.lean) の `wellFounded_step` で、仮定は無い。
- 経緯は [04-official-design.md](04-official-design.md) §6.1 の段 C〜F にある。下の §0 以降は段 C の時点の記録である。

## 0. 注意（見直し、2026-09-24）

- 9 個の仮定のうち 2 個が偽である。だから 9 個が同時に成り立つことは無く、`wellFounded_of_stageC` はまだ何も言っていない。
  - `TopStartLoRight`：反例 `(1,20,15,23,3,10,28,22)[1]`。Lean の反証は `Classification/Proofs/TopStartLoRightFalse.lean` の `not_topStartLoRight_of_check`。
  - `TopStartLoRoot`：反例 `(1,13,29,4,18,25,15)[1]`。`top-chain.cjs` の行 `TopStartLo [l=cr, plain, pa=o]` が FAIL を出す。
- 下の §3 の表で、この 2 行の「失敗 0」は無作為の標本がこの反例を引かなかっただけである。
- `PLAN.md` の `TopStart'` への直しが済んだら、組み立てをやり直す。

## 1. 要約

- 公式の ω-Y の展開の整礎性 `WellFounded Descent.Step` を、段 C の 9 個の開いた命題だけを仮定にして証明した。
  - ファイル：[OmegaY/Official/Recon/FinalAssembly.lean](../OmegaY/Official/Recon/FinalAssembly.lean)
  - 定理：`OmegaY.Official.Recon.FinalAssembly.wellFounded_of_stageC`
  - `leanman check` は exit 0。`#print axioms` は `[propext, Classical.choice, Quot.sound]` だけ。`sorry`、新しい公理、`native_decide` は無い。
- 仮定は次の 9 個で、これ以外の仮定は無い。

| 仮定 | 定義の場所 |
|---|---|
| `TopStepLoRoot` | `Classification/Proofs/TopChainMain.lean` |
| `TopStartLoRoot` | `Classification/Proofs/TopChainMain.lean` |
| `TopStartLoRight` | `Classification/Proofs/TopChainMain.lean` |
| `BoundaryChain` | `Classification/Proofs/ChainCorrStartRoot.lean` |
| `CutJumpRootRow` | `Classification/Proofs/Pkg3Jump.lean` |
| `CutRunTop` | `Classification/Proofs/Pkg3Run.lean` |
| `RootPass IsPlain` | `Recon/CrossPlainPosSim.lean` |
| `LexImg IsPlain` | `Recon/CrossPlainPosLex.lean` |
| `LexImg IsClean` | `Recon/CrossPlainPosLex.lean` |

- 行の法則の `LowerRowsCopy`、`LowerRowsBoundary` は、証明済みの `LRC*.lean`（未追跡）を import して使った。仮定には入れていない。

```lean
theorem wellFounded_of_stageC
    (hSR : TopChain.TopStepLoRoot)
    (hTR : TopChain.TopStartLoRoot)
    (hTRi : TopChain.TopStartLoRight)
    (hB : Classification.Proofs.ChainCorr.BoundaryChain)
    (hCJR : Classification.Proofs.ChainCorr.Pkg3.CutJumpRootRow)
    (hCRT : Classification.Proofs.ChainCorr.Pkg3.CutRunTop)
    (hRP : CrossPlainPos.RootPass IsPlain)
    (hLP : CrossPlainPos.LexImg IsPlain)
    (hLC : CrossPlainPos.LexImg IsClean) :
    WellFounded Descent.Step
```

## 2. 依存の木

【開】は段 C の開いた命題（上の 9 個）。【済】は証明済み。括弧の中は定理の名前。

- `WellFounded Step`（`ControlProof.wellFounded_of_block_keys`）
  - `ControlDominates`【済】（`controlDominates`）
  - `BlockReconstruction`（`blockReconstruction_of_reconstructionHolds`）
    - `ReconstructionHolds`（`reconstructionHolds_of_rowLaw_chain`）
      - `BottomHolds`【済】（`bottomHolds`）
      - `RowLawHolds`（`RowLaw.rowLawHolds_of_jumpLaw`）
        - `JumpLawHolds`【済】（`LRC.jumpLawHolds`）
          - `LowerRowsCopy`【済】（`LRC.lowerRowsCopy_holds`）
          - `LowerRowsBoundary`【済】（`LRC.lowerRowsBoundary_holds`）
      - `ChainHolds`（`chainHolds_of_three`）
        - `ParentBelowHolds`【済】（`LowerPB.StageB.parentBelowHolds`）
        - `CrossLexFor IsCut` ← `CutPredHolds`【済】（`CutPredMD.cutPredHolds`、`crossLexFor_cut`）
        - `CrossLexFor IsUpper`（`LowerChainRecon.crossLexFor_upper_of_lower`）
          - `Emitted`【済】（`CopyShape.Found.emitted`）
          - `TopStep`、`TopStart`（下の「共有の族」）
        - `CrossLexFor IsPlain`（`Pk4.crossLexFor_plain_pk4`）
          - `EmitBelow`、`PairAbove`、`PairOld`【済】（`Pk4*.lean`）
          - `TopStep`、`TopStart`
          - `RootPass IsPlain`【開】
          - `LexImg IsPlain`【開】
        - `CrossLexFor IsClean`（`Pk4.crossLexFor_clean_pk4`）
          - `EmitBelow`、`CleanFirst`、`PairAbove`、`PairOld`、`RootPass IsClean`【済】
          - `TopStep`、`TopStart`
          - `LexImg IsClean`【開】
  - `KeyLeRest`（`Pkg3.keyLeRest_pkg3`）
    - `TopStep`、`TopStart`
    - `NonTopStep`（`NonTop.nonTopStep_of_reconstruction`）← `BlockReconstruction`（上）
    - `StartRelNT`【済】（`NonTop.startRelNT`）
    - `StartRootNT`【済】（`NonTop.startRootNT`）
    - `StepCut`、`CutJump`、`CutStartCopyNT`、`CutStartRootNT`（`Pkg3.package3`）
      - `CutStartCopyNT`【済】（`cutStartCopyNT`）
      - `CutStartRootNT` ← `BoundaryChain`【開】（`cutStartRootNT_of_boundaryChain`）
      - `CutJump` ← `CutJumpRootRow`【開】と `CutJumpRun`（`cutJump_of_rows`）
        - `CutJumpRun` ← `CutRunTop`【開】（`cutJumpRun_of_top`）
      - `StepCut` ← `TopStep`、`NonTopStep`、`CutStartRootNT`、`CutJump`（`stepCut_of_lower`）
- 共有の族 `TopStep`、`TopStart`（`TopChain.topStep_topStart_of_parts`）
  - `TopStepLoRoot`【開】
  - `TopStepLoJump`（`TopChain.topStepLoJump_of_jumpLaw`）
    - `JumpLawHolds`【済】（上）
    - `LowExpCopy`【済】（`TopChain.lowExpCopy`）
  - `TopStartLoRoot`【開】
  - `TopStartLoRight`【開】

`NonTopStep` は `BlockReconstruction` から出す。`BlockReconstruction` は `KeyLeRest` を使わないので、循環しない。

## 3. 数値の確かめ

組み立ては新しい命題を足していない。9 個の仮定を、既存のハーネスでもう一度試した（2026-09-24、1 本ずつ、node のヒープは 2048 MB まで）。**どの行も失敗 0。**

| ハーネス | 命題（ハーネスの行） | K と B（81 列、n = 1,2,3、243 展開） | ほかの標本 |
|---|---|---:|---|
| `top-chain.cjs` | `TopStepLoRoot`（Stand と jump） | 1896 | 無作為・長さ 7 以下・値 30 以下（5365 展開）：32913 |
| `top-chain.cjs` | `TopStartLoRoot`（`TopStartLo [l=cr, …]`） | 3204 | 同じ無作為：56072 |
| `top-chain.cjs` | `TopStartLoRight`（`TopStartLo [l>cr, cut か pa=o]`） | 1551 | 同じ無作為：22762 |
| `pkg3-rows.cjs` | `CutJumpRootRow` | 290 | 無作為・長さ 7 以下・値 30 以下（5639 展開）：46359 |
| `pkg3-rows.cjs` | `CutRunTop` | 838 | 同じ無作為：8506 |
| `startcopy-root-parts.cjs` | `BoundaryChain` | 11136 | 無作為・長さ 6 以下・値 25 以下、n = 1,2（420 展開）：10111 |
| `cross-plain-pos-img.cjs` | `LexImg IsPlain` | 1470 | 長さ 6 以下・値 8 以下の全部（98301 展開）：171399。長さ 5 以下・値 10 以下の全部：60702。無作為・値 30 以下、n = 1：3036 |
| `cross-plain-pos-img.cjs` | `LexImg IsClean` | 513 | 同じ順に 7611、1975、46 |
| `cross-plain-pos-sim.cjs` | `RootPass IsPlain`（`EndCp plain cM =cr`） | 420 | 長さ 6 以下・値 12 以下の全部（727668 展開）：402 |

- K = [samples/known-counterexamples.json](../reference/official/samples/known-counterexamples.json)、B = [samples/legbelowtop-bad64.json](../reference/official/samples/legbelowtop-bad64.json)。
- `TopStartLo` の行は、`l = c_r` の行が `TopStartLoRoot`、`l > c_r` で cut（ハーネスの `clean!`）か `pa = o` の行が `TopStartLoRight` にあたる。`l > c_r`、cut でない、`pa < o` の行は証明済みの `topStartLoRightNC` の場合である。
- `RootPass` の場合（鎖の端 `c_M` が根の列 `c_r` にある）はまれで、長さ 6 以下・値 12 以下の全部でも 402 回だけだった。ハーネスの `EndCp plain cM =cr` は、ChainCp が見つけた `C` から `R` の鎖が `c_M` そのものに届くことを確かめる。`RootPass` の `C` は列 `c_r + w i` にあり、生の親の鎖は左へ進むので、どの `C` もこの `C` と同じく `c_M` より前にある。だからこの行で `RootPass` を確かめたことになる。
- 同じハーネスの `RootPassGen`（`Cp(Z, z)` のすべての組、`z` は `c_r` の節点）は偽の行を出す（K と B で 546 回）。これは `RootPass` より強い一般の形で、組み立てでは使っていない。
- `startcopy-root-parts.cjs` は K と B で、偽と分かっている `CopyOrder`（141 回）と `CutTop`（30 回）の失敗を出す。この 2 つは組み立てで使っていない。
- 長さ 6 以下・値 12 以下の合法な列すべて（05 の標本 A）での 9 個の結果は、各命題を作ったときの試験にある（`TopChainMain.lean`、`Pkg3Main.lean` の注記、05-large-value-audit.md）。今回は `RootPass` だけをこの範囲で試し直した。
- 時間切れで結果が出なかった試験：`startcopy-root-parts.cjs` の無作為 1500 列（値 20 以下、900 秒）、`cross-plain-pos-img.cjs` の n = 2 の無作為と長さ 6 以下・値 12 以下の全部、`cross-plain-pos-sim.cjs` の無作為・値 40 以下。

## 4. 残るもの

- 証明していないのは、上の 9 個の開いた命題だけである。
- 使っている未追跡のファイルは `Recon/LRC*.lean`（`LowerRowsCopy`、`LowerRowsBoundary` の証明。見直し中）と、このファイル `FinalAssembly.lean` だけである。
- 偽と分かっている命題（`LegBelowTop`、`StartLeg`、`StartCopy`、`StepInner`、`CopyOrder`、MA、`Profile7` の `Boundary` など）は、依存の木のどこにも無い。
