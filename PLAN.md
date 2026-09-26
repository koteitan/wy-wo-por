# PLAN — wy-wo-por

公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）。`ControlProof.wellFounded_of_block_keys` の残りの仮定は、出力の山の再構成 `BlockReconstruction` と `KeyLeRest` の 2 つ。

作業は依存の順に進める。葉が仮定にしてよいのは、証明済みの命題か、この PLAN に載っていて文面が決まった命題だけ。数値の試験は反例探しに限り、1 回 60 秒以内・小さい入力にする（値の大きい列の監査は [notes/05-large-value-audit.md](notes/05-large-value-audit.md)）。段 A〜D は済み。段 E の結果は下のとおり。

- 段 E で、帰着の 2 か所が偽の命題に頼っていると分かった（目標の命題 ChainHolds などは、どちらの反例でも成り立つ）
  - `TopStart'` の作り直し：`RootValueIn` は偽（反例 `(1,4,18,56,18)`、`TSQRootValueInFalse.lean`）。`TopStartPaOUp` と `TopStart'` の強い条項（HasAboveLow のとき Stand pe pa）も数値では偽。`TopStart'` をさらに弱め、`KeyLeRest` と親の鎖の帰着を作り直す
  - `CrossLexFor IsUpper` の作り直し：`PaONoGapHi` は偽（反例 `(1,21,5,20,59,20)`、`CrossUpperQHiFalse.lean`）。`CopyQLowerW` も同じ入力で数値では偽。内側の場合の `TopCopy` を `Rel`（CopyNode ∨ TopNode）に弱めて帰着を作り直す
- 組み立て：`FinalStageE.lean` は 5 つの命題を仮定にした整礎性を示すが、うち 2 つが偽なので中身が無い。`TopStep`（`topStep_final`）、`SeamChainX`、`QRootRowGe`（`SCXMain.lean`）、`CutRightTopHi`（`CrossUpperQHiCut.lean`）は仮定なしで証明済み
