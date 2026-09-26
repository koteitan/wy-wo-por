# PLAN — wy-wo-por

公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）。`ControlProof.wellFounded_of_block_keys` の残りの仮定は、出力の山の再構成 `BlockReconstruction` と `KeyLeRest` の 2 つ。

作業は依存の順に進める。葉が仮定にしてよいのは、証明済みの命題か、この PLAN に載っていて文面が決まった命題だけ。数値の試験は反例探しに限り、1 回 60 秒以内・小さい入力にする（値の大きい列の監査は [notes/05-large-value-audit.md](notes/05-large-value-audit.md)）。段 A〜C は済み、段 D は下の 5 つを残して済んだ。

- 段 D の残り（文面は決まっている）
  - 🤖 `TopStart'` の最後の部品：`RootValueIn`（`TSQRootValueX0.lean`、`M(s)` だけの命題）。ここから `TopStartPaOUp` が出る（`topStart'_of_cutParent_rootValueIn`）。小さい入力には当てはまる例が無く、数値の裏付けは弱い
  - `CrossLexFor IsUpper` の新しい帰着の残り（`CrossUpperQ.lean`、`crossLexFor_upper_of_chain`）
    - 🤖 `PaONoGapHi`、`CutRightTopHi`
    - 🤖 `SeamChainX`、`QRootRowGe`
- 🤖 組み立て：`wellFounded_of_stageD`（`CCLAssembly.lean`）と `wellFounded_of_stageC_QX`（`CrossUpperQAssembly.lean`）に、証明済みの `CutParentNT`、`StepRootTop`、`StartRootTopUp`、`TopStartCutRight` などを入れ、仮定を上の 5 つだけにした定理を作る
