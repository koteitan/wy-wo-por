# PLAN — wy-wo-por

公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）。`ControlProof.wellFounded_of_block_keys` の残りの仮定は、出力の山の再構成 `BlockReconstruction` と `KeyLeRest` の 2 つ。

作業は依存の順に進める。葉が仮定にしてよいのは、証明済みの命題か、値の大きい列で真と確かめ済みで文面が決まった命題だけ（[notes/05-large-value-audit.md](notes/05-large-value-audit.md)）。段 A（土台と道筋）は済んだ。

- 段 B（作業中）
  - 🤖 検証：行の法則 `LowerRowsCopy`、`LowerRowsBoundary` は証明した。これで `JumpLawHolds` は仮定なしで成り立つ（`LRC*.lean`）
- 段 C：段 B の後に残る命題（段 B が終わってから組む）
  - 鎖の対応の残り：`TopStepLoRoot`、`TopStartLoRoot`、`TopStartLoRight`（列 `x_0` と `c_r` の継ぎ目、同じ行のすき間の写し。`LowerRowsCopy`、`LowerRowsBoundary` の仮定は外れる）
  - すき間の写しの残り：`BoundaryChain`、`CutJumpRootRow`、`CutRunTop`
  - 親の鎖の残り：`RootPass IsPlain`、`LexImg IsPlain`、`LexImg IsClean`
