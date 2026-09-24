# PLAN — wy-wo-por

公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）。`ControlProof.wellFounded_of_block_keys` の残りの仮定は、出力の山の再構成 `BlockReconstruction` と `KeyLeRest` の 2 つ。

作業は依存の順に進める。葉が仮定にしてよいのは、証明済みの命題か、値の大きい列で真と確かめ済みで文面が決まった命題だけ（[notes/05-large-value-audit.md](notes/05-large-value-audit.md)）。段 A（土台と道筋）は済んだ。

- 段 B（検証の残り 1 つ）
  - 🤖 検証：行の法則 `LowerRowsCopy`、`LowerRowsBoundary` は証明した。これで `JumpLawHolds` は仮定なしで成り立つ（`LRC*.lean`）
- 段 C：最後に残る命題（文面は決まっている。互いに独立）
  - 🤖 継ぎ目（列 `x_0` の写しと根の列 `c_r`）：`TopStepLoRoot`、`TopStartLoRoot`、`BoundaryChain`
  - 🤖 `TopStartLoRight`（同じ行のすき間の写し）
  - 🤖 すき間の写しの行：`CutJumpRootRow`、`CutRunTop`
  - 🤖 親の鎖の plain と clean：`RootPass IsPlain`、`LexImg IsPlain`、`LexImg IsClean`
  - 🤖 組み立て：段 C の命題だけを仮定にした `WellFounded Step` の定理を 1 本にまとめる
