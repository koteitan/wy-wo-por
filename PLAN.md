# PLAN — wy-wo-por

- 公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）
  - `ControlProof.wellFounded_of_block_keys` の残りの 2 つの仮定を証明する（[notes/04-official-design.md §6.1](notes/04-official-design.md)）
    - 出力の山の再構成 `ReconstructionHolds`（`Recon.reconstructionHolds_of_rowLaw_chain`）
      - 🤖 行の法則 `Recon.RowLawHolds`：新しい列で `row u⁺ = B (row u) (row π(u⁺))`
      - 親の鎖 `Recon.ChainHolds`（`Recon.chainHolds_of_split` で 2 つに分けた）
        - `ParentBelowHolds`：新しい列の実の節点 `u` の格納された親 `p` は `height p ≤ height u`
        - `CrossChainHolds`：候補 `Q u` が `p` の列にないとき、`Q u` から格納された親をたどって `p` の直前の節点 `c` に届き、`v(u) ≤ v(c)`
    - `KeyLeRest`：7 つの領域の補題に帰着した（`KeyRegions.keyLeRest_of_regions`）
      - 🤖 写した列の下の部分（行 < τ）で、尺度の根の鎖と元の山の鎖の対応の理論を作る（7 つの領域すべての土台）
      - 7 つの領域の補題 `RegionUpper`、`RegionPlainBoundary`、`RegionPlainInner`、`RegionCleanBoundary`、`RegionCleanInner`、`RegionCutBoundary`、`RegionCutInner` を証明する
