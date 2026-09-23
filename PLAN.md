# PLAN — wy-wo-por

- 公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）
  - `ControlProof.wellFounded_of_block_keys` の残りの 2 つの仮定を証明する（[notes/04-official-design.md §6.1](notes/04-official-design.md)）
    - 出力の山の再構成 `ReconstructionHolds`（`Recon.reconstructionHolds_of_rowLaw_chain`）
      - 行の法則 `Recon.RowLawHolds`（上の行が下の行の bump になることは証明済み、`RowLaw.bumpChainHolds`）
        - 🤖 `RowLaw.JumpLawHolds`：`row u⁺ = bump (row u) e` なら、親の行について `jump (row u) (row π(u⁺)) = e`
      - 親の鎖 `Recon.ChainHolds`（`Recon.chainHolds_of_split` で 2 つに分けた）
        - `ParentBelowHolds`（上の部分と、bump の指数が 0 のときは証明済み。`ParentBelow.parentBelowHolds_of_lower`）
          - 🤖 `LowerParentBelowHolds`：`u` が τ より下で、`row u⁺ = bump (row u) e`（`e ≥ 1`）のとき、親の列は `B_{e+1}(row u)` の中で `row u` より上に節点を持たない
        - `CrossChainHolds`：値を使わない比較 `Lex` に言い換え、上の節点の出所の種類で分けた（`CrossKinds.crossChainHolds_of_three`）
          - 🤖 `CutPredHolds`：cut の emit の直前は、いつも同じ出所の clean の emit で、`leftColumn` も同じ
          - 🤖 `CrossLexFor IsPlain` と `CrossLexFor IsClean`
          - 🤖 `CrossLexFor IsUpper`
    - `KeyLeRest`：7 つの領域の補題に帰着した（`KeyRegions.keyLeRest_of_regions`）
      - すき間の写しでない 5 つの領域は、鎖の対応の 5 つの命題に帰着した（`ChainCorrRegions.wellFounded_of_chains`）
        - 🤖 `StepInner`：元の山の 1 歩に、出力の鎖の歩みが対応する
        - 🤖 `StartLeg` と `StartJump`：脚の列は `cr` 以上、出発の jump は元以下
        - 🤖 `StartCopy` と `StartRoot`：出発の節点の対応（脚が `cr` より右のときと、`cr` のとき）
      - 🤖 すき間の写しの 2 つの領域 `RegionCutBoundary`、`RegionCutInner` を証明する（鍵は辞書式でだけ小さいので、成分ごとの道具を厳密な版に広げる）
