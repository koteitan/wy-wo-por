# PLAN — wy-wo-por

- 公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）
  - `Classification.Bridge.wellFounded_of_block` の 3 つの仮定を証明する（[notes/04-official-design.md §6.1](notes/04-official-design.md)）
    - 🤖 出力の山の再構成 `ReconstructionHolds`：`n ≥ 1` の、`x₀` から右の列
    - 🤖 `ControlDominates`：入力の山の末列の、一番上より下の節点の鍵は制御の鍵より小さい
    - 🤖 `KeyLeRest`：写した列の出力の脚の原子の鍵は、元の脚の原子の鍵を写したもの以下
