# PLAN — wy-wo-por

- 🤖 公式の展開の定義で ω-Y の整礎性を証明する（branch `feature/official-expansion`）
  - ✅ 公式の展開規則を完全に書き起こす（[notes/03-official-rule.md](notes/03-official-rule.md)、[reference/official/](reference/official/)）
  - ✅ 公式の展開を Lean で定義し、公式のプログラムの出力と照合する（[OmegaY/Official/](OmegaY/Official/)、[notes/03-official-rule.md §8](notes/03-official-rule.md)）
  - ✅ 写した辺の鍵の上界に代わる不変量を設計し、数値で試す（脚の原子の系、[notes/04-official-design.md](notes/04-official-design.md)、[reference/official/reserve.cjs](reference/official/reserve.cjs)）
  - 🤖 脚の原子の系と分類の判定を Lean で定義し、いくつかの展開で確かめる
  - 分類の補題を仮定にした整礎性の定理を Lean で示す
  - 分類の補題を証明する（[notes/04-official-design.md §6](notes/04-official-design.md)）
  - 次元の保存を公式の展開で証明する
