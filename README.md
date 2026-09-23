[English](README-en.md) | [Japanese](README.md)

# wy-wo-por：公式の ω-Y の整礎性（作業中）

公式の ω-Y 数列システムの展開が整礎であることを、Lean 4 で証明することを目指すリポジトリである。

- 公式の ω-Y の定義は、Naruyoko 氏のプログラム [Study and Expand Sequence(仮)](https://naruyoko.github.io/StudyAndExpandSequence/) の `expand` である（[notes/00-survey.md](notes/00-survey.md)）。
- Phyrion 氏が証明した weak-magma ω-Y は、公式の ω-Y とは別の数列システムである。その patterns of resemblance による再証明は [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por) にある。
- 二つの違いは、写した区画のすき間を埋める規則（magma）と、どの節点を持ち上げるかの規則である。Phyrion 氏の証明の不変量のうち、写した辺の鍵の上界が公式の ω-Y では破れる（[notes/01-feasibility.md](notes/01-feasibility.md)）。
- 公式の展開規則の書き起こしと、公式のプログラムとの差分試験は [notes/03-official-rule.md](notes/03-official-rule.md) にある。自前の実装は [reference/official/](reference/official/) にある。
- 公式の展開の Lean の定義は [OmegaY/Official/Build.lean](OmegaY/Official/Build.lean) の `OmegaY.Official.expand` である。公式のプログラムの出力 474 個との照合は [OmegaY/Official/Check.lean](OmegaY/Official/Check.lean) にある。
- 証明の設計は [notes/04-official-design.md](notes/04-official-design.md) にある。Phyrion 氏の反映の定理はそのまま使い、表現の原子を「節点ごとの脚の原子」に替える。この原子の系で、反映に要る分類が試したすべての展開で成り立った（[reference/official/reserve.cjs](reference/official/reserve.cjs)）。Lean でも、原子の系と分類の判定を [OmegaY/Official/Reserve.lean](OmegaY/Official/Reserve.lean) で定義し、474 個の展開で判定が真になることを [OmegaY/Official/ReserveCheck.lean](OmegaY/Official/ReserveCheck.lean) で確かめた。[OmegaY/Official/Reconstruction.lean](OmegaY/Official/Reconstruction.lean) で、次の 2 つを仮定にした整礎性の定理 `OmegaY.Official.Reconstruction.wellFounded_of_parts` を証明した：出力の山の次数が $`D`$ 以下であること、出力の脚の原子がすべて分類されること（`DegreeAndAtomsHold`）。次数のほうは、出力の山の再構成（`ReconstructionHolds`）を仮定にして [OmegaY/Official/Dimension.lean](OmegaY/Official/Dimension.lean) で証明した。出力の長さと、出力の山が作れることは証明済みである。最初に仮定にした `Descent.ClassificationHolds` は空の列のせいで偽だった（`not_classificationHolds`）ので、空でない列に限った形に直した。

## 状態

作業中である。公式の ω-Y の停止性は、まだこのリポジトリの定理ではない。証明されているのは、未解決の 2 つの補題（出力の山の再構成 `ReconstructionHolds`、脚の原子の分類）を仮定にした整礎性である。分類は、さらに 2 つの命題（`ControlDominates`、`KeyLeRest`）に帰着した。つまり、残る未解決の命題は 3 つである（`Classification.Bridge.wellFounded_of_block`）。作業は branch `feature/official-expansion` で行う。
