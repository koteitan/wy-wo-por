[English](README-en.md) | [Japanese](README.md)

# wy-wo-por：公式の ω-Y の整礎性（作業中）

公式の ω-Y 数列システムの展開が整礎であることを、Lean 4 で証明することを目指すリポジトリである。

- 公式の ω-Y の定義は、Naruyoko 氏のプログラム [Study and Expand Sequence(仮)](https://naruyoko.github.io/StudyAndExpandSequence/) の `expand` である（[notes/00-survey.md](notes/00-survey.md)）。
- Phyrion 氏が証明した weak-magma ω-Y は、公式の ω-Y とは別の数列システムである。その patterns of resemblance による再証明は [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por) にある。
- 二つの違いは、写した区画のすき間を埋める規則（magma）だけである。Phyrion 氏の証明の不変量のうち、写した辺の鍵の上界が公式の ω-Y では破れる（[notes/01-feasibility.md](notes/01-feasibility.md)）。

## 状態

作業中である。公式の ω-Y の停止性は、まだこのリポジトリの定理ではない。作業は branch `feature/official-expansion` で行う。
