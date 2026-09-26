[← Back](README.md) | [English](rule.md) | [Japanese](../rule.md)

# Working rules for study/

## Files

- The Japanese text is in `study/*.md` and the English translation in `study/en/*.md`. The translation has the same sections, tables and formulas as the Japanese text.
- The first line of each file is a navigation line. A Japanese note has `[← Back](README.md) | [English](en/FILE) | [Japanese](FILE)`, an English note has `[← Back](README.md) | [English](FILE) | [Japanese](../FILE)`.

## Order

- Arrange the material so that it can be read from the top. Do not use a term that no earlier section or note has explained. Do not use a term before the section or note that defines it.
- Start each note with a "Prerequisites" table that says which terms of earlier notes it uses.
- End each note with a table "Where this repository uses it" that lists README sections and notes/ sections.

## Terms

- Define every term before its first use.
- Do not make a new term when an existing expression suffices, so that the reader has fewer terms to remember. Give a name only to what is used many times.
- Write "parent" (親), never "father" (父).
- Give each term one meaning only. The following terms are used only in these meanings.
  - stage: a stage (top, key) of the recursion of the relation $`R`$.
  - height: the height of a structure (the $`\gamma`$ of the domain $`\{x \mid x \lt \gamma\}`$).
  - degree: the degree of a row (an ordinal below $`\omega^\omega`$).
  - jump: the jump of two rows. For an edge of a mountain write "the jump of the edge", not "the degree".
- The label of the root column is "the root label", not "the root index".

## Content

- Write the definition first, then a small example.
- Give a proof or a proof outline for each theorem. Say so when something is not proved here.
- Do not write about the formalization (the proof assistant): no names, files or code of the formalization, and no remarks about it. Give theorems and objects a mathematical name or a number ("Property 2", "Lemma 1 of §8", and so on).
- Write structures as $`(A; P_1, \ldots, P_k)`$. This notation is explained where it is first used, in [03](03-sigma1-elementary.md) §1.
- Compute example values with Python, or by following the definitions by hand. Do not compute them with the proof assistant. Say which of the two was used. One run of a computer program takes at most 60 seconds.
- A numerical test is not a proof. When reporting a test, state its range (length of sequences, bound on the values, number of copies).

## Sentences

- Write short sentences, one point per sentence.
- Do not use metaphors. Use literal words.
- Write in formulas what can be written in formulas.

## Formulas (so that GitHub renders them)

- Write inline math as `` $`...`$ ``.
- Write display math in a ```` ```math ```` fence.
- In inline math write the inequality signs as `\lt` and `\gt`.
- Break rows with `\cr`. Do not use two backslashes.
- Inside a list item, do not use a math fence. Use inline math only.
- Do not write `|` in math inside a table cell. Use `\mid`.

## References to other projects

- Refer to other projects by their public GitHub URL. Do not write local paths.
- Mathematics shared with the 1-Y study ([study/ of koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por/tree/main/study)) and the weak-magma ω-Y study ([study/ of koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por/tree/main/study)) is written in the same order. Their text may be copied and adapted. Definitions and symbols follow this repository.
