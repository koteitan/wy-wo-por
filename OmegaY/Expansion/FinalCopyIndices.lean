/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinalCopyIndices.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FinalHighDepth

/-!
# Actual surviving copy indices

The final size is calculated from the executed blocks and the program's
last-column removal. A successful occurrence read therefore supplies both
its survival bound and its block-count bound. No assertion concerns the
deleted last column, and positive copy counts are explicit.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The precise number of columns returned by a positive actual expansion. -/
theorem Preparation.expandDiagram_size
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    result.size = p.root.column +
      (copies + 1) * (p.reduced.size - 1 - p.root.column) := by
  obtain ⟨full, hFull, ready⟩ := p.blocks_total hLast copies
  have he : full.pop = result := Except.ok.inj
    ((p.expandDiagram_of_blocks hLast hCopies hFull).symm.trans hRun)
  rw [← he, Array.size_pop, ready.size_eq]
  omega

/-- A shifted bad-part source coordinate that actually survives the final
return cannot come from a block beyond the executed count. -/
theorem Preparation.block_le_of_final_column
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {block sourceColumn : Nat} (hRight : p.root.column < sourceColumn)
    (hSurvives : sourceColumn + block * (p.reduced.size - 1 - p.root.column) < result.size) :
    block ≤ copies := by
  have hSize := p.expandDiagram_size hLast hCopies hRun
  by_contra hNot
  have hBlock : copies + 1 ≤ block := by omega
  have hMul := Nat.mul_le_mul_right (p.reduced.size - 1 - p.root.column) hBlock
  omega

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

include copy

/-- The successful final read supplies an actual output-column bound. -/
theorem output_column_lt : copy.outputRef.column < result.size := by
  obtain ⟨column, hColumn, _⟩ := cellAt_ok_iff.mp copy.output_read
  exact (Array.getElem?_eq_some_iff.mp hColumn).1

/-- Survival of the shifted source coordinate follows from its occurrence,
independently of any claimed copy count or event correspondence. -/
theorem shifted_column_lt :
    source.1.val + block * (p.reduced.size - 1 - p.root.column) < result.size := by
  rw [← copy.source_column]
  exact copy.output_column_lt

/-- The actual state recorded by an occurrence locates its source strictly
to the right of the bad root. -/
theorem source_right : p.root.column < source.1.val := copy.state.next_lower

/-- No block-range input is needed for an occurrence read from the actual
final returned mountain. -/
theorem block_le (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) : block ≤ copies :=
  p.block_le_of_final_column hLast hCopies hRun copy.source_right copy.shifted_column_lt

/-- A typed output node identified with the real occurrence has precisely
the source/block coordinate, and that coordinate is in the final mountain. -/
theorem node_column {node : (Frame.ofMountain result).Node}
    (hRef : (Frame.ofMountain result).ref node = copy.outputRef) :
    node.1.val = source.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      source.1.val + block * (p.reduced.size - 1 - p.root.column) < result.size := by
  exact ⟨(congrArg Ref.column hRef).trans copy.source_column, copy.shifted_column_lt⟩

end EffectiveCopyOccurrence

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.expandDiagram_size
#print axioms OmegaY.Expansion.Preparation.block_le_of_final_column
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.output_column_lt
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.shifted_column_lt
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.source_right
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.block_le
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.node_column
