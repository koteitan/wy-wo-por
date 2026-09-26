/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/HistoryPrefix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CopyRunHistory

/-!
# Earlier execution histories from a completed block history

The history records actual prior states and runs, with preservation into
the current mountain. Comparing their exact sizes recovers preservation
into each intermediate state too. This allows a local edge theorem that
needs a history to be applied at any previously copied source column.
-/

namespace OmegaY.Expansion

open Canonical

theorem PreservesColumns.between_prefixes {short long final : Mountain}
    (hShort : PreservesColumns short final) (hLong : PreservesColumns long final)
    (hSize : short.size ≤ long.size) : PreservesColumns short long := by
  intro column hColumn
  exact (hLong column (hColumn.trans_le hSize)).symm.trans (hShort column hColumn)

theorem CopyRunHistory.restrict {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref} {next : Nat} {ambient : Mountain}
    (history : CopyRunHistory p block start references next ambient)
    {earlier : Nat} {before : Mountain}
    (state : DynamicBlockState p block start references earlier before)
    (hEarlier : earlier ≤ next) (hPreserve : PreservesColumns before ambient) :
    CopyRunHistory p block start references earlier before := by
  intro sourceColumn hLower hUpper
  obtain ⟨oldBefore, column, oldState, hRun, hOldPreserve⟩ :=
    history sourceColumn hLower (hUpper.trans_le hEarlier)
  have hSize : (oldBefore.push column).size ≤ before.size := by
    have hOldSize := oldState.size_eq
    have hSize := state.size_eq
    simp only [Array.size_push]
    omega
  exact ⟨oldBefore, column, oldState, hRun, hOldPreserve.between_prefixes hPreserve hSize⟩

/-- The earlier state includes its complete earlier execution history;
it is derived from the actual recorded runs rather than assumed anew. -/
theorem CopyRunHistory.column_with_history {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref} {next : Nat} {ambient : Mountain}
    (history : CopyRunHistory p block start references next ambient)
    {sourceColumn : Nat} (hLower : p.root.column < sourceColumn) (hUpper : sourceColumn < next) :
    ∃ before column, ∃ _state : DynamicBlockState p block start references sourceColumn before,
      CopyRunHistory p block start references sourceColumn before ∧
      copyColumn before p.marked references sourceColumn
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column ∧
      PreservesColumns (before.push column) ambient ∧
      ambient[sourceColumn + block * (p.reduced.size - 1 - p.root.column)]? = some column := by
  obtain ⟨before, column, state, hRun, hPreserve, hRead⟩ := history.column_read hLower hUpper
  have hBeforePreserved : PreservesColumns before ambient :=
    (PreservesColumns.push before column).trans hPreserve
  exact ⟨before, column, state, history.restrict state hUpper.le hBeforePreserved,
    hRun, hPreserve, hRead⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.between_prefixes
#print axioms OmegaY.Expansion.CopyRunHistory.restrict
#print axioms OmegaY.Expansion.CopyRunHistory.column_with_history
