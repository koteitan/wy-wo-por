/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/EffectiveOccurrenceUnique.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveParent

/-!
# Coherence of independently constructed effective occurrences

Different parent-edge proofs may reconstruct a source occurrence from
different input certificates. The actual marker maximum, block reference
query and final preserved column force the same output reference and cell.
Thus existential endpoint constructions can form one coherent copied map.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (left right : EffectiveCopyOccurrence p block start references source result)

theorem marker_unique : left.read.marker = right.read.marker := by
  have hIndex : left.read.marker.index = right.read.marker.index := by
    rcases lt_trichotomy left.read.marker.index right.read.marker.index with hLt | hEq | hGt
    · exact False.elim (left.read.no_between right.read.marker.index hLt right.read.marker_before
        (List.mem_map.mpr ⟨right.read.marker, right.read.marker_mem, rfl⟩))
    · exact hEq
    · exact False.elim (right.read.no_between left.read.marker.index hGt left.read.marker_before
        (List.mem_map.mpr ⟨left.read.marker, left.read.marker_mem, rfl⟩))
  have hColumn : left.read.marker.column = right.read.marker.column :=
    (left.data.marker_columns left.read.marker left.read.marker_mem).trans
      (right.data.marker_columns right.read.marker right.read.marker_mem).symm
  cases hl : left.read.marker with
  | mk lc li =>
    cases hr : right.read.marker with
    | mk rc ri =>
      simp only [hl, hr, Ref.mk.injEq] at hColumn hIndex ⊢
      exact ⟨hColumn, hIndex⟩

theorem effective_row_unique : left.read.outputCell.row = right.read.outputCell.row := by
  have hSources : left.data.sources = right.data.sources := by
    have hLeft : p.reduced[source.1.val]? = some left.data.sources :=
      (left.state.base_ambient source.1.val source.1.isLt).symm.trans left.data.source_column
    have hRight : p.reduced[source.1.val]? = some right.data.sources :=
      (right.state.base_ambient source.1.val source.1.isLt).symm.trans right.data.source_column
    exact Option.some.inj (hLeft.symm.trans hRight)
  let lm := left.data.marker_data left.read.marker left.read.marker_mem
  let rm := right.data.marker_data right.read.marker right.read.marker_mem
  have hCurrent : lm.current = rm.current := Option.some.inj
    (lm.current_at.symm.trans (by rw [hSources, left.marker_unique right]; exact rm.current_at))
  have hQueryL : referenceAt start references lm.current.row = .ok lm.targetCell.row :=
    (left.state.referenceAt_preserved lm.current.row).symm.trans lm.reference
  have hQueryR : referenceAt start references rm.current.row = .ok rm.targetCell.row :=
    (right.state.referenceAt_preserved rm.current.row).symm.trans rm.reference
  have hTarget : lm.targetCell.row = rm.targetCell.row := Except.ok.inj
    (hQueryL.symm.trans (by rw [hCurrent]; exact hQueryR))
  rw [left.read.output_row, right.read.output_row]
  change Row.lift lm.current.row lm.targetCell.row _ = Row.lift rm.current.row rm.targetCell.row _
  rw [hCurrent, hTarget]

/-- No final-mountain normality or validity is needed: actual finished-column
validity and whole-column preservation already force endpoint identity. -/
theorem unique : left.outputRef = right.outputRef ∧ left.read.outputCell = right.read.outputCell := by
  have hColumnIndex : left.before.size = right.before.size :=
    left.data.destination.symm.trans right.data.destination
  have hLeftRead : result[left.before.size]? = some left.column :=
    left.preserved.column_read (by simp)
  have hRightRead : result[right.before.size]? = some right.column :=
    right.preserved.column_read (by simp)
  have hColumns : left.column = right.column := Option.some.inj
    (hLeftRead.symm.trans (by rw [hColumnIndex]; exact hRightRead))
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := left.data.copyColumn_valid
  have hActualEq : actual = left.column := Except.ok.inj (hActual.symm.trans left.read.copy_run)
  subst actual
  have hRightAt : left.column[right.read.outputIndex]? = some right.read.outputCell := by
    rw [hColumns]
    exact right.read.output_at
  have hIndex : left.read.outputIndex = right.read.outputIndex :=
    column_read_index_eq_of_row hValid left.read.output_at hRightAt (left.effective_row_unique right)
  have hRefs : left.outputRef = right.outputRef := by
    change (⟨left.before.size, left.read.outputIndex⟩ : Ref) = ⟨right.before.size, right.read.outputIndex⟩
    rw [hColumnIndex, hIndex]
  exact ⟨hRefs, Except.ok.inj (left.output_read.symm.trans (hRefs ▸ right.output_read))⟩

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.marker_unique
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.effective_row_unique
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.unique
