/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedBlockRun.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreparedBlockStep
import OmegaY.Expansion.ColumnPower

/-! The actual next copy supplies precisely the state needed by the next
source column. The argument is uniform in the source index, rather than
enumerating first, second, and later columns separately. -/

namespace OmegaY.Expansion

open Canonical

theorem PreparedBlockState.copy_next {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {next : Nat} {ambient : Mountain}
    (s : PreparedBlockState p references next ambient) (hLast : 1 < last)
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    (hNext : next < p.reduced.size) :
    ∃ column,
      copyColumn ambient p.marked references next (p.reduced.size - 1 - p.root.column)
        p.root.column = .ok column ∧
      FinishedColumn ambient column ∧ ColumnValid ambient ambient.size column ∧
      TopOne column ∧ ColumnPowerSteps column ∧ CopiedMarkerRows p references next column ∧
      PreparedBlockState p references (next + 1) (ambient.push column) := by
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast hMap hNext
  obtain ⟨column, hRun, hFinished, hValid, hTop, hPower, _, hSupport⟩ :=
    d.copyColumn_valid_power hParentPower hParentLow hNoPremature
  have hRows : CopiedMarkerRows p references next column := by
    intro marker hm current hCurrent target hTarget
    let md := d.marker_data marker hm
    have hCurrentAmbient : Canonical.cellAt ambient marker = .ok current :=
      p.cell_read_preserved s.base_preserved hCurrent
    have hDataRead : Canonical.cellAt ambient marker = .ok md.current :=
      cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns marker hm] using d.source_column,
        md.current_at⟩
    have hCurrentEq : current = md.current := Except.ok.inj (hCurrentAmbient.symm.trans hDataRead)
    subst current
    have hTargetAmbient : referenceAt ambient references md.current.row = .ok target :=
      (p.initial_referenceAt_preserved s.base_preserved hMap md.current.row).trans hTarget
    have hTargetEq : target = md.targetCell.row := Except.ok.inj (hTargetAmbient.symm.trans md.reference)
    subst target
    exact hSupport marker hm
  exact ⟨column, hRun, hFinished, hValid, hTop, hPower, hRows,
    s.push hNext hValid hPower hRows⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreparedBlockState.copy_next
