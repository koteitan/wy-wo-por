/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighMarkerStationary.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualStationaryMarkerUpper
import OmegaY.Expansion.ActualNextHighestBoundary

/-!
# A marker whose source upper reaches the terminal threshold cannot rise

The actual marker target is strictly below its reference cap, which is at
most the terminal top. Every real source marker has a successor upper row.
Thus a high source upper leaves no room for a strictly raised effective row.
The auxiliary row-zero case follows from the actual zero reference query.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem EffectiveCopyOccurrence.stationary_of_marked_high_upper
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source sourceUpper : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    (hSourceUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height sourceUpper) :
    copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  let md := d.marker_data (Frame.ref source) hMarked
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hCurrent : md.current = F.cell source := Option.some.inj
    (md.current_at.symm.trans copy.read.source_at)
  have hCurrentRow : md.current.row = F.height source := congrArg Cell.row hCurrent
  have hReference : referenceAt copy.before references (F.height source) = .ok copy.read.outputCell.row :=
    copy.read.marked_reference hMarked
  have hTargetReference : referenceAt copy.before references (F.height source) = .ok md.targetCell.row := by
    have h := md.reference
    change referenceAt copy.before references md.current.row = .ok md.targetCell.row at h
    rw [hCurrentRow] at h
    exact h
  have hTargetRow : copy.read.outputCell.row = md.targetCell.row :=
    Except.ok.inj (hReference.symm.trans hTargetReference)
  by_cases hZero : source.2.val = 0
  · have hPhantom : md.current = phantom := Option.some.inj
      (md.current_at.symm.trans (by simpa only [Frame.ref, hZero] using d.source_valid.phantom))
    have hCurrentZero : md.current.row = 0 := congrArg Cell.row hPhantom
    have hTargetZero : md.targetCell.row = 0 := d.target_zero hMarked hCurrentZero
    exact hTargetRow.trans (hTargetZero.trans (hCurrentRow.symm.trans hCurrentZero).symm)
  · obtain ⟨hSuccessor, _⟩ := d.prepared_real_marker_successor hSources hMarked
      (show 0 < (Frame.ref source).index by change 0 < source.2.val; omega)
    have hUpperAt : d.sources[source.2.val + 1]? = some (F.cell sourceUpper) := by
      have hRead := d.frame_source_read hSources (congrArg Fin.val (Frame.upper_spec hSourceUpper).1)
      simpa only [(Frame.upper_spec hSourceUpper).2] using hRead
    have hUpperCell : md.upper = F.cell sourceUpper := Option.some.inj (md.upper_at.symm.trans hUpperAt)
    have hSourceSuccessor : F.height sourceUpper = Row.bump (F.height source) 0 :=
      (congrArg Cell.row hUpperCell).symm.trans
        (hSuccessor.trans (congrArg (fun row => Row.bump row 0) hCurrentRow))
    obtain ⟨degree, hTarget, hCap⟩ := copy.state.marker_caps_below_lastTop
      hLast d source.1.isLt (Frame.ref source) hMarked
    have hBelow : copy.read.outputCell.row < p.lastTop.row := by
      rw [hTargetRow]
      exact hTarget.trans_le hCap
    have hBefore : copy.read.outputCell.row < Row.bump (F.height source) 0 :=
      hBelow.trans_le (hHigh.trans_eq hSourceSuccessor)
    exact (Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero
      (Row.jump_le_of_lt_bump copy.read.source_row_le_output hBefore))).symm

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stationary_of_marked_high_upper
