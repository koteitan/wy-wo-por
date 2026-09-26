/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualAllUpperLift.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentAdvance

/-!+# Actual lifted upper rows including marked lower sources

The marked branch starts at the actual effective target, after all fill.
Its executed upper is the target successor. The prepared source successor
law makes this precisely the same contour lift formula as for unmarked
lowers. A marked source upper is not assumed to be its effective copy.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source upper : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

theorem upper_lift_read_all (hLast : 1 < last) (hReal : Real source)
    (hUpper : (Frame.ofMountain p.reduced).upper source = some upper) :
    ∃ cell, Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok cell ∧
      cell.row = copy.contourCut ((Frame.ofMountain p.reduced).height upper) := by
  by_cases hIndex : source.2.val ∈ (p.marked[source.1.val]?.getD []).map Ref.index
  · obtain ⟨marker, hm, hi⟩ := List.mem_map.mp hIndex
    have hMarker : marker = Frame.ref source := congrArg₂ Ref.mk (copy.data.marker_columns marker hm) hi
    have hMarked : BucketMem p.marked source.1.val (Frame.ref source) := hMarker ▸ hm
    have hCurrentIndex := copy.read.marker_index_of_marked hMarked
    let d := copy.data
    let md := d.marker_data copy.read.marker copy.read.marker_mem
    have hSource : p.reduced[source.1.val]? = some d.sources :=
      (copy.state.base_ambient _ source.1.isLt).symm.trans d.source_column
    have hCurrent : md.current = (Frame.ofMountain p.reduced).cell source := Option.some.inj
      (md.current_at.symm.trans (by simpa only [hCurrentIndex] using copy.read.source_at))
    have hUpperAt : d.sources[copy.read.marker.index + 1]? =
        some ((Frame.ofMountain p.reduced).cell upper) := by
      have hRead := d.frame_source_read hSource (congrArg Fin.val (Frame.upper_spec hUpper).1)
      simpa only [hCurrentIndex, (Frame.upper_spec hUpper).2] using hRead
    have hUpperCell : md.upper = (Frame.ofMountain p.reduced).cell upper :=
      Option.some.inj (md.upper_at.symm.trans hUpperAt)
    have hReadRow : copy.read.outputCell.row = md.targetCell.row := by
      have hRow := copy.read.output_row
      rw [hCurrent, Row.lift_at_root] at hRow
      exact hRow
    obtain ⟨hSuccessor, hRoot⟩ := d.prepared_real_marker_successor hSource copy.read.marker_mem
      (by simpa only [hCurrentIndex, Frame.Real] using hReal)
    obtain ⟨hNoPremature, hPP, hPL⟩ := copy.state.column_data_parent_inputs hLast source.1.isLt d
    obtain ⟨cell, hRead, hRow, _⟩ := d.effective_marker_upper hPP hPL hNoPremature copy.read.copy_run
      copy.read.marker_mem hSuccessor hRoot copy.read.output_at hReadRow
    have hResult : result[copy.before.size]? = some copy.column := copy.preserved.column_read (by simp)
    refine ⟨cell, cellAt_ok_iff.mpr ⟨copy.column, hResult, hRead⟩, ?_⟩
    change cell.row = Row.lift md.current.row md.targetCell.row ((Frame.ofMountain p.reduced).height upper)
    have hOldUpper : (Frame.ofMountain p.reduced).height upper = Row.bump md.current.row 0 :=
      (congrArg Cell.row hUpperCell).symm.trans hSuccessor
    rw [hOldUpper, Row.lift_bump le_rfl, Row.lift_at_root]
    exact hRow
  · exact copy.upper_lift_read hLast hIndex hUpper

/-- If the source upper is unmarked, it is the actual immediate upper of
the effective lower at the level of rows, including marked lower sources. -/
theorem effective_upper_row_all (hLast : 1 < last) (hReal : Real source)
    (upperCopy : EffectiveCopyOccurrence p block start references upper result)
    (hUpper : (Frame.ofMountain p.reduced).upper source = some upper)
    (hUnmarked : upper.2.val ∉ (p.marked[upper.1.val]?.getD []).map Ref.index) :
    ∃ cell, Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok cell ∧
      cell.row = upperCopy.read.outputCell.row := by
  obtain ⟨cell, hRead, hRow⟩ := copy.upper_lift_read_all hLast hReal hUpper
  refine ⟨cell, hRead, ?_⟩
  rw [hRow, copy.contourCut_eq_of_unmarked_upper upperCopy hUpper hUnmarked, upperCopy.read.output_row]
  rfl

/-- At a following source marker, the old segment's lift has reset to
the physical source row. This is an actual cap consequence and does not
identify the physical marker with its possibly raised effective target. -/
theorem contourCut_fixed_at_marked_upper
    (hUpper : (Frame.ofMountain p.reduced).upper source = some upper)
    (hMarked : BucketMem p.marked upper.1.val (Frame.ref upper)) :
    copy.contourCut ((Frame.ofMountain p.reduced).height upper) =
      (Frame.ofMountain p.reduced).height upper := by
  let d := copy.data
  let md := d.marker_data copy.read.marker copy.read.marker_mem
  have hc : upper.1.val = source.1.val := congrArg Fin.val (Frame.upper_spec hUpper).1
  have hi := (Frame.upper_spec hUpper).2
  have hm : Frame.ref upper ∈ d.bucket := by
    change Frame.ref upper ∈ p.marked[source.1.val]?.getD []
    simpa only [BucketMem, hc] using hMarked
  let nextMd := d.marker_data (Frame.ref upper) hm
  have hSource : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient _ source.1.isLt).symm.trans d.source_column
  have hRead := d.frame_source_read hSource hc
  have hCurrent : nextMd.current = (Frame.ofMountain p.reduced).cell upper :=
    Option.some.inj (nextMd.current_at.symm.trans hRead)
  have hAfter : copy.read.marker.index < (Frame.ref upper).index := by
    have hb := copy.read.marker_before
    change copy.read.marker.index < upper.2.val
    omega
  obtain ⟨degree, hTarget, hCap⟩ := d.reference_caps copy.read.marker copy.read.marker_mem
    (Frame.ref upper) hm hAfter
  change Row.lift md.current.row md.targetCell.row ((Frame.ofMountain p.reduced).height upper) = _
  apply Row.lift_eq_of_ge_cap md.target_lower hTarget
  exact hCap.trans_eq (congrArg Cell.row hCurrent)

theorem upper_physical_row_of_marked (hLast : 1 < last) (hReal : Real source)
    (hUpper : (Frame.ofMountain p.reduced).upper source = some upper)
    (hMarked : BucketMem p.marked upper.1.val (Frame.ref upper)) :
    ∃ cell, Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok cell ∧
      cell.row = (Frame.ofMountain p.reduced).height upper := by
  obtain ⟨cell, hRead, hRow⟩ := copy.upper_lift_read_all hLast hReal hUpper
  exact ⟨cell, hRead, hRow.trans (copy.contourCut_fixed_at_marked_upper hUpper hMarked)⟩

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.upper_lift_read_all
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.effective_upper_row_all
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.contourCut_fixed_at_marked_upper
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.upper_physical_row_of_marked
