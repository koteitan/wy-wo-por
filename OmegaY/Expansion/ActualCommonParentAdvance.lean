/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonParentAdvance.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSharedContourCutAll
import OmegaY.Expansion.ActualEffectiveOrder

/-!+# A true shared event after common parents split

An unmarked immediate source upper stays in the preceding occurrence's
actual controlling-marker segment. If two old source frontiers share a
parent, their actual copied immediate uppers have a common row. Provided
the old and new source nodes are unmarked, the new effective occurrences
have precisely that row. They therefore share an actual target event even
when their current numerical parents are different.

This covers a genuine next-event branch of the first-difference problem;
crossing a marked new node can separate physical and effective endpoints
and is not silently included.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source upper : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)
  (upperCopy : EffectiveCopyOccurrence p block start references upper result)

/-- No marked source index can intervene between adjacent source nodes
when the upper itself is unmarked. Both marker identities come from the
maximal preceding-marker fields of actual execution records. -/
theorem marker_eq_of_unmarked_upper
    (hUpper : (Frame.ofMountain p.reduced).upper source = some upper)
    (hUnmarked : upper.2.val ∉ (p.marked[upper.1.val]?.getD []).map Ref.index) :
    copy.read.marker = upperCopy.read.marker := by
  have hc : upper.1.val = source.1.val := congrArg Fin.val (Frame.upper_spec hUpper).1
  have hi : upper.2.val = source.2.val + 1 := (Frame.upper_spec hUpper).2
  have hLowMember : copy.read.marker.index ∈ (p.marked[upper.1.val]?.getD []).map Ref.index := by
    rw [hc]
    exact List.mem_map.mpr ⟨copy.read.marker, copy.read.marker_mem, rfl⟩
  have hHighMember : upperCopy.read.marker.index ∈ (p.marked[source.1.val]?.getD []).map Ref.index := by
    rw [← hc]
    exact List.mem_map.mpr ⟨upperCopy.read.marker, upperCopy.read.marker_mem, rfl⟩
  have hHighBefore : upperCopy.read.marker.index ≤ source.2.val := by
    have hBefore := upperCopy.read.marker_before
    have hNe : upperCopy.read.marker.index ≠ upper.2.val := by
      intro he
      exact hUnmarked (he ▸ List.mem_map.mpr ⟨upperCopy.read.marker, upperCopy.read.marker_mem, rfl⟩)
    omega
  have hIndex : copy.read.marker.index = upperCopy.read.marker.index := by
    rcases lt_trichotomy copy.read.marker.index upperCopy.read.marker.index with hlt | he | hgt
    · exact False.elim (copy.read.no_between _ hlt hHighBefore hHighMember)
    · exact he
    · exact False.elim (upperCopy.read.no_between _ hgt
        (by have := copy.read.marker_before; omega) hLowMember)
  have hColumn : copy.read.marker.column = upperCopy.read.marker.column :=
    (copy.data.marker_columns _ copy.read.marker_mem).trans
      (hc.symm.trans (upperCopy.data.marker_columns _ upperCopy.read.marker_mem).symm)
  exact congrArg₂ Ref.mk hColumn hIndex

/-- The two independently reconstructed occurrences use the same actual
root row and reference query, hence the same entire contour cut map. -/
theorem contourCut_eq_of_unmarked_upper
    (hUpper : (Frame.ofMountain p.reduced).upper source = some upper)
    (hUnmarked : upper.2.val ∉ (p.marked[upper.1.val]?.getD []).map Ref.index)
    (cut : Row) : copy.contourCut cut = upperCopy.contourCut cut := by
  have hc : upper.1.val = source.1.val := congrArg Fin.val (Frame.upper_spec hUpper).1
  have hMarker := copy.marker_eq_of_unmarked_upper upperCopy hUpper hUnmarked
  have hSources : copy.data.sources = upperCopy.data.sources := by
    have hLow : p.reduced[source.1.val]? = some copy.data.sources :=
      (copy.state.base_ambient source.1.val source.1.isLt).symm.trans copy.data.source_column
    have hHigh : p.reduced[upper.1.val]? = some upperCopy.data.sources :=
      (upperCopy.state.base_ambient upper.1.val upper.1.isLt).symm.trans upperCopy.data.source_column
    exact Option.some.inj (hLow.symm.trans (by simpa only [hc] using hHigh))
  let lm := copy.data.marker_data copy.read.marker copy.read.marker_mem
  let um := upperCopy.data.marker_data upperCopy.read.marker upperCopy.read.marker_mem
  have hCurrent : lm.current = um.current := Option.some.inj
    (lm.current_at.symm.trans (by rw [hSources, hMarker]; exact um.current_at))
  have hLowQuery : referenceAt start references lm.current.row = .ok lm.targetCell.row :=
    (copy.state.referenceAt_preserved _).symm.trans lm.reference
  have hHighQuery : referenceAt start references um.current.row = .ok um.targetCell.row :=
    (upperCopy.state.referenceAt_preserved _).symm.trans um.reference
  have hTarget : lm.targetCell.row = um.targetCell.row := Except.ok.inj
    (hLowQuery.symm.trans (by rw [hCurrent]; exact hHighQuery))
  change Row.lift lm.current.row lm.targetCell.row cut = Row.lift um.current.row um.targetCell.row cut
  rw [hCurrent, hTarget]

/-- The real immediate upper of an unmarked copied lower has the same
row as the real effective upper-source occurrence. No upper-parent
identity, target adjacency, or target numerical recognition is assumed. -/
theorem effective_upper_row (hLast : 1 < last)
    (hLowerUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    (hUpper : (Frame.ofMountain p.reduced).upper source = some upper)
    (hUpperUnmarked : upper.2.val ∉ (p.marked[upper.1.val]?.getD []).map Ref.index) :
    ∃ cell, Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok cell ∧
      cell.row = upperCopy.read.outputCell.row := by
  obtain ⟨cell, hRead, hRow⟩ := copy.upper_lift_read hLast hLowerUnmarked hUpper
  refine ⟨cell, hRead, ?_⟩
  rw [hRow, upperCopy.read.output_row]
  exact copy.contourCut_eq_of_unmarked_upper upperCopy hUpper hUpperUnmarked _

end EffectiveCopyOccurrence

/-- The target event at the next effective rows is obtained from actual
row membership. The new source nodes' P values are entirely unrestricted.
Only the previous source frontiers have a common designated parent. -/
theorem common_parent_advance_event
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z nextU nextZ parent : (Frame.ofMountain p.reduced).Node}
    (uCopy : EffectiveCopyOccurrence p block start references u result)
    (zCopy : EffectiveCopyOccurrence p block start references z result)
    (nextUCopy : EffectiveCopyOccurrence p block start references nextU result)
    (nextZCopy : EffectiveCopyOccurrence p block start references nextZ result)
    (hLast : 1 < last) (hValid : MountainValid result)
    (hUUnmarked : u.2.val ∉ (p.marked[u.1.val]?.getD []).map Ref.index)
    (hZUnmarked : z.2.val ∉ (p.marked[z.1.val]?.getD []).map Ref.index)
    (hNextUUnmarked : nextU.2.val ∉ (p.marked[nextU.1.val]?.getD []).map Ref.index)
    (hNextZUnmarked : nextZ.2.val ∉ (p.marked[nextZ.1.val]?.getD []).map Ref.index)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUUpper : (Frame.ofMountain p.reduced).upper u = some nextU)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some nextZ)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    ∃ (actualU actualZ : (Frame.ofMountain result).Node) (event : Nat),
      Frame.ref actualU = nextUCopy.outputRef ∧ Frame.ref actualZ = nextZCopy.outputRef ∧
      (Frame.ofMountain result).cell actualU = nextUCopy.read.outputCell ∧
      (Frame.ofMountain result).cell actualZ = nextZCopy.read.outputCell ∧
      (Frame.ofMountain result).height actualU = (Frame.ofMountain result).height actualZ ∧
      event ≤ (Frame.ofMountain result).lastEvent ∧
      (Frame.ofMountain result).eventCut event = (Frame.ofMountain result).height actualU ∧
      eventFrontier hValid.toOrdered event actualU.1 = actualU ∧
      eventFrontier hValid.toOrdered event actualZ.1 = actualZ := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hu := frontierAt_spec hNormal.toOrdered hCut u.1
  have hz := frontierAt_spec hNormal.toOrdered hCut z.1
  have huBelow : F.height u ≤ cut := hUFront ▸ hu.2.2.1
  have hzBelow : F.height z ≤ cut := hZFront ▸ hz.2.2.1
  have huAbove := hu.2.2.2.2 nextU (hUFront.symm ▸ hUUpper)
  have hzAbove := hz.2.2.2.2 nextZ (hZFront.symm ▸ hZUpper)
  have hSourceSame : F.height nextU = F.height nextZ := by
    rcases le_total (F.height z) (F.height u) with hle | hle
    · exact hNormal.common_parent_upper_rows hUP hZP hUUpper hZUpper hle (huBelow.trans_lt hzAbove)
    · exact (hNormal.common_parent_upper_rows hZP hUP hZUpper hUUpper hle (hzBelow.trans_lt huAbove)).symm
  obtain ⟨uCell, zCell, hURead, hZRead, hRows⟩ :=
    uCopy.common_parent_upper_rows zCopy hLast hUUnmarked hZUnmarked hUP hZP hUUpper hZUpper hSourceSame
  obtain ⟨uActual, hUActual, hUActualRow⟩ :=
    uCopy.effective_upper_row nextUCopy hLast hUUnmarked hUUpper hNextUUnmarked
  obtain ⟨zActual, hZActual, hZActualRow⟩ :=
    zCopy.effective_upper_row nextZCopy hLast hZUnmarked hZUpper hNextZUnmarked
  have hUCell : uCell = uActual := Except.ok.inj (hURead.symm.trans hUActual)
  have hZCell : zCell = zActual := Except.ok.inj (hZRead.symm.trans hZActual)
  have hNextRows : nextUCopy.read.outputCell.row = nextZCopy.read.outputCell.row :=
    hUActualRow.symm.trans ((congrArg Cell.row hUCell).symm.trans
      (hRows.trans ((congrArg Cell.row hZCell).trans hZActualRow)))
  obtain ⟨actualU, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt nextUCopy.output_read
  obtain ⟨actualZ, hZRef, hZCell⟩ := Canonical.frame_node_of_cellAt nextZCopy.output_read
  have hActualRows : T.height actualU = T.height actualZ :=
    (congrArg Cell.row hUCell).trans (hNextRows.trans (congrArg Cell.row hZCell).symm)
  have hRealNext : Frame.Real nextU := by
    have hi := (Frame.upper_spec hUUpper).2
    change 0 < nextU.2.val
    omega
  have hOne : (1 : Row) ≤ T.height actualU := by
    change (1 : Row) ≤ (T.cell actualU).row
    rw [hUCell]
    exact (Frame.one_le_height hNormal.toOrdered hRealNext).trans nextUCopy.read.source_row_le_output
  obtain ⟨event, hEvent, hEventRow⟩ := eventCut_of_member
    (mem_eventCuts.mpr (height_mem_eventRows actualU hOne))
  exact ⟨actualU, actualZ, event, hURef, hZRef, hUCell, hZCell, hActualRows, hEvent, hEventRow,
    frontierAt_of_height_eq hValid.toOrdered (T.eventCut_one_le event) hEventRow.symm,
    frontierAt_of_height_eq hValid.toOrdered (T.eventCut_one_le event) (hActualRows.symm.trans hEventRow.symm)⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.marker_eq_of_unmarked_upper
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.contourCut_eq_of_unmarked_upper
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.effective_upper_row
#print axioms OmegaY.Expansion.common_parent_advance_event
