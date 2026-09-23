/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualReferenceGapRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedNodeOrigin
import OmegaY.Expansion.PreservedSearchNodes

/-!
# Numerical recognition of every actual reference-gap cell

Actual fill membership selects an interior rung, a parent-interval seam,
or the selected top endpoint. Previously proved executable fill steps
supply the real upper, numerical first hit and raw edge in all three cases.
Complete-column preservation then places that same step in the final graph.
No output upper, output parent, or numerical induction hypothesis is input.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

/-- Every actual reference-gap cell is the lower endpoint of a previously
proved canonical fill step, including the highest fill-to-contour seam. -/
theorem ColumnCopyData.reference_gap_step
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {gap : List Cell} {original lower : Cell}
    (hFill : fill mountain ⟨sourceColumn, marker.index + 1⟩ shift
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row = .ok gap)
    (hMember : original ∈ gap) (hShape : SameShape original lower) :
    ∃ parentRef parent, ∃ step : ActualFillStep mountain column parentRef parent,
      step.lower.row = lower.row := by
  let md := d.marker_data marker hm
  obtain ⟨hp, hParentNodes⟩ := Array.getElem?_eq_some_iff.mp md.parent_nodes
  have hParentValid : ColumnValid mountain (md.sourceParent.column + shift) md.parentNodes :=
    hParentNodes ▸ d.ambient_valid _ hp
  have hStrict := fillRowsStrict_of_columnValid hParentValid
  have hUpperRead : lookup mountain ⟨sourceColumn, marker.index + 1⟩ = .ok md.upper :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, md.upper_at⟩
  have hLeftward := (d.source_valid.stored_valid _ _ _ md.upper_at md.upper_left).1
  have hExact := fill_eq_cells hUpperRead md.upper_left md.parent_nodes hStrict md.target_at
    le_rfl (Nat.add_lt_add_right hLeftward shift) (low := md.current.row)
  have hGap : gap = fillCells md.parentNodes (md.sourceParent.column + shift)
      md.current.row md.targetCell.row := Except.ok.inj (hFill.symm.trans hExact)
  have hActualMember : original ∈ fillCells md.parentNodes (md.sourceParent.column + shift)
      md.current.row md.targetCell.row := hGap ▸ hMember
  obtain ⟨parentIndex, parent, parentUpper, hParent, hParentUpper, hLow, hHigh,
    hParentRow, hUpperCap, hRung, _, _⟩ := mem_fillCells hStrict md.target_at le_rfl hActualMember
  obtain ⟨degree, hDegree, hDegreeRow⟩ := Row.mem_fillLadder.mp hRung
  by_cases hInterior : degree + 1 < Row.jump parent.row parentUpper.row
  · obtain ⟨step, hStepLower, _⟩ := d.copyColumn_fill_interior hParentPower hParentLow hNoPremature
      hRun hm hParent hParentUpper ⟨hLow, hHigh⟩ hInterior
    exact ⟨_, _, step, hStepLower.1.symm.trans (hDegreeRow.trans hShape.1)⟩
  · have hDegreeEq : degree = Row.jump parent.row parentUpper.row - 1 := by omega
    have hUpperRow : parentUpper.row = original.row := by
      calc
        parentUpper.row = Row.bump parent.row (Row.jump parent.row parentUpper.row - 1) :=
          hParentPower marker hm parentIndex parent parentUpper hParent hParentUpper
        _ = Row.bump parent.row degree := by rw [hDegreeEq]
        _ = original.row := hDegreeRow
    by_cases hBelow : parentUpper.row < md.targetCell.row
    · obtain ⟨nextParent, hNextParent, _, _⟩ :=
        fill_successor hStrict md.target_at le_rfl hParentUpper hBelow
      obtain ⟨step, hStepLower, _⟩ := d.copyColumn_fill_seam hParentPower hParentLow hNoPremature
        hRun hm hParent hParentUpper hNextParent ⟨hLow, hHigh⟩ ⟨hLow.trans hParentRow.le, hBelow⟩
      exact ⟨_, _, step, hStepLower.1.symm.trans (hUpperRow.trans hShape.1)⟩
    · have hTargetEq : parentUpper.row = md.targetCell.row :=
        le_antisymm hUpperCap (le_of_not_gt hBelow)
      have hRaised : md.current.row < md.targetCell.row :=
        hLow.trans_lt (hParentRow.trans_eq hTargetEq)
      obtain ⟨step, hStepRow, _⟩ := d.prepared_fill_contour_seam hSource
        hParentPower hParentLow hNoPremature hRun hm hRaised
      exact ⟨_, _, step, hStepRow.trans (hTargetEq.symm.trans (hUpperRow.trans hShape.1))⟩

/-- A real fill certificate is located by its actual lower row and then
transported to a final node through complete-column preservation. -/
theorem CopiedNodeOrigin.rawParent_eq_P_of_fill_step
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    (hValid : MountainValid result) {parentRef : Ref} {parent : Cell}
    (step : ActualFillStep packet.before packet.column parentRef parent)
    (hRow : step.lower.row = (Frame.ofMountain result).height node) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  have hColumnValid : ColumnValid packet.before packet.before.size packet.column := by
    obtain ⟨actual, hActual, _, hColumn, _, _⟩ := packet.data.copyColumn_valid
    have he : actual = packet.column := Except.ok.inj (hActual.symm.trans packet.copy_run)
    exact he ▸ hColumn
  have hPosition := column_read_index_eq_of_row hColumnValid step.lower_at packet.node_read hRow
  have hCurrentRef : Frame.ref node = ⟨packet.before.size, step.position⟩ :=
    congrArg₂ Ref.mk packet.target_column.symm hPosition.symm
  have hEdge : RawRefEdge (packet.before.push packet.column)
      ⟨packet.before.size, step.position⟩ parentRef :=
    ⟨step.lower, step.upper, parent,
      cellAt_ok_iff.mpr ⟨packet.column, by simp, step.lower_at⟩,
      cellAt_ok_iff.mpr ⟨packet.column, by simp, step.upper_at⟩,
      step.upper_left, step.parent_at⟩
  have hFinalEdge := hEdge.preserve packet.preserved
  have hEdgeRead := hFinalEdge
  obtain ⟨_, _, actualParent, _, _, _, hParentRead⟩ := hEdgeRead
  obtain ⟨parentNode, hParentRef, _⟩ := Canonical.frame_node_of_cellAt hParentRead
  have hRaw := hFinalEdge.rawParent hCurrentRef hParentRef
  have hFind : Canonical.findParent result (Frame.ref node) = .ok parentRef := by
    rw [hCurrentRef, packet.preserved.findParent (by simp)]
    exact step.parent_found
  have hP := (Executable.findParent_ref_iff hValid.toOrdered node parentNode).mp
    (by simpa only [hParentRef] using hFind)
  exact hRaw.trans hP.symm

/-- The reference-gap constructor is completely recognized, including its
highest target endpoint. Actual state data supplies all parent-column
power and low-endpoint inputs; neither an upper nor an induction hypothesis
is passed by the caller. -/
theorem CopiedNodeOrigin.reference_gap_rawParent_eq_P
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {marker : Ref} (hm : marker ∈ packet.data.bucket) {gap : List Cell} {original : Cell}
    (hFill : fill packet.before ⟨packet.sourceColumn, marker.index + 1⟩
      (packet.block * (p.reduced.size - 1 - p.root.column))
      (packet.data.marker_data marker hm).current.row (packet.data.marker_data marker hm).targetCell.row = .ok gap)
    (hMember : original ∈ gap)
    (hShape : SameShape original ((Frame.ofMountain result).cell node)) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  obtain ⟨hNoPremature, hPP, hPL⟩ :=
    packet.state.column_data_parent_inputs hLast packet.source_bound packet.data
  obtain ⟨parentRef, parent, step, hRow⟩ := packet.data.reference_gap_step packet.source_read
    hPP hPL hNoPremature packet.copy_run hm hFill hMember hShape
  exact packet.rawParent_eq_P_of_fill_step
    (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun) step hRow

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.reference_gap_step
#print axioms OmegaY.Expansion.CopiedNodeOrigin.rawParent_eq_P_of_fill_step
#print axioms OmegaY.Expansion.CopiedNodeOrigin.reference_gap_rawParent_eq_P
