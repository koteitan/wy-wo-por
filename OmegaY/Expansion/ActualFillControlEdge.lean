/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFillControlEdge.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFillEdgeKeys
import OmegaY.Expansion.FillContourSeam

/-!
# A concrete effective weak edge controls every actual fill edge

A nonempty reference gap has a real top-to-contour step, even when its
parent-column high reference is a value-one top with no outgoing edge of
its own. The controlling edge is in the copied child column: its lower
and parent have the high reference row, and its upper is one row above.

All three cells survive through the packet's actual complete-column
preservation. The fill edge and its control have identical endpoint
*columns*, which is the endpoint identity used by the reflection model.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

universe u

private theorem preserve_cell_read {before after : Mountain}
    (h : PreservesColumns before after) {ref : Ref} {cell : Cell}
    (hRead : Canonical.cellAt before ref = .ok cell) :
    Canonical.cellAt after ref = .ok cell := by
  obtain ⟨nodes, hColumn, hCell⟩ := Canonical.cellAt_ok_iff.mp hRead
  exact Canonical.cellAt_ok_iff.mpr ⟨nodes, h.column_read hColumn, hCell⟩

/-- A proved actual fill step gives a real stored edge in any later graph
which retains its completed column. No fresh adjacency is an input. -/
theorem ActualFillStep.stored_edge_preserved {mountain result : Mountain} {column : Column}
    {parentRef : Ref} {parent : Cell} (step : ActualFillStep mountain column parentRef parent)
    (hPreserved : PreservesColumns (mountain.push column) result) :
    ∃ edge : RealStoredEdge (Frame.ofMountain result),
      Frame.ref edge.lower = ⟨mountain.size, step.position⟩ ∧
      (Frame.ofMountain result).cell edge.lower = step.lower ∧
      (Frame.ofMountain result).cell edge.upper = step.upper ∧
      Frame.ref edge.parent = parentRef ∧
      (Frame.ofMountain result).cell edge.parent = parent := by
  have hLower : Canonical.cellAt result ⟨mountain.size, step.position⟩ = .ok step.lower :=
    preserve_cell_read hPreserved (Canonical.cellAt_ok_iff.mpr ⟨column, by simp, step.lower_at⟩)
  have hUpper : Canonical.cellAt result ⟨mountain.size, step.position + 1⟩ = .ok step.upper :=
    preserve_cell_read hPreserved (Canonical.cellAt_ok_iff.mpr ⟨column, by simp, step.upper_at⟩)
  have hParent := preserve_cell_read hPreserved step.parent_at
  obtain ⟨lower, hLowerRef, hLowerCell⟩ := Canonical.frame_node_of_cellAt hLower
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpper
  obtain ⟨parentNode, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt hParent
  have hUpperNode := Frame.upper_of_refs hLowerRef hUpperRef
  have hLowerReal : Frame.Real lower := by
    have hIndex := congrArg Ref.index hLowerRef
    change lower.2.val = step.position at hIndex
    change 0 < lower.2.val
    rw [hIndex]
    exact step.position_positive
  let edge : RealStoredEdge (Frame.ofMountain result) := {
    lower := lower
    upper := upper
    parent := parentNode
    lower_real := hLowerReal
    upper_eq := hUpperNode
    parent_eq := rawParent_eq_of_upper_left hUpperNode
      (by rw [hUpperCell, hParentRef]; exact step.upper_left) }
  exact ⟨edge, hLowerRef, hLowerCell, hUpperCell, hParentRef, hParentCell⟩

/-- A genuinely returned gap member forces a raised target. The statement
comes from the actual segment's three calls, not from a target assumption. -/
theorem CopiedNodeOrigin.reference_gap_raised
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    {marker : Ref} (hm : marker ∈ packet.data.bucket) {gap : List Cell} {original : Cell}
    (hFill : fill packet.before ⟨packet.sourceColumn, marker.index + 1⟩
      (packet.block * (p.reduced.size - 1 - p.root.column))
      (packet.data.marker_data marker hm).current.row
      (packet.data.marker_data marker hm).targetCell.row = .ok gap)
    (hMember : original ∈ gap) :
    (packet.data.marker_data marker hm).current.row <
      (packet.data.marker_data marker hm).targetCell.row := by
  let d := packet.data
  let md := d.marker_data marker hm
  obtain ⟨_, _, actualGap, _, _, _, _, _, hActualFill, _, _, hBounds⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero
      d.destination.le d.source_top packet.references (d.bucket.map Ref.index)
      md.current_at md.upper_at md.upper_left md.parent_nodes md.target_at md.reference md.target_lower
      (d.segment_run hm)
  have hEq : actualGap = gap := Except.ok.inj (hActualFill.symm.trans hFill)
  have hBound := hBounds original (hEq ▸ hMember)
  exact hBound.1.trans_le hBound.2

/-- The actual nonempty gap has an actual surviving degree-zero effective
weak control edge, with the high reference as parent and the same copied
child column. This also covers a high reference that is a parent-column top. -/
theorem CopiedNodeOrigin.reference_gap_control_edge
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    (hLast : 1 < last) {marker : Ref} (hm : marker ∈ packet.data.bucket)
    {gap : List Cell} {original : Cell}
    (hFill : fill packet.before ⟨packet.sourceColumn, marker.index + 1⟩
      (packet.block * (p.reduced.size - 1 - p.root.column))
      (packet.data.marker_data marker hm).current.row
      (packet.data.marker_data marker hm).targetCell.row = .ok gap)
    (hMember : original ∈ gap) :
    ∃ control : RealStoredEdge (Frame.ofMountain result),
      control.lower.1 = node.1 ∧
      Frame.ref control.parent =
        ⟨(packet.data.marker_data marker hm).sourceParent.column +
          packet.block * (p.reduced.size - 1 - p.root.column),
          (packet.data.marker_data marker hm).targetIndex⟩ ∧
      (Frame.ofMountain result).cell control.parent = (packet.data.marker_data marker hm).targetCell ∧
      (Frame.ofMountain result).height control.lower = (packet.data.marker_data marker hm).targetCell.row ∧
      (Frame.ofMountain result).height control.upper =
        Row.bump (packet.data.marker_data marker hm).targetCell.row 0 ∧
      control.degree = 0 := by
  have hRaised := packet.reference_gap_raised hm hFill hMember
  obtain ⟨hNoPremature, hPP, hPL⟩ :=
    packet.state.column_data_parent_inputs hLast packet.source_bound packet.data
  obtain ⟨step, hLowerRow, hUpperRow⟩ := packet.data.prepared_fill_contour_seam
    packet.source_read hPP hPL hNoPremature packet.copy_run hm hRaised
  obtain ⟨control, hLowerRef, hLowerCell, hUpperCell, hParentRef, hParentCell⟩ :=
    step.stored_edge_preserved packet.preserved
  have hColumn : control.lower.1 = node.1 :=
    Fin.ext ((congrArg Ref.column hLowerRef).trans packet.target_column)
  have hLower : (Frame.ofMountain result).height control.lower =
      (packet.data.marker_data marker hm).targetCell.row := by
    simpa only [Frame.height, hLowerCell] using hLowerRow
  have hUpper : (Frame.ofMountain result).height control.upper =
      Row.bump (packet.data.marker_data marker hm).targetCell.row 0 := by
    simpa only [Frame.height, hUpperCell] using hUpperRow
  refine ⟨control, hColumn, hParentRef, hParentCell, hLower, hUpper, ?_⟩
  unfold RealStoredEdge.degree
  rw [hLower]
  simp only [Frame.height, hParentCell, Row.jump_self]

/-- The pure reference-key bound is now a comparison to a concrete actual
edge with exactly the same ordinal-label endpoints as the fill edge.
The reference control's zero degree is proved from actual seam rows. -/
theorem CopiedNodeOrigin.reference_gap_key_lt_control_edge
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    (hLegal : Legal (front ++ [last])) (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (packet : CopiedNodeOrigin p result edge.upper)
    {marker : Ref} (hm : marker ∈ packet.data.bucket) {gap : List Cell} {original : Cell}
    (hFill : fill packet.before ⟨packet.sourceColumn, marker.index + 1⟩
      (packet.block * (p.reduced.size - 1 - p.root.column))
      (packet.data.marker_data marker hm).current.row
      (packet.data.marker_data marker hm).targetCell.row = .ok gap)
    (hMember : original ∈ gap)
    (hShape : SameShape original ((Frame.ofMountain result).cell edge.upper))
    {D : Nat} (hSupported : ∀ w : (Frame.ofMountain result).Node, ∀ i,
      D < i → Row.coeff ((Frame.ofMountain result).height w) i = 0)
    {Label : Type u} [LinearOrder Label] (labels : Fin result.size → Label)
    (hLabels : StrictMono labels) :
    ∃ control : RealStoredEdge (Frame.ofMountain result),
      control.lower.1 = edge.lower.1 ∧ control.parent.1 = edge.parent.1 ∧
      control.degree = 0 ∧
      Frame.ref control.parent =
        ⟨(packet.data.marker_data marker hm).sourceParent.column +
          packet.block * (p.reduced.size - 1 - p.root.column),
          (packet.data.marker_data marker hm).targetIndex⟩ ∧
      Keys.eval (edge.keyTemplate (expandDiagram_normal hLegal hRun).toOrdered D) labels <
        Keys.eval (control.keyTemplate (expandDiagram_normal hLegal hRun).toOrdered D) labels := by
  obtain ⟨control, hColumn, hParentRef, _, _, _, hDegree⟩ :=
    packet.reference_gap_control_edge hLast hm hFill hMember
  obtain ⟨reference, hReferenceRef, _, hSameColumn, _, _, hKey⟩ :=
    packet.reference_gap_edge_key_bound hLegal hRun edge hm hFill hMember hShape hSupported labels hLabels
  have hParentEq : control.parent = reference :=
    Executable.ref_injective _ (hParentRef.trans hReferenceRef.symm)
  refine ⟨control, hColumn.trans (upper_spec edge.upper_eq).1,
    (congrArg Sigma.fst hParentEq).trans hSameColumn.symm, hDegree, hParentRef, ?_⟩
  rw [control.eval_keyTemplate_eq_truncate (expandDiagram_normal hLegal hRun).toOrdered
    (show control.degree ≤ D by omega) labels, hDegree, Nat.sub_zero, hParentEq]
  exact hKey

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualFillStep.stored_edge_preserved
#print axioms OmegaY.Expansion.CopiedNodeOrigin.reference_gap_control_edge
#print axioms OmegaY.Expansion.CopiedNodeOrigin.reference_gap_key_lt_control_edge
