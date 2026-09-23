/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFillSourceControl.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFillControlEdge

/-!
# The concrete source weak edge behind a filled segment's control

The original weak edge is recovered from real source reads and the source
canonical rule. Its degree is proved zero from the marker-successor row.
The source and target controls have the exact column shifts used by copyEdge.
This identifies endpoints for the reflected-copy branch; it does not assume
or assert the still separate transport inequality for the control's roots.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

universe u

/-- Every nonempty actual gap comes from a real degree-zero source edge.
In particular its source parent is at or to the right of the bad-root
column, so both endpoint columns use the shifted copy rule. -/
theorem CopiedNodeOrigin.reference_gap_source_edge
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    {marker : Ref} (hm : marker ∈ packet.data.bucket) {gap : List Cell} {original : Cell}
    (hFill : fill packet.before ⟨packet.sourceColumn, marker.index + 1⟩
      (packet.block * (p.reduced.size - 1 - p.root.column))
      (packet.data.marker_data marker hm).current.row
      (packet.data.marker_data marker hm).targetCell.row = .ok gap)
    (hMember : original ∈ gap) :
    ∃ source : RealStoredEdge (Frame.ofMountain p.reduced),
      Frame.ref source.lower = ⟨packet.sourceColumn, marker.index⟩ ∧
      Frame.ref source.upper = ⟨packet.sourceColumn, marker.index + 1⟩ ∧
      Frame.ref source.parent = (packet.data.marker_data marker hm).sourceParent ∧
      (Frame.ofMountain p.reduced).cell source.lower = (packet.data.marker_data marker hm).current ∧
      source.degree = 0 ∧ p.root.column ≤ source.parent.1.val := by
  let d := packet.data
  let md := d.marker_data marker hm
  have hRaised := packet.reference_gap_raised hm hFill hMember
  have hIndex : 0 < marker.index := by
    by_contra hn
    have hz : marker.index = 0 := by omega
    have hCurrentAt : d.sources[0]? = some md.current := by simpa only [hz] using md.current_at
    have hCurrent : md.current = phantom := Option.some.inj
      (hCurrentAt.symm.trans d.source_valid.phantom)
    have hZero : md.current.row = 0 := by rw [hCurrent]; rfl
    have hTarget := d.target_zero hm hZero
    change md.targetCell.row = 0 at hTarget
    change md.current.row < md.targetCell.row at hRaised
    rw [hZero, hTarget] at hRaised
    exact (lt_irrefl _) hRaised
  have hLowerRead : Canonical.cellAt p.reduced ⟨packet.sourceColumn, marker.index⟩ = .ok md.current :=
    Canonical.cellAt_ok_iff.mpr ⟨d.sources, packet.source_read, md.current_at⟩
  have hUpperRead : Canonical.cellAt p.reduced ⟨packet.sourceColumn, marker.index + 1⟩ = .ok md.upper :=
    Canonical.cellAt_ok_iff.mpr ⟨d.sources, packet.source_read, md.upper_at⟩
  obtain ⟨lower, hLowerRef, hLowerCell⟩ := Canonical.frame_node_of_cellAt hLowerRead
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hUpper := Frame.upper_of_refs hLowerRef hUpperRef
  have hReal : Frame.Real lower := by
    have hi := congrArg Ref.index hLowerRef
    change lower.2.val = marker.index at hi
    change 0 < lower.2.val
    rw [hi]
    exact hIndex
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨parent, hP, _, _, hLeft⟩ := hNormal.upper_step lower upper hReal hUpper
  have hParentRef : Frame.ref parent = md.sourceParent := by
    apply Option.some.inj
    exact hLeft.symm.trans (by rw [hUpperCell]; exact md.upper_left)
  let source : RealStoredEdge (Frame.ofMountain p.reduced) := {
    lower := lower
    upper := upper
    parent := parent
    lower_real := hReal
    upper_eq := hUpper
    parent_eq := (hNormal.rawParent_eq_P hReal).trans hP }
  obtain ⟨hSuccessor, hParentRoot⟩ := d.prepared_marker_successor packet.source_read hm hRaised
  change md.upper.row = Row.bump md.current.row 0 at hSuccessor
  have hJump : Row.jump ((Frame.ofMountain p.reduced).height lower)
      ((Frame.ofMountain p.reduced).height upper) = 1 := by
    simp only [Frame.height, hLowerCell, hUpperCell, hSuccessor, Row.jump_bump, Nat.zero_add]
  have hDegreeEq := source.degree_from_vertical_jump hNormal.rawRowGeometry
  change Row.jump ((Frame.ofMountain p.reduced).height lower)
    ((Frame.ofMountain p.reduced).height upper) = source.degree + 1 at hDegreeEq
  have hDegree : source.degree = 0 := by rw [hJump] at hDegreeEq; omega
  have hParentColumn := congrArg Ref.column hParentRef
  refine ⟨source, hLowerRef, hUpperRef, hParentRef, hLowerCell, hDegree, ?_⟩
  change p.root.column ≤ parent.1.val
  change parent.1.val = md.sourceParent.column at hParentColumn
  rw [hParentColumn]
  exact hParentRoot

/-- A fill edge is strictly below a specific actual effective control,
and that control's endpoint columns are the exact shifts of a specific
actual source weak edge. No comparison with the transported source key is
an input or conclusion of this theorem; that is the next independent
ordinary-effective-edge transport obligation. -/
theorem CopiedNodeOrigin.reference_gap_source_control_pair
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
    ∃ (source : RealStoredEdge (Frame.ofMountain p.reduced))
        (control : RealStoredEdge (Frame.ofMountain result)),
      source.degree = 0 ∧ control.degree = 0 ∧
      Frame.ref source.lower = ⟨packet.sourceColumn, marker.index⟩ ∧
      p.root.column ≤ source.parent.1.val ∧
      control.lower.1 = edge.lower.1 ∧ control.parent.1 = edge.parent.1 ∧
      control.lower.1.val = source.lower.1.val + packet.block * (p.reduced.size - 1 - p.root.column) ∧
      control.parent.1.val = source.parent.1.val + packet.block * (p.reduced.size - 1 - p.root.column) ∧
      Keys.eval (edge.keyTemplate (expandDiagram_normal hLegal hRun).toOrdered D) labels <
        Keys.eval (control.keyTemplate (expandDiagram_normal hLegal hRun).toOrdered D) labels := by
  obtain ⟨source, hSourceLower, _, hSourceParent, _, hSourceDegree, hRoot⟩ :=
    packet.reference_gap_source_edge hm hFill hMember
  obtain ⟨control, hChild, hParent, hControlDegree, hControlParent, hKey⟩ :=
    packet.reference_gap_key_lt_control_edge hLegal hLast hRun edge hm hFill hMember hShape
      hSupported labels hLabels
  have hSourceColumn := congrArg Ref.column hSourceLower
  have hSourceParentColumn := congrArg Ref.column hSourceParent
  have hControlParentColumn := congrArg Ref.column hControlParent
  have hChildColumn := congrArg Fin.val hChild
  have hUpperColumn := congrArg Fin.val (upper_spec edge.upper_eq).1
  have hDestination := packet.data.destination
  have hTargetColumn := packet.target_column
  refine ⟨source, control, hSourceDegree, hControlDegree, hSourceLower, hRoot,
    hChild, hParent, ?_, ?_, hKey⟩
  · change source.lower.1.val = packet.sourceColumn at hSourceColumn
    omega
  · change source.parent.1.val = (packet.data.marker_data marker hm).sourceParent.column
      at hSourceParentColumn
    change control.parent.1.val = (packet.data.marker_data marker hm).sourceParent.column +
      packet.block * (p.reduced.size - 1 - p.root.column) at hControlParentColumn
    omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.CopiedNodeOrigin.reference_gap_source_edge
#print axioms OmegaY.Expansion.CopiedNodeOrigin.reference_gap_source_control_pair
