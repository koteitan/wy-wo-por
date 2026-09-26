/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFillCopiedKey.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFillControlEdge
import OmegaY.Expansion.CopiedNodeRetarget
import OmegaY.Expansion.ActualCopiedKeyBound

/-!
An actual fill edge is strictly below its actual effective weak control.
The control is then identified as a real recorded effective source copy,
so the ordinary transport theorem supplies its key bound.  No comparison
between the control and source keys is an additional hypothesis.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem CopiedNodeOrigin.reference_gap_key_bound
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
      D < i → Row.coeff ((Frame.ofMountain result).height w) i = 0) :
    Nonempty (ActualCopiedKeyBound p result
      (expandDiagram_valid_of_success hLegal hRun).toOrdered edge D) := by
  let hOrdered := (expandDiagram_valid_of_success hLegal hRun).toOrdered
  let columnLabels : Fin (Frame.ofMountain result).width → Nat := fun column => column.val
  obtain ⟨control, hControlColumn, hControlParentRef, _hParentCell, hControlRow, _hUpperRow, hDegree⟩ :=
    packet.reference_gap_control_edge hLast hm hFill hMember
  obtain ⟨reference, hReferenceRef, _hReferenceCell, hParentColumn, _hParentBefore,
      _hDegreeBound, hFillKey⟩ := packet.reference_gap_edge_key_bound hLegal hRun edge hm hFill
        hMember hShape hSupported columnLabels
        (fun _ _ h => h)
  have hParentEq : control.parent = reference := Executable.ref_injective _
    (hControlParentRef.trans hReferenceRef.symm)
  have hKey : Keys.eval (edge.keyTemplate hOrdered D) columnLabels <
      Keys.eval (control.keyTemplate hOrdered D) columnLabels := by
    have hControlEval : Keys.eval (control.keyTemplate hOrdered D) columnLabels =
        Keys.truncate (fun i : Fin (D + 1) =>
          columnLabels (scaleRoot hOrdered (D - i.val) reference).1) (D + 1) := by
      simpa only [hDegree, Nat.sub_zero, hParentEq] using
        control.eval_keyTemplate_eq_truncate hOrdered (show control.degree ≤ D by omega)
          columnLabels
    exact hFillKey.trans_eq hControlEval.symm
  have hChild : control.lower.1 = edge.lower.1 :=
    hControlColumn.trans (upper_spec edge.upper_eq).1
  have hParent : control.parent.1 = edge.parent.1 :=
    (congrArg Sigma.fst hParentEq).trans hParentColumn.symm
  have hUpperColumn : control.upper.1 = edge.upper.1 :=
    (upper_spec control.upper_eq).1.trans hControlColumn
  let controlPacket := packet.retarget control.upper hUpperColumn
  have hControlAt : packet.column[control.lower.2.val]? =
      some ((Frame.ofMountain result).cell control.lower) :=
    packet.read_same_column control.lower hControlColumn
  obtain ⟨certificate⟩ := packet.data.marker_effective_adjacent_source packet.copy_run
    hControlAt hm hControlRow
  obtain ⟨source, copy, hSourceColumn, hLowerRef⟩ := controlPacket.effective_adjacent_source
    control hOrdered certificate
  obtain ⟨bound⟩ := controlPacket.effective_key_bound control hLast hRun source copy hSourceColumn hLowerRef D
  exact ⟨bound.weaken (congrArg Fin.val hParent.symm) (congrArg Fin.val hChild.symm) hKey.le⟩

/-- The entire fill alternative of executable edge provenance is discharged. -/
theorem CopiedNodeOrigin.fill_upper_key_bound
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    (edge : RealStoredEdge (Frame.ofMountain result))
    (packet : CopiedNodeOrigin p result edge.upper)
    (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hFillOrigin : FillUpperOrigin packet.data ((Frame.ofMountain result).cell edge.upper))
    (D : Nat) (hSupported : ∀ w : (Frame.ofMountain result).Node, ∀ i,
      D < i → Row.coeff ((Frame.ofMountain result).height w) i = 0) :
    Nonempty (ActualCopiedKeyBound p result
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered edge D) := by
  obtain ⟨marker, hm, gap, original, hFill, hMember, hShape⟩ := hFillOrigin
  exact packet.reference_gap_key_bound (build_success_legal p.initial_build) hLast hRun edge hm
    hFill hMember hShape hSupported

/-- Every surviving newly copied real edge has a true source edge, the
actual block's endpoint map, and a complete key bound. The source kind
and fill control are recovered internally from the actual execution. -/
theorem Preparation.copied_edge_key_bound
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hColumn : p.reduced.size ≤ edge.lower.1.val) (D : Nat)
    (hSupported : ∀ w : (Frame.ofMountain result).Node, ∀ i,
      D < i → Row.coeff ((Frame.ofMountain result).height w) i = 0) :
    Nonempty (ActualCopiedKeyBound p result
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered edge D) := by
  rcases p.copied_edge_key_bound_or_fill hLast hCopies hRun edge hColumn D with
    hOrdinary | ⟨packet, hFill⟩
  · exact hOrdinary
  · exact packet.fill_upper_key_bound edge hLast hRun hFill D hSupported

end OmegaY.Expansion

#print axioms OmegaY.Expansion.CopiedNodeOrigin.reference_gap_key_bound
#print axioms OmegaY.Expansion.Preparation.copied_edge_key_bound
