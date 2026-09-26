/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootCandidateRange.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFixedCandidateRecognition

/-!
# Actual effective rows stay inside source root-column intervals

This uses the executed controlling marker and its genuine reference cap.
Any root-column row above a source row is also above that effective copy.
It does not identify the boundary candidate with the original source node.
-/

namespace OmegaY.Geometry.Frame

theorem cap_le_of_same_column_height_lt {F : Frame} (hF : F.Ordered)
    {root node : F.Node} {cap : Row}
    (hBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    (hColumn : node.1 = root.1) (hAbove : F.height root < F.height node) :
    cap ≤ F.height node := by
  rcases root with ⟨column, index⟩
  rcases node with ⟨nodeColumn, nodeIndex⟩
  change nodeColumn = column at hColumn
  subst nodeColumn
  have hIndex : index.val < nodeIndex.val :=
    (hF.rows_strict column).lt_iff_lt.mp hAbove
  have hBound : index.val + 1 < F.length column := by have := nodeIndex.isLt; omega
  let upper : F.Node := ⟨column, ⟨index.val + 1, hBound⟩⟩
  have hUpper : F.upper ⟨column, index⟩ = some upper := by
    simp only [Frame.upper, hBound, ↓reduceDIte, upper]
  exact (hBarrier upper hUpper).trans
    ((hF.rows_strict column).monotone (show (⟨index.val + 1, hBound⟩ : Fin _) ≤ nodeIndex by
      change index.val + 1 ≤ nodeIndex.val
      omega))

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

theorem row_lt_root_height (hLast : 1 < last)
    {rootNode : (Frame.ofMountain p.reduced).Node}
    (hColumn : rootNode.1.val = p.root.column)
    (hAbove : (Frame.ofMountain p.reduced).height source <
      (Frame.ofMountain p.reduced).height rootNode) :
    copy.read.outputCell.row < (Frame.ofMountain p.reduced).height rootNode := by
  let F := Frame.ofMountain p.reduced
  let md := copy.data.marker_data copy.read.marker copy.read.marker_mem
  have hNormal := build_normal_of_success p.reduced_build
  rcases copy.state.marker_source_transport hLast copy.data copy.read.marker_mem
      rfl copy.read.marker_before with
    ⟨_, hFixed⟩ | ⟨index, a, hTarget, _, hInside | ⟨_, hFixed⟩⟩
  · exact (copy.read.output_row.trans hFixed).trans_lt hAbove
  · have hColumns : rootNode.1 = a.root.1 :=
      Fin.ext (hColumn.trans (congrArg Ref.column a.root_ref).symm)
    have hRootBelow : F.height a.root < F.height rootNode :=
      hInside.2.1.trans_lt hAbove
    have hCap := Frame.cap_le_of_same_column_height_lt hNormal.toOrdered
      a.root_upper_barrier hColumns hRootBelow
    have hLift := (Row.lift_mem_interval a.target_lower a.target_below
      (a.root_row.symm.trans_le hInside.2.1) hInside.2.2).2
    rw [copy.read.output_row, ← hTarget]
    exact hLift.trans_le hCap
  · exact (copy.read.output_row.trans hFixed).trans_lt hAbove

/-- The new current row is in the very same source root-candidate row
interval, including when that current row rises. -/
theorem root_candidate_range (hLast : 1 < last)
    {candidate : (Frame.ofMountain p.reduced).Node}
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hRoot : candidate.1.val = p.root.column) :
    (Frame.ofMountain p.reduced).height candidate ≤ copy.read.outputCell.row ∧
      ∀ upper, (Frame.ofMountain p.reduced).upper candidate = some upper →
        copy.read.outputCell.row < (Frame.ofMountain p.reduced).height upper := by
  have hNormal := build_normal_of_success p.reduced_build
  refine ⟨(Frame.Q_height_le hNormal.toOrdered hCandidate).trans copy.read.source_row_le_output, ?_⟩
  intro upper hUpper
  exact copy.row_lt_root_height hLast
    ((congrArg Fin.val (Frame.upper_spec hUpper).1).trans hRoot)
    (Frame.Q_upper_gt hNormal.toOrdered hCandidate hUpper)

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.cap_le_of_same_column_height_lt
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.row_lt_root_height
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.root_candidate_range
