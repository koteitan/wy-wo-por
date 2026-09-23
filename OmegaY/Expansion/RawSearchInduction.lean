/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawSearchInduction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.TotalFrontier
import OmegaY.Expansion.RawSearchReconstruction
import OmegaY.Geometry.RecordParentBound

/-!
# Exact strict-left induction interfaces after raw geometry

The only unproved input in the left prefix is recognition of its existing
raw edges by numerical P. Tops independently settle missing raw parents.
Raw B and raw D then provide all geometry needed from the recognized prefix.
There is no recognition assumption on the current column.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem MountainSums.rawParent_eq_P_of_recognition {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    (hTops : MountainTops mountain) {u : (Frame.ofMountain mountain).Node}
    (hReal : Frame.Real u)
    (hRecognized : ∀ parent, (Frame.ofMountain mountain).rawParent u = some parent →
      (Frame.ofMountain mountain).P u = some parent) :
    (Frame.ofMountain mountain).rawParent u = (Frame.ofMountain mountain).P u := by
  cases hRaw : (Frame.ofMountain mountain).rawParent u with
  | some parent => exact (hRecognized parent hRaw).symm
  | none =>
    have hOne := (hSums.rawParent_none_iff_value_one hValid hTops hReal).mp hRaw
    cases hParent : (Frame.ofMountain mountain).P u with
    | none => rfl
    | some parent =>
      obtain ⟨hPositive, hSmall⟩ := Frame.P_value hValid.toOrdered hParent
      rw [hOne] at hSmall
      omega

theorem rawParentSearch_iff_agreement {mountain : Mountain}
    (hValid : MountainValid mountain) (hSums : MountainSums mountain)
    (hTops : MountainTops mountain) :
    (Frame.ofMountain mountain).RawParentSearch ↔
      ∀ u, Frame.Real u → (Frame.ofMountain mountain).rawParent u = (Frame.ofMountain mountain).P u := by
  constructor
  · intro h u hReal
    exact hSums.rawParent_eq_P_of_recognition hValid hTops hReal (h u · hReal)
  · intro h u parent hReal hRaw
    exact (h u hReal).symm.trans hRaw

private theorem upper_of_value_gt_one {mountain : Mountain}
    (hTops : MountainTops mountain) {u : (Frame.ofMountain mountain).Node}
    (hValue : 1 < (Frame.ofMountain mountain).value u) :
    ∃ upper, (Frame.ofMountain mountain).upper u = some upper := by
  cases hUpper : (Frame.ofMountain mountain).upper u with
  | none =>
    have hOne := MountainTops.value_one_of_upper_none hTops hUpper
    omega
  | some upper => exact ⟨upper, rfl⟩

/-- Every field of the left-column geometry packet is obtained from
independent raw laws and numerical recognition confined to that prefix. -/
theorem leftParentGeometry_of_raw_recognition {mountain : Mountain}
    (hValid : MountainValid mountain) (hSums : MountainSums mountain)
    (hTops : MountainTops mountain) (hRaw : MountainRawGeometry mountain)
    (hFather : (Frame.ofMountain mountain).RawFatherUpperBound) {bound : Nat}
    (hKnown : ∀ u parent, u.1.val < bound → Frame.Real u →
      (Frame.ofMountain mountain).rawParent u = some parent →
      (Frame.ofMountain mountain).P u = some parent) :
    Frame.LeftParentGeometry (Frame.ofMountain mountain) bound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u _ _ hValue
    exact upper_of_value_gt_one hTops hValue
  · intro u upper _ hReal hUpper
    obtain ⟨_, _, _, _, _, _, hLarge⟩ := hSums.rawParent_upper hValid hReal hUpper
    exact hLarge
  · intro u upper hLeft hReal hUpper
    obtain ⟨parent, hParent, _, _, hB⟩ := hRaw.rawRowGeometry u upper hReal hUpper
    exact ⟨parent, hKnown u parent hLeft hReal hParent, hB⟩
  · intro u parent hLeft hParent hParentValue
    have hUValue := (Frame.P_value hValid.toOrdered hParent).2
    have hReal := Frame.real_of_value_pos hValid.toOrdered
      ((by omega : 0 < (Frame.ofMountain mountain).value parent).trans hUValue)
    have hEq := hSums.rawParent_eq_P_of_recognition hValid hTops hReal
      (fun p hp => hKnown u p hLeft hReal hp)
    have hRawParent := hEq.trans hParent
    obtain ⟨upper, hUpper⟩ := upper_of_value_gt_one hTops (hParentValue.trans hUValue)
    obtain ⟨parentUpper, hParentUpper⟩ := upper_of_value_gt_one hTops hParentValue
    rw [Frame.aboveHeight_of_upper hUpper, Frame.aboveHeight_of_upper hParentUpper]
    exact hFather u parent upper parentUpper hReal hRawParent hUpper hParentUpper

/-- For an actual expansion all geometric and numerical-sum hypotheses are
discharged; only the strict-left numerical induction hypothesis remains. -/
theorem expandDiagram_leftParentGeometry {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    {bound : Nat}
    (hKnown : ∀ (u parent : (Frame.ofMountain result).Node), u.1.val < bound → Frame.Real u →
      (Frame.ofMountain result).rawParent u = some parent →
      (Frame.ofMountain result).P u = some parent) :
    Frame.LeftParentGeometry (Frame.ofMountain result) bound :=
  leftParentGeometry_of_raw_recognition (expandDiagram_valid_of_success hLegal hRun)
    (expandDiagram_equations hLegal hRun).1 (expandDiagram_equations hLegal hRun).2
    (expandDiagram_raw_geometry hLegal hRun) (expandDiagram_raw_father_upper_bound hLegal hRun) hKnown

end OmegaY.Expansion

#print axioms OmegaY.Expansion.MountainSums.rawParent_eq_P_of_recognition
#print axioms OmegaY.Expansion.rawParentSearch_iff_agreement
#print axioms OmegaY.Expansion.leftParentGeometry_of_raw_recognition
#print axioms OmegaY.Expansion.expandDiagram_leftParentGeometry
