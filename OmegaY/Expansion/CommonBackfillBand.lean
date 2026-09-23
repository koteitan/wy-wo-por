/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonBackfillBand.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.TotalFrontier

/-!
# Common additive contribution through actual copied bands

Only the stored references of the upper cells need agree. In particular,
the incoming left leg of the physical marker at the bottom of a band may
differ in the two columns; it is not used by the band's backfill.
All numerical addends are derived from the actual mountain sums and reads.
This does not itself assert that two copied marker bands have been aligned.
-/

namespace OmegaY.Expansion

open Canonical Geometry

def bandValue (nodes : Column) (start offset : Nat) : Nat :=
  (nodes[start + offset]?.getD phantom).value

def BandParentsAgree (left right : Column) (startLeft startRight count : Nat) : Prop :=
  ∀ offset, offset < count →
    (left[startLeft + offset + 1]?.getD phantom).left =
      (right[startRight + offset + 1]?.getD phantom).left

theorem common_addends_sum (a b : Nat → Nat) (count : Nat)
    (hSteps : ∀ offset, offset < count → ∃ addend,
      a offset = a (offset + 1) + addend ∧ b offset = b (offset + 1) + addend) :
    ∃ total, a 0 = a count + total ∧ b 0 = b count + total := by
  induction count with
  | zero => exact ⟨0, by omega, by omega⟩
  | succ count ih =>
    obtain ⟨total, ha, hb⟩ := ih (fun offset hOffset => hSteps offset (by omega))
    obtain ⟨addend, haStep, hbStep⟩ := hSteps count (by omega)
    exact ⟨addend + total, by omega, by omega⟩

/-- Two actual positive bands with the same upper-stored parents receive
exactly the same total contribution between their endpoints. -/
theorem MountainSums.common_band_addend {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {leftColumn rightColumn : Nat} {left right : Column}
    (hLeft : mountain[leftColumn]? = some left) (hRight : mountain[rightColumn]? = some right)
    {startLeft startRight count : Nat} (hStartLeft : 0 < startLeft) (hStartRight : 0 < startRight)
    (hBoundLeft : startLeft + count < left.size) (hBoundRight : startRight + count < right.size)
    (hAgree : BandParentsAgree left right startLeft startRight count) :
    ∃ addend, bandValue left startLeft 0 = bandValue left startLeft count + addend ∧
      bandValue right startRight 0 = bandValue right startRight count + addend := by
  obtain ⟨hlc, hLeftEq⟩ := Array.getElem?_eq_some_iff.mp hLeft
  obtain ⟨hrc, hRightEq⟩ := Array.getElem?_eq_some_iff.mp hRight
  have hLeftValid : ColumnValid mountain leftColumn left := hLeftEq ▸ hValid leftColumn hlc
  have hRightValid : ColumnValid mountain rightColumn right := hRightEq ▸ hValid rightColumn hrc
  have hLeftSums : left.toList.IsChain (AdjacentSum mountain) := hLeftEq ▸ hSums leftColumn hlc
  have hRightSums : right.toList.IsChain (AdjacentSum mountain) := hRightEq ▸ hSums rightColumn hrc
  apply common_addends_sum
  intro offset hOffset
  have hl : startLeft + offset < left.size := by omega
  have hlu : startLeft + offset + 1 < left.size := by omega
  have hr : startRight + offset < right.size := by omega
  have hru : startRight + offset + 1 < right.size := by omega
  have hLeftSum := (List.isChain_iff_getElem.mp hLeftSums) (startLeft + offset)
    (by simpa only [Array.length_toList] using hlu)
  have hRightSum := (List.isChain_iff_getElem.mp hRightSums) (startRight + offset)
    (by simpa only [Array.length_toList] using hru)
  simp only [Array.getElem_toList] at hLeftSum hRightSum
  have hLeftReal : left[startLeft + offset].row ≠ 0 := ne_of_gt
    (hLeftValid.rows_strict 0 (startLeft + offset) phantom _ hLeftValid.phantom
      (Array.getElem?_eq_getElem hl) (by omega))
  have hRightReal : right[startRight + offset].row ≠ 0 := ne_of_gt
    (hRightValid.rows_strict 0 (startRight + offset) phantom _ hRightValid.phantom
      (Array.getElem?_eq_getElem hr) (by omega))
  obtain ⟨leftRef, leftParent, hLeftStored, hLeftRead, _, hLeftValue⟩ := hLeftSum hLeftReal
  obtain ⟨rightRef, rightParent, hRightStored, hRightRead, _, hRightValue⟩ := hRightSum hRightReal
  have hStoredEq : left[startLeft + offset + 1].left = right[startRight + offset + 1].left := by
    simpa only [Array.getElem?_eq_getElem hlu, Array.getElem?_eq_getElem hru, Option.getD_some]
      using hAgree offset hOffset
  have hRefEq : leftRef = rightRef := Option.some.inj
    (hLeftStored.symm.trans (hStoredEq.trans hRightStored))
  subst rightRef
  have hParentEq : rightParent = leftParent := Except.ok.inj (hRightRead.symm.trans hLeftRead)
  subst rightParent
  have hlu' : startLeft + (offset + 1) < left.size := by omega
  have hru' : startRight + (offset + 1) < right.size := by omega
  refine ⟨leftParent.value, ?_, ?_⟩
  · simpa only [bandValue, Nat.add_assoc, Array.getElem?_eq_getElem hl,
      Array.getElem?_eq_getElem hlu', Option.getD_some] using hLeftValue
  · simpa only [bandValue, Nat.add_assoc, Array.getElem?_eq_getElem hr,
      Array.getElem?_eq_getElem hru', Option.getD_some] using hRightValue

/-- The common gap contribution preserves, and reflects, the comparison
between the actual band endpoints. -/
theorem MountainSums.common_band_compare {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {leftColumn rightColumn : Nat} {left right : Column}
    (hLeft : mountain[leftColumn]? = some left) (hRight : mountain[rightColumn]? = some right)
    {startLeft startRight count : Nat} (hStartLeft : 0 < startLeft) (hStartRight : 0 < startRight)
    (hBoundLeft : startLeft + count < left.size) (hBoundRight : startRight + count < right.size)
    (hAgree : BandParentsAgree left right startLeft startRight count) :
    (bandValue left startLeft 0 ≤ bandValue right startRight 0 ↔
      bandValue left startLeft count ≤ bandValue right startRight count) ∧
    (bandValue left startLeft 0 < bandValue right startRight 0 ↔
      bandValue left startLeft count < bandValue right startRight count) := by
  obtain ⟨addend, hL, hR⟩ := hSums.common_band_addend hValid hLeft hRight
    hStartLeft hStartRight hBoundLeft hBoundRight hAgree
  omega

/-- Actual expansion supplies all sums and validity. The remaining input
is solely an alignment of concrete upper-stored references and array indices. -/
theorem expandDiagram_common_band_addend {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    {leftColumn rightColumn : Nat} {left right : Column}
    (hLeft : result[leftColumn]? = some left) (hRight : result[rightColumn]? = some right)
    {startLeft startRight count : Nat} (hStartLeft : 0 < startLeft) (hStartRight : 0 < startRight)
    (hBoundLeft : startLeft + count < left.size) (hBoundRight : startRight + count < right.size)
    (hAgree : BandParentsAgree left right startLeft startRight count) :
    ∃ addend, bandValue left startLeft 0 = bandValue left startLeft count + addend ∧
      bandValue right startRight 0 = bandValue right startRight count + addend :=
  (expandDiagram_equations hLegal hRun).1.common_band_addend
    (expandDiagram_valid_of_success hLegal hRun) hLeft hRight hStartLeft hStartRight
    hBoundLeft hBoundRight hAgree

end OmegaY.Expansion

#print axioms OmegaY.Expansion.common_addends_sum
#print axioms OmegaY.Expansion.MountainSums.common_band_addend
#print axioms OmegaY.Expansion.MountainSums.common_band_compare
#print axioms OmegaY.Expansion.expandDiagram_common_band_addend
