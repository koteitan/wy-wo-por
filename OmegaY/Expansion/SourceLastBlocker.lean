/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SourceLastBlocker.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalFrontierNumeric
import OmegaY.Geometry.RecordParentBound

/-!
# The actual last blocker of a source search

A successful source parent search supplies its last rejected record and
all the source inequalities needed by the common-parent copy argument.
No source record path, height barrier, or upper-value comparison is assumed.
These are source statements; transporting them through copying remains a
separate task.
-/

namespace OmegaY.Geometry.Frame

/-- The entire last-blocker packet for a non-immediate successful search.
The blocker and both uppers are actual nodes of the given source frame. -/
theorem Normal.source_last_blocker {F : Frame} (hF : F.Normal)
    {u q p : F.Node} (hParent : F.P u = some p) (hQ : F.Q u = some q)
    (hDistinct : q ≠ p) :
    ∃ z uUpper zUpper,
      ParentPath F q z ∧ F.P z = some p ∧
      p.1.val < z.1.val ∧ z.1.val < u.1.val ∧
      F.upper u = some uUpper ∧ F.upper z = some zUpper ∧
      F.height z ≤ F.height u ∧ F.height u < F.height zUpper ∧
      F.height uUpper = F.height zUpper ∧
      F.value u ≤ F.value z ∧ F.value uUpper ≤ F.value zUpper := by
  have hUReal : Real u := real_of_value_pos hF.toOrdered
    ((P_value hF.toOrdered hParent).1.trans (P_value hF.toOrdered hParent).2)
  have hQReal := Q_real hF.toOrdered hUReal hQ
  obtain ⟨candidate, hCandidate, trace⟩ := (P_iff hF.toOrdered).mp hParent
  have hCandidateEq : candidate = q := Option.some.inj (hCandidate.symm.trans hQ)
  subst candidate
  rcases trace.parentPath_last_barrier hF.toOrdered (hF.real_positive q hQReal) with
    hDirect | ⟨z, path, hLast, hBarrier⟩
  · exact (hDistinct hDirect).elim
  · obtain ⟨uUpper, hUUpper⟩ := hF.upper_of_parent hParent
    obtain ⟨zUpper, hZUpper⟩ := hF.upper_of_parent hLast
    have hZReal := path.real_of_start hF.toOrdered hQReal
    have hZBelow := (record_parent_left_and_below hF.toOrdered hQ path).2
    have hZAbove := current_below_record_parent_upper hF.toOrdered
      (LeftParentGeometry.of_normal hF u.1.val) hUReal hQ path hZUpper
    obtain ⟨uParent, hUP, hURow, hUValue, _⟩ := hF.upper_step u uUpper hUReal hUUpper
    obtain ⟨zParent, hZP, hZRow, hZValue, _⟩ := hF.upper_step z zUpper hZReal hZUpper
    have hUPeq : uParent = p := Option.some.inj (hUP.symm.trans hParent)
    have hZPeq : zParent = p := Option.some.inj (hZP.symm.trans hLast)
    subst uParent
    subst zParent
    have hSameRow : F.height uUpper = F.height zUpper := by
      rw [hURow, hZRow]
      exact Row.B_eq_of_between hZBelow (P_height_le hF.toOrdered hLast)
        (by simpa only [hZRow] using hZAbove)
    have hUpperBarrier : F.value uUpper ≤ F.value zUpper := by
      rw [hUValue, hZValue]
      omega
    exact ⟨z, uUpper, zUpper, path, hLast, P_column_lt hF.toOrdered hLast,
      record_barrier_column_lt hF.toOrdered hQ path, hUUpper, hZUpper,
      hZBelow, hZAbove, hSameRow, hBarrier, hUpperBarrier⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- A concrete source build determines the initial candidate as well as
the complete direct-hit/last-blocker alternative. All source-side numerical
and geometric inputs of the blocker argument are conclusions. -/
theorem build_source_last_blocker {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain)
    {u p : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P u = some p) :
    ∃ q, (Frame.ofMountain mountain).Q u = some q ∧
      (q = p ∨ ∃ z uUpper zUpper,
        Frame.ParentPath (Frame.ofMountain mountain) q z ∧
        (Frame.ofMountain mountain).P z = some p ∧
        p.1.val < z.1.val ∧ z.1.val < u.1.val ∧
        (Frame.ofMountain mountain).upper u = some uUpper ∧
        (Frame.ofMountain mountain).upper z = some zUpper ∧
        (Frame.ofMountain mountain).height z ≤ (Frame.ofMountain mountain).height u ∧
        (Frame.ofMountain mountain).height u < (Frame.ofMountain mountain).height zUpper ∧
        (Frame.ofMountain mountain).height uUpper = (Frame.ofMountain mountain).height zUpper ∧
        (Frame.ofMountain mountain).value u ≤ (Frame.ofMountain mountain).value z ∧
        (Frame.ofMountain mountain).value uUpper ≤ (Frame.ofMountain mountain).value zUpper) := by
  have hNormal := build_normal_of_success hBuild
  obtain ⟨q, hQ, _⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  refine ⟨q, hQ, ?_⟩
  by_cases hDirect : q = p
  · exact Or.inl hDirect
  · exact Or.inr (hNormal.source_last_blocker hParent hQ hDirect)

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.source_last_blocker
#print axioms OmegaY.Expansion.build_source_last_blocker
