/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Geometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Canonical.Normal

/-! Geometry theorems specialized to the actual successful legal-input
constructor. The local geometric certificate is derived, not supplied. -/

namespace OmegaY.Canonical

open Geometry

theorem build_father_upper_bound {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p uplus pplus : (Frame.ofMountain mountain).Node}
    (hParent : findParent mountain (Frame.ref u) = .ok (Frame.ref p))
    (huplus : (Frame.ofMountain mountain).upper u = some uplus)
    (hpplus : (Frame.ofMountain mountain).upper p = some pplus) :
    (Frame.ofMountain mountain).height uplus ≤ (Frame.ofMountain mountain).height pplus := by
  have hNormal := build_normal_of_legal hLegal hBuild
  exact Frame.father_upper_bound_nodes hNormal
    ((Executable.findParent_ref_iff hNormal.toOrdered u p).mp hParent) huplus hpplus

theorem build_candidate_after_upper {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p upper : (Frame.ofMountain mountain).Node}
    (hParent : findParent mountain (Frame.ref u) = .ok (Frame.ref p))
    (hUpper : (Frame.ofMountain mountain).upper u = some upper) :
    nextCandidate mountain (Frame.ref upper) = .ok (Frame.ref p) ∨
      ∃ pplus, (Frame.ofMountain mountain).upper p = some pplus ∧
        (Frame.ofMountain mountain).height pplus = (Frame.ofMountain mountain).height upper ∧
        nextCandidate mountain (Frame.ref upper) = .ok (Frame.ref pplus) := by
  have hNormal := build_normal_of_legal hLegal hBuild
  have hp := (Executable.findParent_ref_iff hNormal.toOrdered u p).mp hParent
  rcases Frame.candidate_after_upper hNormal hp hUpper with he | ⟨pplus, hu, hh, he⟩
  · exact Or.inl ((Executable.nextCandidate_ref_iff hNormal.toOrdered upper p).mpr he)
  · exact Or.inr ⟨pplus, hu, hh,
      (Executable.nextCandidate_ref_iff hNormal.toOrdered upper pplus).mpr he⟩

end OmegaY.Canonical

#print axioms OmegaY.Canonical.build_father_upper_bound
#print axioms OmegaY.Canonical.build_candidate_after_upper
