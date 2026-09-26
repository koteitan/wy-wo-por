/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/RowShadow.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.RowShadow
import OmegaY.Canonical.Normal

/-! Same-row ancestry for the actual canonical builder and its parent search. -/

namespace OmegaY.Canonical

open Geometry

theorem build_P_rowShadow {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p : (Frame.ofMountain mountain).Node}
    (hp : (Frame.ofMountain mountain).P u = some p) :
    Frame.RowShadow (Frame.ofMountain mountain) u p :=
  Frame.P_rowShadow (build_normal_of_legal hLegal hBuild) hp

theorem build_findParent_rowShadow {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u p : (Frame.ofMountain mountain).Node}
    (hp : findParent mountain (Frame.ref u) = .ok (Frame.ref p)) :
    Frame.RowShadow (Frame.ofMountain mountain) u p := by
  have hNormal := build_normal_of_legal hLegal hBuild
  exact Frame.P_rowShadow hNormal
    ((Executable.findParent_ref_iff hNormal.toOrdered u p).mp hp)

#print axioms build_findParent_rowShadow

end OmegaY.Canonical
