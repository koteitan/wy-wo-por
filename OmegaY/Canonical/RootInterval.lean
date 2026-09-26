/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/RootInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.RootInterval
import OmegaY.Canonical.Normal

/-! Root-interval closure on actual successfully built source mountains. -/

namespace OmegaY.Canonical

open Geometry

theorem build_root_interval_parent {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {root : (Frame.ofMountain mountain).Node} {degree : Nat}
    (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootBarrier : ∀ upper, (Frame.ofMountain mountain).upper root = some upper →
      Row.bump ((Frame.ofMountain mountain).height root) degree ≤
        (Frame.ofMountain mountain).height upper)
    {u p : (Frame.ofMountain mountain).Node}
    (hp : findParent mountain (Frame.ref u) = .ok (Frame.ref p))
    (hu : Frame.RootInterval (Frame.ofMountain mountain) root
      (Row.bump ((Frame.ofMountain mountain).height root) degree) u) :
    Frame.RootInterval (Frame.ofMountain mountain) root
      (Row.bump ((Frame.ofMountain mountain).height root) degree) p ∨
      (Frame.BeforeRoot (Frame.ofMountain mountain) root p ∧
        Row.bump ((Frame.ofMountain mountain).height root) degree ≤
          (Frame.ofMountain mountain).aboveHeight u) := by
  have hNormal := build_normal_of_legal hLegal hBuild
  exact Frame.root_interval_parent_bump hNormal hRootReal hDegree hRootBarrier
    ((Executable.findParent_ref_iff hNormal.toOrdered u p).mp hp) hu

theorem build_root_interval_internal_parent {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {root : (Frame.ofMountain mountain).Node} {degree : Nat}
    (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootBarrier : ∀ upper, (Frame.ofMountain mountain).upper root = some upper →
      Row.bump ((Frame.ofMountain mountain).height root) degree ≤
        (Frame.ofMountain mountain).height upper)
    {u p upper : (Frame.ofMountain mountain).Node}
    (hp : findParent mountain (Frame.ref u) = .ok (Frame.ref p))
    (hu : Frame.RootInterval (Frame.ofMountain mountain) root
      (Row.bump ((Frame.ofMountain mountain).height root) degree) u)
    (hUpper : (Frame.ofMountain mountain).upper u = some upper)
    (hInside : (Frame.ofMountain mountain).height upper <
      Row.bump ((Frame.ofMountain mountain).height root) degree) :
    Frame.RootInterval (Frame.ofMountain mountain) root
      (Row.bump ((Frame.ofMountain mountain).height root) degree) p := by
  have hNormal := build_normal_of_legal hLegal hBuild
  exact Frame.root_interval_internal_parent hNormal hRootReal
    (Row.bump_strictMono_exponent _ hDegree) hRootBarrier
    ((Executable.findParent_ref_iff hNormal.toOrdered u p).mp hp) hu hUpper hInside

#print axioms build_root_interval_parent
#print axioms build_root_interval_internal_parent

end OmegaY.Canonical
