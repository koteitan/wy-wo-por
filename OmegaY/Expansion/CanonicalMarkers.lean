/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CanonicalMarkers.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Canonical.BottomLegs
import OmegaY.Canonical.Normal
import OmegaY.Expansion.WeakGeometry

/-! The complete auxiliary row-zero marker chain for actual canonical build
outputs.  Its concrete bottom legs and its ordered geometry are conclusions
of the builder theorems, not additional hypotheses. -/

namespace OmegaY.Expansion

open Canonical

theorem build_phantomChain {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain) :
    PhantomChain mountain := by
  apply phantomChain_of_ordered (build_normal_of_legal hLegal hBuild).toOrdered
  intro c hi hpos
  simpa only [if_neg (Nat.ne_of_gt hpos)] using build_bottom_left hBuild c hi

theorem build_phantom_reachable {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {rootColumn currentColumn : Nat} (hle : rootColumn ≤ currentColumn)
    (hc : currentColumn < mountain.size) :
    ForwardWeakPath mountain ⟨rootColumn, 0⟩ ⟨currentColumn, 0⟩ :=
  (build_phantomChain hLegal hBuild).reachable hle hc

theorem build_phantom_weakReaches {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {rootColumn currentColumn : Nat} (hle : rootColumn ≤ currentColumn)
    (hc : currentColumn < mountain.size) :
    weakReaches mountain ⟨rootColumn, 0⟩ (currentColumn + 1) ⟨currentColumn, 0⟩ = .ok true :=
  (build_phantomChain hLegal hBuild).weakReaches hle hc

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_phantomChain
#print axioms OmegaY.Expansion.build_phantom_reachable
#print axioms OmegaY.Expansion.build_phantom_weakReaches
