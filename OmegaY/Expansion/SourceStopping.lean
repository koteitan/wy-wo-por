/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SourceStopping.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FrozenSource

/-! The contour's numerical stopping test cannot fire before a genuine
source-column top. This fact is about frozen source cells, not new copies. -/

namespace OmegaY.Expansion

open Canonical

def NoPrematureOne (nodes : Column) : Prop :=
  ∀ index current upper, nodes[index]? = some current → nodes[index + 1]? = some upper →
    current.value ≠ 1

theorem build_source_no_premature_one {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain) {sourceColumn : Nat} {nodes : Column}
    (hColumn : mountain[sourceColumn]? = some nodes) : NoPrematureOne nodes := by
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hValid : ColumnValid mountain sourceColumn nodes :=
    hNodes ▸ build_valid_of_success hBuild sourceColumn hc
  intro index current upper hCurrent hUpper
  by_cases hZero : index = 0
  · have hCurrentZero : nodes[0]? = some current := by simpa only [hZero] using hCurrent
    have he : current = phantom := Option.some.inj (hCurrentZero.symm.trans hValid.phantom)
    simp [he, phantom]
  · have hSteps : ColumnSteps mountain sourceColumn nodes :=
      hNodes ▸ build_steps hBuild sourceColumn hc
    have hLarge := (hSteps index current upper hCurrent hUpper (by omega)).1
    omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_source_no_premature_one
