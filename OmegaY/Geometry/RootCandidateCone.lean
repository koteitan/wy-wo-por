/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RootCandidateCone.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.IntervalLegTransport

/-!
# Pulling an actual candidate's root cone into its child's column

Strictly above the root row, the real child has a real predecessor.
Its numerical parent is either the current candidate or that candidate's
immediate predecessor. The same-row parent-shadow theorem therefore pulls
the root cone back through this real predecessor. No condition on the
current child's accepted numerical parent is needed.
-/

namespace OmegaY.Geometry.Frame

theorem root_cone_child_of_candidate {F : Frame} (hF : F.Normal)
    {root source candidate : F.Node} (hRootReal : Real root)
    (hCandidate : F.Q source = some candidate)
    (hCone : RootCone F root candidate)
    (hAbove : F.height root < F.height source)
    (hCandidateLower : F.height root ≤ F.height candidate) :
    RootCone F root source := by
  obtain ⟨lower, hLowerReal, hUpper, hColumn, _⟩ :=
    real_lower_of_height_lt hF.toOrdered hRootReal hAbove
  obtain ⟨oldParent, hOldParent, _⟩ := hF.upper_step lower source hLowerReal hUpper
  have hOldCone : RootCone F root oldParent ∧ F.height root ≤ F.height oldParent := by
    rcases candidate_after_upper hF hOldParent hUpper with hSame | ⟨plus, hPlus, hPlusRow, hSame⟩
    · have he : oldParent = candidate := Option.some.inj (hSame.symm.trans hCandidate)
      exact he.symm ▸ ⟨hCone, hCandidateLower⟩
    · have he : plus = candidate := Option.some.inj (hSame.symm.trans hCandidate)
      subst plus
      obtain ⟨low, hLowReal, hLowColumn, hLowRow, hLowPath⟩ := hCone
      refine ⟨⟨low, hLowReal, hLowColumn.trans (upper_spec hPlus).1, hLowRow, hLowPath⟩, ?_⟩
      have hLowBefore : F.height low < F.height candidate :=
        hLowRow.trans_lt (hAbove.trans_eq hPlusRow.symm)
      exact hLowRow.symm.trans_le (height_le_lower_of_lt_upper hF.toOrdered hPlus hLowColumn hLowBefore)
  exact (root_cone_child_of_parent hF hOldParent hOldCone.1 hOldCone.2).1.same_column hColumn

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.root_cone_child_of_candidate
