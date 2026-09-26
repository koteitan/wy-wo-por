/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/InheritedRootCone.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.RootInterval
import OmegaY.Rows.Lift

/-! Root-row ancestry propagates from a numerical parent to its child.
The child need not lie below a root interval cap. This direction follows
from actual same-row shadows, rather than interval closure. -/

namespace OmegaY.Geometry.Frame

/-- An actual root-row shadow below the parent gives a real child-column
shadow, with its index below the child and its full numerical-parent path. -/
theorem RootCone.child_witness {F : Frame} (hF : F.Normal)
    {root child parent : F.Node} (hParent : F.P child = some parent)
    (hCone : RootCone F root parent) (hBelow : F.height root ≤ F.height parent) :
    ∃ low : F.Node, Real low ∧ low.1 = child.1 ∧ F.height low = F.height root ∧
      F.height low ≤ F.height child ∧ low.2.val ≤ child.2.val ∧ ParentPath F low root := by
  obtain ⟨parentLow, hReal, hColumn, hRow, hPath⟩ := hCone
  obtain ⟨low, hLowReal, hLowColumn, hLowHeight, hLowRow, hLowPath⟩ :=
    P_rowShadow hF hParent parentLow hReal hColumn (hRow.trans_le hBelow)
  have hIndex : low.2.val ≤ child.2.val := by
    rcases low with ⟨c, i⟩
    dsimp only at hLowColumn
    subst c
    exact (hF.rows_strict child.1).le_iff_le.mp hLowHeight
  exact ⟨low, hLowReal, hLowColumn, hLowRow.trans hRow, hLowHeight, hIndex,
    hLowPath.trans hPath⟩

theorem RootCone.of_parent {F : Frame} (hF : F.Normal)
    {root child parent : F.Node} (hParent : F.P child = some parent)
    (hCone : RootCone F root parent) (hBelow : F.height root ≤ F.height parent) :
    RootCone F root child := by
  obtain ⟨low, hReal, hColumn, hRow, _, _, hPath⟩ := hCone.child_witness hF hParent hBelow
  exact ⟨low, hReal, hColumn, hRow, hPath⟩

/-- If the child is above this cap, both of its endpoints are fixed by
this interval lift. Its parent can nevertheless be strictly lifted. -/
theorem RootInterval.child_transport_cases {F : Frame} (hF : F.Normal)
    {root child parent childUpper : F.Node} {degree : Nat} {target : Row}
    (hParent : F.P child = some parent)
    (hInside : RootInterval F root (Row.bump (F.height root) degree) parent)
    (hUpper : F.upper child = some childUpper)
    (hTargetLow : F.height root ≤ target)
    (hTargetHigh : target < Row.bump (F.height root) degree) :
    RootInterval F root (Row.bump (F.height root) degree) child ∨
      (Row.bump (F.height root) degree ≤ F.height child ∧
        RootCone F root child ∧
        Row.lift (F.height root) target (F.height child) = F.height child ∧
        Row.lift (F.height root) target (F.height childUpper) = F.height childUpper) := by
  have hCone := hInside.1.of_parent hF hParent hInside.2.1
  have hLow := hInside.2.1.trans (P_height_le hF.toOrdered hParent)
  by_cases hChild : F.height child < Row.bump (F.height root) degree
  · exact Or.inl ⟨hCone, hLow, hChild⟩
  · have hHigh := le_of_not_gt hChild
    have hUpperRow : F.height childUpper = Row.B (F.height child) (F.height parent) :=
      (aboveHeight_of_upper hUpper).symm.trans (hF.above_row hParent)
    exact Or.inr ⟨hHigh, hCone,
      Row.lift_eq_of_ge_cap hTargetLow hTargetHigh hHigh,
      Row.lift_eq_of_ge_cap hTargetLow hTargetHigh
        (hHigh.trans (hUpperRow ▸ (Row.lt_B (F.height child) (F.height parent)).le))⟩

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.RootCone.child_witness
#print axioms OmegaY.Geometry.Frame.RootCone.of_parent
#print axioms OmegaY.Geometry.Frame.RootInterval.child_transport_cases
