/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/ParentExit.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.PathBranch

/-!
# Exhaustive exits of an actual finite numerical-parent path

Strictly decreasing column indices force a path starting right of a fixed
root column either to terminate on that side, to reach the root column,
or to cross directly to a strictly earlier column. This concerns parent
traversal inside one finite frame, not repeated expansion termination.
-/

namespace OmegaY.Geometry.Frame

theorem parent_path_exit {F : Frame} (hF : F.Ordered) {root : Nat}
    {source : F.Node} (hRight : root < source.1.val) :
    (∃ terminal, ParentPath F source terminal ∧ root < terminal.1.val ∧ F.P terminal = none) ∨
      (∃ endpoint, ParentPath F source endpoint ∧ endpoint.1.val = root) ∨
      (∃ last parent, ParentPath F source last ∧ root < last.1.val ∧
        F.P last = some parent ∧ parent.1.val < root) := by
  generalize hColumn : source.1.val = column
  induction column using Nat.strongRecOn generalizing source with
  | ind column ih =>
      cases hParent : F.P source with
      | none => exact .inl ⟨source, .refl _, hRight, hParent⟩
      | some parent =>
          by_cases hParentRight : root < parent.1.val
          · have hBefore : parent.1.val < column := (P_column_lt hF hParent).trans_eq hColumn
            rcases ih parent.1.val hBefore hParentRight rfl with
              ⟨terminal, path, hTerminalRight, hTerminal⟩ |
              ⟨endpoint, path, hEndpoint⟩ | ⟨last, fixed, path, hLastRight, hFixed, hFixedColumn⟩
            · exact .inl ⟨terminal, .cons hParent path, hTerminalRight, hTerminal⟩
            · exact .inr (.inl ⟨endpoint, .cons hParent path, hEndpoint⟩)
            · exact .inr (.inr ⟨last, fixed, .cons hParent path, hLastRight, hFixed, hFixedColumn⟩)
          · by_cases hRoot : parent.1.val = root
            · exact .inr (.inl ⟨parent, .cons hParent (.refl _), hRoot⟩)
            · exact .inr (.inr ⟨source, parent, .refl _, hRight, hParent, by omega⟩)

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.parent_path_exit
