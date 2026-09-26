/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedAnyCommonParentPair.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAnyCommonParentPair
import OmegaY.Expansion.PreservedFrameNodes

/-!
# Universal common-parent packets in later preserved mountains

Complete-column preservation transports all five typed nodes, complete
cells, actual copy occurrences, root endpoints and original-source reads.
Stored parents and consecutive uppers are preserved as well. Later event
indices are not identified with the old event enumeration.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace AnyCommonParentPair

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start before after : Mountain} {references : List Ref}
  {sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node}
  (pair : AnyCommonParentPair p block start references sourceU sourceZ sourceParent before)
  (h : PreservesColumns before after)

/-- Transport preserves the full source correspondence in every origin
branch; no copied or root-boundary endpoint is replaced by a bare row. -/
noncomputable def extend :
    AnyCommonParentPair p block start references sourceU sourceZ sourceParent after where
  uCopy := pair.uCopy.extend h
  u := h.mapNode pair.u
  z := h.mapNode pair.z
  parent := h.mapNode pair.parent
  uUpper := h.mapNode pair.uUpper
  zUpper := h.mapNode pair.zUpper
  u_ref := (h.mapNode_ref pair.u).trans pair.u_ref
  u_cell := (h.mapNode_cell pair.u).trans pair.u_cell
  z_origin := by
    rcases pair.z_origin with ⟨hFixed, hRef, hCell⟩ | ⟨hMoved, copy, hRef, hCell⟩
    · exact .inl ⟨hFixed, (h.mapNode_ref pair.z).trans hRef,
        (h.mapNode_cell pair.z).trans hCell⟩
    · exact .inr ⟨hMoved, copy.extend h, (h.mapNode_ref pair.z).trans hRef,
        (h.mapNode_cell pair.z).trans hCell⟩
  parent_origin := by
    rcases pair.parent_origin with ⟨hFixed, hRef, hCell⟩ |
      ⟨hRoot, endpoint, hRef, hCell⟩ | ⟨hMoved, copy, hRef, hCell⟩
    · exact .inl ⟨hFixed, (h.mapNode_ref pair.parent).trans hRef,
        (h.mapNode_cell pair.parent).trans hCell⟩
    · refine .inr (.inl ⟨hRoot, endpoint.extend h, ?_, ?_⟩)
      · simpa only [EffectiveRootEndpoint.extend_reference] using (h.mapNode_ref pair.parent).trans hRef
      · simpa only [EffectiveRootEndpoint.extend_target] using (h.mapNode_cell pair.parent).trans hCell
    · exact .inr (.inr ⟨hMoved, copy.extend h, (h.mapNode_ref pair.parent).trans hRef,
        (h.mapNode_cell pair.parent).trans hCell⟩)
  u_real := h.mapNode_real pair.u_real
  z_real := h.mapNode_real pair.z_real
  z_column := by simpa only [h.mapNode_column] using pair.z_column
  u_parent := h.mapNode_rawParent pair.u_parent
  z_parent := h.mapNode_rawParent pair.z_parent
  u_upper := h.mapNode_upper pair.u_upper
  z_upper := h.mapNode_upper pair.z_upper
  upper_height := by simpa only [h.mapNode_height] using pair.upper_height

@[simp] theorem extend_u_ref : Frame.ref (pair.extend h).u = Frame.ref pair.u :=
  h.mapNode_ref pair.u

@[simp] theorem extend_z_ref : Frame.ref (pair.extend h).z = Frame.ref pair.z :=
  h.mapNode_ref pair.z

@[simp] theorem extend_parent_ref : Frame.ref (pair.extend h).parent = Frame.ref pair.parent :=
  h.mapNode_ref pair.parent

@[simp] theorem extend_uUpper_ref : Frame.ref (pair.extend h).uUpper = Frame.ref pair.uUpper :=
  h.mapNode_ref pair.uUpper

@[simp] theorem extend_zUpper_ref : Frame.ref (pair.extend h).zUpper = Frame.ref pair.zUpper :=
  h.mapNode_ref pair.zUpper

@[simp] theorem extend_u_cell :
    (Frame.ofMountain after).cell (pair.extend h).u = (Frame.ofMountain before).cell pair.u :=
  h.mapNode_cell pair.u

@[simp] theorem extend_z_cell :
    (Frame.ofMountain after).cell (pair.extend h).z = (Frame.ofMountain before).cell pair.z :=
  h.mapNode_cell pair.z

@[simp] theorem extend_parent_cell :
    (Frame.ofMountain after).cell (pair.extend h).parent = (Frame.ofMountain before).cell pair.parent :=
  h.mapNode_cell pair.parent

@[simp] theorem extend_uUpper_cell :
    (Frame.ofMountain after).cell (pair.extend h).uUpper = (Frame.ofMountain before).cell pair.uUpper :=
  h.mapNode_cell pair.uUpper

@[simp] theorem extend_zUpper_cell :
    (Frame.ofMountain after).cell (pair.extend h).zUpper = (Frame.ofMountain before).cell pair.zUpper :=
  h.mapNode_cell pair.zUpper

@[simp] theorem extend_u_column : (pair.extend h).u.1.val = pair.u.1.val :=
  h.mapNode_column pair.u

@[simp] theorem extend_z_column : (pair.extend h).z.1.val = pair.z.1.val :=
  h.mapNode_column pair.z

@[simp] theorem extend_parent_column : (pair.extend h).parent.1.val = pair.parent.1.val :=
  h.mapNode_column pair.parent

theorem extend_values :
    (Frame.ofMountain after).value (pair.extend h).u = (Frame.ofMountain before).value pair.u ∧
      (Frame.ofMountain after).value (pair.extend h).z = (Frame.ofMountain before).value pair.z :=
  ⟨congrArg Cell.value (h.mapNode_cell pair.u), congrArg Cell.value (h.mapNode_cell pair.z)⟩

theorem extend_parent_value :
    (Frame.ofMountain after).value (pair.extend h).parent =
      (Frame.ofMountain before).value pair.parent :=
  congrArg Cell.value (h.mapNode_cell pair.parent)

theorem extend_upper_values :
    (Frame.ofMountain after).value (pair.extend h).uUpper = (Frame.ofMountain before).value pair.uUpper ∧
      (Frame.ofMountain after).value (pair.extend h).zUpper = (Frame.ofMountain before).value pair.zUpper :=
  ⟨congrArg Cell.value (h.mapNode_cell pair.uUpper), congrArg Cell.value (h.mapNode_cell pair.zUpper)⟩

theorem extend_heights :
    (Frame.ofMountain after).height (pair.extend h).u = (Frame.ofMountain before).height pair.u ∧
      (Frame.ofMountain after).height (pair.extend h).z = (Frame.ofMountain before).height pair.z ∧
      (Frame.ofMountain after).height (pair.extend h).parent = (Frame.ofMountain before).height pair.parent ∧
      (Frame.ofMountain after).height (pair.extend h).uUpper = (Frame.ofMountain before).height pair.uUpper ∧
      (Frame.ofMountain after).height (pair.extend h).zUpper = (Frame.ofMountain before).height pair.zUpper :=
  ⟨h.mapNode_height pair.u, h.mapNode_height pair.z, h.mapNode_height pair.parent,
    h.mapNode_height pair.uUpper, h.mapNode_height pair.zUpper⟩

end AnyCommonParentPair
end OmegaY.Expansion

#print axioms OmegaY.Expansion.AnyCommonParentPair.extend
#print axioms OmegaY.Expansion.AnyCommonParentPair.extend_values
#print axioms OmegaY.Expansion.AnyCommonParentPair.extend_parent_value
#print axioms OmegaY.Expansion.AnyCommonParentPair.extend_heights
