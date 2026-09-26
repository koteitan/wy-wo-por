/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualAnyCommonParentPair.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMarkedCommonParentPacket
import OmegaY.Expansion.ActualFixedCommonParentPacket
import OmegaY.Expansion.ActualRootCommonParentPacket

/-!
# Every actual source common-parent comparison branch

One interface covers copied or unchanged earlier records and common
parents to either side of, or in, the root column. Source-to-target
correspondence is retained: the current child has an actual effective
copy, while the other node is either its unchanged complete source cell
or another actual effective copy. The target geometry is constructed
through the four established packet theorems.
-/

namespace OmegaY.Expansion

open Canonical Geometry

structure AnyCommonParentPair {front : List Nat} {last : Nat}
    (p : Preparation front last) (block : Nat) (start : Mountain) (references : List Ref)
    (sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  uCopy : EffectiveCopyOccurrence p block start references sourceU result
  u : (Frame.ofMountain result).Node
  z : (Frame.ofMountain result).Node
  parent : (Frame.ofMountain result).Node
  uUpper : (Frame.ofMountain result).Node
  zUpper : (Frame.ofMountain result).Node
  u_ref : Frame.ref u = uCopy.outputRef
  u_cell : (Frame.ofMountain result).cell u = uCopy.read.outputCell
  z_origin :
    (sourceZ.1.val ≤ p.root.column ∧ Frame.ref z = Frame.ref sourceZ ∧
      (Frame.ofMountain result).cell z = (Frame.ofMountain p.reduced).cell sourceZ) ∨
    (p.root.column < sourceZ.1.val ∧
      ∃ zCopy : EffectiveCopyOccurrence p block start references sourceZ result,
        Frame.ref z = zCopy.outputRef ∧ (Frame.ofMountain result).cell z = zCopy.read.outputCell)
  parent_origin :
    (sourceParent.1.val < p.root.column ∧ Frame.ref parent = Frame.ref sourceParent ∧
      (Frame.ofMountain result).cell parent = (Frame.ofMountain p.reduced).cell sourceParent) ∨
    (sourceParent.1.val = p.root.column ∧
      ∃ endpoint : EffectiveRootEndpoint p start references sourceParent result,
        Frame.ref parent = endpoint.reference ∧ (Frame.ofMountain result).cell parent = endpoint.target) ∨
    (p.root.column < sourceParent.1.val ∧
      ∃ parentCopy : EffectiveCopyOccurrence p block start references sourceParent result,
        Frame.ref parent = parentCopy.outputRef ∧
          (Frame.ofMountain result).cell parent = parentCopy.read.outputCell)
  u_real : Frame.Real u
  z_real : Frame.Real z
  z_column : z.1.val ≤ u.1.val
  u_parent : (Frame.ofMountain result).rawParent u = some parent
  z_parent : (Frame.ofMountain result).rawParent z = some parent
  u_upper : (Frame.ofMountain result).upper u = some uUpper
  z_upper : (Frame.ofMountain result).upper z = some zUpper
  upper_height : (Frame.ofMountain result).height uUpper = (Frame.ofMountain result).height zUpper

private theorem copied_node_cell
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    {node : (Frame.ofMountain result).Node} (hRef : Frame.ref node = copy.outputRef) :
    (Frame.ofMountain result).cell node = copy.read.outputCell :=
  Except.ok.inj ((cellAt_of_frame_node result node).symm.trans
    (by simpa only [hRef] using copy.output_read))

def EffectiveCommonParentPair.toAny
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node}
    (pair : EffectiveCommonParentPair p block start references sourceU sourceZ sourceParent result)
    (hZRight : p.root.column < sourceZ.1.val) (hParentRight : p.root.column < sourceParent.1.val) :
    AnyCommonParentPair p block start references sourceU sourceZ sourceParent result where
  uCopy := pair.uCopy
  u := pair.u
  z := pair.z
  parent := pair.parent
  uUpper := pair.uUpper
  zUpper := pair.zUpper
  u_ref := pair.u_ref
  u_cell := copied_node_cell pair.uCopy pair.u_ref
  z_origin := .inr ⟨hZRight, pair.zCopy, pair.z_ref, copied_node_cell pair.zCopy pair.z_ref⟩
  parent_origin := .inr (.inr ⟨hParentRight, pair.parentCopy, pair.parent_ref,
    copied_node_cell pair.parentCopy pair.parent_ref⟩)
  u_real := pair.u_real
  z_real := pair.z_real
  z_column := pair.z_column
  u_parent := pair.u_parent
  z_parent := pair.z_parent
  u_upper := pair.u_upper
  z_upper := pair.z_upper
  upper_height := pair.upper_height

def FixedCommonParentPair.toAny
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node}
    (pair : FixedCommonParentPair p block start references sourceU sourceZ sourceParent result)
    (hZRight : p.root.column < sourceZ.1.val) (hParentFixed : sourceParent.1.val < p.root.column) :
    AnyCommonParentPair p block start references sourceU sourceZ sourceParent result where
  uCopy := pair.uCopy
  u := pair.u
  z := pair.z
  parent := pair.parent
  uUpper := pair.uUpper
  zUpper := pair.zUpper
  u_ref := pair.u_ref
  u_cell := pair.u_cell
  z_origin := .inr ⟨hZRight, pair.zCopy, pair.z_ref, pair.z_cell⟩
  parent_origin := .inl ⟨hParentFixed, pair.parent_ref, pair.parent_cell⟩
  u_real := pair.u_real
  z_real := pair.z_real
  z_column := pair.z_column
  u_parent := pair.u_parent
  z_parent := pair.z_parent
  u_upper := pair.u_upper
  z_upper := pair.z_upper
  upper_height := pair.upper_height

def RootCommonParentPair.toAny
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node}
    (pair : RootCommonParentPair p block start references sourceU sourceZ sourceParent result)
    (hZRight : p.root.column < sourceZ.1.val) (hParentRoot : sourceParent.1.val = p.root.column) :
    AnyCommonParentPair p block start references sourceU sourceZ sourceParent result where
  uCopy := pair.uCopy
  u := pair.u
  z := pair.z
  parent := pair.parent
  uUpper := pair.uUpper
  zUpper := pair.zUpper
  u_ref := pair.u_ref
  u_cell := copied_node_cell pair.uCopy pair.u_ref
  z_origin := .inr ⟨hZRight, pair.zCopy, pair.z_ref, copied_node_cell pair.zCopy pair.z_ref⟩
  parent_origin := .inr (.inl ⟨hParentRoot, pair.rootEndpoint, pair.parent_ref,
    Except.ok.inj ((cellAt_of_frame_node result pair.parent).symm.trans
      (by simpa only [pair.parent_ref] using pair.rootEndpoint.result_read))⟩)
  u_real := pair.u_real
  z_real := pair.z_real
  z_column := pair.z_column
  u_parent := pair.u_parent
  z_parent := pair.z_parent
  u_upper := pair.u_upper
  z_upper := pair.z_upper
  upper_height := pair.upper_height

def MixedCommonParentPair.toAny
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node}
    (pair : MixedCommonParentPair p block start references sourceU sourceZ sourceParent sourceZUpper result)
    (hZLeft : sourceZ.1.val ≤ p.root.column) (hParentFixed : sourceParent.1.val < p.root.column) :
    AnyCommonParentPair p block start references sourceU sourceZ sourceParent result where
  uCopy := pair.uCopy
  u := pair.u
  z := pair.z
  parent := pair.parent
  uUpper := pair.uUpper
  zUpper := pair.zUpper
  u_ref := pair.u_ref
  u_cell := pair.u_cell
  z_origin := .inl ⟨hZLeft, pair.z_ref, pair.z_cell⟩
  parent_origin := .inl ⟨hParentFixed, pair.parent_ref, pair.parent_cell⟩
  u_real := pair.u_real
  z_real := pair.z_real
  z_column := pair.z_column
  u_parent := pair.u_parent
  z_parent := pair.z_parent
  u_upper := pair.u_upper
  z_upper := pair.z_upper
  upper_height := pair.upper_height

/-- Every source common-parent overlap with a copied current source has
a complete target comparison packet. All source marker, earlier-column,
and common-parent location branches are decided within the proof. -/
theorem DynamicBlockState.recorded_any_common_parent_pair
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZP : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hURight : p.root.column < sourceU.1.val)
    (hZColumn : sourceZ.1.val ≤ sourceU.1.val) (hBefore : sourceU.1.val < next)
    (hZUpper : (Frame.ofMountain p.reduced).upper sourceZ = some sourceZUpper)
    (hOrder : (Frame.ofMountain p.reduced).height sourceZ ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hOverlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper) :
    Nonempty (AnyCommonParentPair p block start references sourceU sourceZ sourceParent ambient) := by
  by_cases hZLeft : sourceZ.1.val ≤ p.root.column
  · obtain ⟨pair⟩ := s.recorded_mixed_common_parent_pair history hLast hUP hZP hURight hBefore
      hZLeft hZUpper hOrder hOverlap
    have hFixed := (Frame.P_column_lt (build_normal_of_success p.reduced_build).toOrdered hZP).trans_le hZLeft
    exact ⟨pair.toAny hZLeft hFixed⟩
  · have hZRight : p.root.column < sourceZ.1.val := Nat.lt_of_not_ge hZLeft
    rcases lt_trichotomy sourceParent.1.val p.root.column with hFixed | hRoot | hMoved
    · obtain ⟨pair⟩ := s.recorded_fixed_common_parent_pair history hLast hUP hZP hFixed hZRight
        hZColumn hBefore hZUpper hOrder hOverlap
      exact ⟨pair.toAny hZRight hFixed⟩
    · obtain ⟨pair⟩ := s.recorded_root_common_parent_pair history hLast hStartRun hUP hZP hRoot
        hZColumn hBefore hZUpper hOrder hOverlap
      exact ⟨pair.toAny hZRight hRoot⟩
    · obtain ⟨pair⟩ := s.recorded_common_parent_pair history hLast hStartRun hUP hZP hMoved
        hZColumn hBefore hZUpper hOrder hOverlap
      exact ⟨pair.toAny hZRight hMoved⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_any_common_parent_pair
