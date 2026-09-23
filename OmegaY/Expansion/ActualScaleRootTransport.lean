/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualScaleRootTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualScaleParentTransport

/-!
# Multi-root transport for roots strictly inside the copied bad part

The actual source scale-root path is computed from `scaleParent` and then
transported along recorded executions. Its copied endpoint is a genuine
effective occurrence selected from history. A new root may extend farther
left, so the conclusion is an upper bound, not an unjustified root equality
with the source-root copy. Roots at or left of the bad-root column remain
outside the scope of this module.
-/

namespace OmegaY.Geometry.Frame

theorem Normal.parentPath_scaleRoot {F : Frame} (hNormal : F.Normal)
    (k : Nat) (u : F.Node) (hReal : Real u) :
    ParentPath F u (scaleRoot hNormal.toOrdered k u) := by
  cases hp : F.scaleParent k u with
  | none =>
    rw [scaleRoot_eq_of_none hNormal.toOrdered hp]
    exact .refl _
  | some parent =>
    have hParent : F.P u = some parent :=
      (hNormal.rawParent_eq_P hReal).symm.trans (scaleParent_some_iff.mp hp).1
    have hParentReal : Real parent := real_of_value_pos hNormal.toOrdered
      (P_value hNormal.toOrdered hParent).1
    rw [scaleRoot_eq_of_parent hNormal.toOrdered hp]
    exact .cons hParent (hNormal.parentPath_scaleRoot k parent hParentReal)
termination_by u.1.val
decreasing_by exact scaleParent_column_lt hNormal.toOrdered hp

theorem scaleRoot_eq_of_scale_path {F : Frame} (hOrdered : F.Ordered) {k : Nat}
    {u v : F.Node}
    (path : Relation.ReflTransGen (fun a b => F.scaleParent k a = some b) u v) :
    scaleRoot hOrdered k u = scaleRoot hOrdered k v := by
  induction path with
  | refl => rfl
  | tail prior hParent ih => exact ih.trans (scaleRoot_eq_of_parent hOrdered hParent)

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)

include s history hLast hStartRun

/-- A source scale-root strictly right of the bad root has an actual copied
endpoint, connected by a path entirely in the target scale forest. -/
theorem DynamicBlockState.recorded_scale_root_transport
    {source : (Frame.ofMountain p.reduced).Node} {k : Nat}
    (hReal : Real source)
    (hRootRight : p.root.column < (scaleRoot p.reduced_valid.toOrdered k source).1.val)
    (hBefore : source.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source ambient) :
    ∃ rootCopy : EffectiveCopyOccurrence p block start references
        (scaleRoot p.reduced_valid.toOrdered k source) ambient,
      Relation.ReflTransGen (fun u v => (Frame.ofMountain ambient).scaleParent k u = some v)
        copy.keyNode rootCopy.keyNode ∧
      scaleRoot s.ambient_valid.toOrdered k copy.keyNode =
        scaleRoot s.ambient_valid.toOrdered k rootCopy.keyNode ∧
      (scaleRoot s.ambient_valid.toOrdered k copy.keyNode).1.val ≤
        (scaleRoot p.reduced_valid.toOrdered k source).1.val +
          block * (p.reduced.size - 1 - p.root.column) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRootBefore : (scaleRoot p.reduced_valid.toOrdered k source).1.val < next :=
    (scaleRoot_column_le p.reduced_valid.toOrdered k source).trans_lt hBefore
  obtain ⟨rootCopy⟩ := s.prior_effective_occurrence history hLast hRootRight hRootBefore
  have sourcePath := hNormal.parentPath_scaleRoot k source hReal
  have targetPath := s.recorded_scale_path history hLast hStartRun sourcePath
    (scaleRoot_same_block p.reduced_valid.toOrdered k source) hRootRight hBefore copy rootCopy
  have hRoots := scaleRoot_eq_of_scale_path s.ambient_valid.toOrdered targetPath
  refine ⟨rootCopy, targetPath, hRoots, ?_⟩
  rw [hRoots]
  exact (scaleRoot_column_le s.ambient_valid.toOrdered k rootCopy.keyNode).trans_eq rootCopy.keyNode_column

theorem DynamicBlockState.recorded_scale_root_bound
    {source : (Frame.ofMountain p.reduced).Node} {k : Nat}
    (hReal : Real source)
    (hRootRight : p.root.column < (scaleRoot p.reduced_valid.toOrdered k source).1.val)
    (hBefore : source.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source ambient) :
    (scaleRoot s.ambient_valid.toOrdered k copy.keyNode).1.val ≤
      (scaleRoot p.reduced_valid.toOrdered k source).1.val +
        block * (p.reduced.size - 1 - p.root.column) := by
  obtain ⟨_, _, _, hBound⟩ := s.recorded_scale_root_transport history hLast hStartRun
    hReal hRootRight hBefore copy
  exact hBound

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.parentPath_scaleRoot
#print axioms OmegaY.Geometry.Frame.scaleRoot_eq_of_scale_path
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_scale_root_transport
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_scale_root_bound
