/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveEdgeColumns.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFiniteEdgeKeys

/-!
# Actual endpoint columns of ordinary effective copied edges

The stored target father is recovered from recorded execution in the
good/root/right cases. Its column, and the effective child's column, obey
the same literal map used for finite key supports. No target father
correspondence, output normality, or numerical comparison is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient result : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)

include s history hLast hStartRun

/-- Good fathers are retained, root fathers use the actual boundary
reference, and right fathers are the previously recorded effective copy. -/
theorem DynamicBlockState.recorded_parent_column
    {source parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hBefore : source.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source ambient) :
    ∃ targetParent : (Frame.ofMountain ambient).Node,
      (Frame.ofMountain ambient).rawParent copy.keyNode = some targetParent ∧
      targetParent.1.val = copiedKeyColumn p.root.column
        (block * (p.reduced.size - 1 - p.root.column)) parent.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRight : p.root.column < source.1.val := copy.state.next_lower
  rcases Nat.lt_trichotomy parent.1.val p.root.column with hGood | hRoot | hParentRight
  · let preserved := s.base_preserved.trans s.start_preserved
    have hEdge := (s.recorded_fixed_parent history hLast hParent hRight hBefore hGood copy).1
    refine ⟨preserved.mapNode parent, hEdge.rawParent copy.keyNode_ref (preserved.mapNode_ref parent), ?_⟩
    rw [preserved.mapNode_column, copiedKeyColumn, if_pos hGood]
  · obtain ⟨endpoint, hEdge⟩ :=
      s.recorded_root_parent_exists history hLast hStartRun hParent hRoot hBefore copy
    refine ⟨endpoint.keyNode, hEdge.rawParent copy.keyNode_ref endpoint.keyNode_ref, ?_⟩
    have hColumn := (congrArg Ref.column endpoint.keyNode_ref).trans endpoint.reference_column
    change endpoint.keyNode.1.val = start.size - 1 at hColumn
    rw [hColumn, copiedKeyColumn, if_neg (by omega), hRoot]
    exact s.boundary_copy_index.symm
  · have hParentBefore : parent.1.val < next := (P_column_lt hNormal.toOrdered hParent).trans hBefore
    obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hParentRight hParentBefore
    have hEdge := s.recorded_effective_parent history hLast hParent hParentRight hBefore copy parentCopy
    refine ⟨parentCopy.keyNode, hEdge.rawParent copy.keyNode_ref parentCopy.keyNode_ref, ?_⟩
    rw [parentCopy.keyNode_column, copiedKeyColumn, if_neg (by omega)]

/-- Exact endpoints for the edge already classified by its effective
lower. Full-prefix retention preserves the recovered stored father. -/
theorem DynamicBlockState.preserved_effective_edge_columns
    (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (hBefore : source.lower.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source.lower ambient)
    (preserved : PreservesColumns ambient result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hLower : Frame.ref edge.lower = (copy.extend preserved).outputRef) :
    edge.parent.1.val = copiedKeyColumn p.root.column
      (block * (p.reduced.size - 1 - p.root.column)) source.parent.1.val ∧
    edge.lower.1.val = copiedKeyColumn p.root.column
      (block * (p.reduced.size - 1 - p.root.column)) source.lower.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  have hParent := (hNormal.rawParent_eq_P source.lower_real).symm.trans source.parent_eq
  obtain ⟨targetParent, hRaw, hColumn⟩ :=
    s.recorded_parent_column history hLast hStartRun hParent hBefore copy
  have hSame : edge.lower = (copy.extend preserved).keyNode := Executable.ref_injective _
    (hLower.trans (copy.extend preserved).keyNode_ref.symm)
  have hMappedLower : edge.lower = preserved.mapNode copy.keyNode :=
    hSame.trans (copy.keyNode_extend preserved)
  have hActual : (Frame.ofMountain result).rawParent edge.lower = some (preserved.mapNode targetParent) := by
    rw [hMappedLower]
    exact preserved.mapNode_rawParent hRaw
  have hParentSame : edge.parent = preserved.mapNode targetParent :=
    Option.some.inj (edge.parent_eq.symm.trans hActual)
  refine ⟨?_, ?_⟩
  · rw [hParentSame, preserved.mapNode_column]
    exact hColumn
  · rw [hSame, (copy.extend preserved).keyNode_column, copiedKeyColumn,
      if_neg (not_lt_of_ge copy.state.next_lower.le)]

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_parent_column
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_effective_edge_columns
