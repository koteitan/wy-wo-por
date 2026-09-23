/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootEndpointScale.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BoundaryScalePaths
import OmegaY.Expansion.ActualHighRootDepth
import OmegaY.Expansion.ActualCommonMarkerBands

/-!
# Actual root-boundary subdivisions preserve retained scales

Low root endpoints have the already constructed path to the original root;
the highest endpoint and high-tail endpoints have their actual fixed-parent
edge. The true endpoint lies between the source root and its actual upper.
This proves its highest difference from the original parent is unchanged.
Raw B and positive backfill then put every subdivision in the retained
scale forest. No target normality, path, or same-block condition is assumed.
-/

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

include s hLast

theorem DynamicBlockState.root_endpoint_below_upper
    {root parent upper : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references root ambient)
    (hParent : (Frame.ofMountain p.reduced).P root = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper root = some upper) :
    endpoint.target.row < (Frame.ofMountain p.reduced).height upper := by
  have hNormal := build_normal_of_success p.reduced_build
  have hReal : Real root := real_of_value_pos hNormal.toOrdered
    ((P_value hNormal.toOrdered hParent).1.trans (P_value hNormal.toOrdered hParent).2)
  rcases Nat.lt_trichotomy root.2.val p.root.index with hBefore | hAt | hAfter
  · have hBelow := s.low_root_endpoint_below hLast endpoint hReal hBefore hUpper
    obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp endpoint.start_read
    have hColumn : start[start.size - 1]? = some nodes := by
      simpa only [endpoint.reference_column] using hNodes
    exact below_lookup_row_lt hColumn hBelow (lookup_ok_iff.mpr ⟨nodes, hNodes, hRead⟩)
  · have hRootRef : Frame.ref root = p.root := congrArg₂ Ref.mk endpoint.source_column hAt
    have hBarrier := p.reduced_badRoot_upper_bound hLast hRootRef hUpper
    cases endpoint with
    | selected selected => exact selected.target_below.trans_le (selected.cap_top.trans hBarrier)
    | highTail tail =>
      have hRootCell : (Frame.ofMountain p.reduced).cell root = p.rootCell := Except.ok.inj
        ((cellAt_of_frame_node p.reduced root).symm.trans (by simpa only [hRootRef] using p.restored_root))
      have hRootRow := congrArg Cell.row hRootCell
      exact False.elim ((not_lt_of_ge (hRootRow ▸ tail.source_high)) (p.root_row_lt_top hLast))
  · have hHigh := p.root_node_after_badRoot_is_high hLast endpoint.source_column hAfter
    cases endpoint with
    | selected selected => exact False.elim ((not_le_of_gt selected.source_below_lastTop) hHigh)
    | highTail tail =>
      rw [EffectiveRootEndpoint.target, tail.target_row]
      have hB := (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
      exact (Row.lt_B _ _).trans_eq hB.symm

/-- Even the root endpoint's potentially subdivided edge preserves the
endpoint jump, as a consequence of the actual upper-selection interval. -/
theorem DynamicBlockState.root_endpoint_parent_jump
    {root parent : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references root ambient)
    (hParent : (Frame.ofMountain p.reduced).P root = some parent) :
    Row.jump endpoint.target.row ((Frame.ofMountain p.reduced).height parent) =
      Row.jump ((Frame.ofMountain p.reduced).height root) ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hParent
  have hB : F.height upper = Row.B (F.height root) (F.height parent) :=
    (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
  have hHigh := s.root_endpoint_below_upper hLast endpoint hParent hUpper
  change endpoint.target.row < F.height upper at hHigh
  rw [hB] at hHigh
  have hInside : Row.jump (F.height root) endpoint.target.row ≤ Row.jump (F.height root) (F.height parent) :=
    Row.jump_le_of_lt_bump endpoint.target_lower hHigh
  have hMax := Row.jump_max (P_height_le hNormal.toOrdered hParent) endpoint.target_lower
  rw [Row.jump_comm (F.height parent) (F.height root), max_eq_left hInside] at hMax
  exact (Row.jump_comm endpoint.target.row (F.height parent)).trans hMax

include history hStartRun

omit history in
/-- The source root edge is realized by a genuine stored path to its
original good-part parent. The three source-index cases are all actual. -/
theorem DynamicBlockState.root_endpoint_parent_path
    {root parent : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references root ambient)
    (hParent : (Frame.ofMountain p.reduced).P root = some parent) :
    RawRefPath ambient endpoint.reference (Frame.ref parent) := by
  let F := Frame.ofMountain p.reduced
  let preserved := s.base_preserved.trans s.start_preserved
  have hNormal := build_normal_of_success p.reduced_build
  have hReal : Real root := real_of_value_pos hNormal.toOrdered
    ((P_value hNormal.toOrdered hParent).1.trans (P_value hNormal.toOrdered hParent).2)
  rcases Nat.lt_trichotomy root.2.val p.root.index with hBefore | hAt | hAfter
  · have hPrefix := (s.low_root_endpoint_path hLast hStartRun endpoint hReal hBefore).preserve s.start_preserved
    have hOld := (RawRefEdge.of_rawParent ((hNormal.rawParent_eq_P hReal).trans hParent)).preserve preserved
    exact hPrefix.trans (.cons hOld (.refl _))
  · obtain ⟨node, hNodeRef, _⟩ := Canonical.frame_node_of_cellAt endpoint.start_read
    have hRaw := s.highest_root_endpoint_rawParent hLast hStartRun endpoint hAt hNodeRef
    rw [hParent, Option.map_some] at hRaw
    have hEdge := (RawRefEdge.of_rawParent hRaw).preserve s.start_preserved
    have hEdge' : RawRefEdge ambient endpoint.reference (Frame.ref parent) := by
      simpa only [hNodeRef, s.base_preserved.mapNode_ref] using hEdge
    exact .cons hEdge' (.refl _)
  · have hHigh := p.root_node_after_badRoot_is_high hLast endpoint.source_column hAfter
    have hOne := Frame.one_le_height hNormal.toOrdered hReal
    have hFront := frontierAt_of_height_eq hNormal.toOrdered hOne (rfl : F.height root = F.height root)
    obtain ⟨hValid, actual, hActualColumn, _, _, hActualRow, hParents, _⟩ :=
      p.blocks_reduced_root_frontier_correspondence hLast hStartRun hOne hHigh endpoint.source_column hFront
    have hRow : endpoint.target.row = F.height root := by
      cases endpoint with
      | selected selected => exact False.elim ((not_le_of_gt selected.source_below_lastTop) hHigh)
      | highTail tail => exact tail.target_row
    obtain ⟨node, hNodeRef, hNodeCell⟩ := Canonical.frame_node_of_cellAt endpoint.start_read
    have hSame : actual = node := Frame.node_eq_of_column_height s.start_valid.toOrdered
      (Fin.ext (hActualColumn.trans ((congrArg Ref.column hNodeRef).trans endpoint.reference_column).symm))
      ((hActualRow hHigh).trans (hRow.symm.trans (congrArg Cell.row hNodeCell).symm))
    have hEdge := (hParents parent hParent).2.1.preserve s.start_preserved
    have hEdge' : RawRefEdge ambient endpoint.reference (Frame.ref parent) := by
      simpa only [hSame, hNodeRef] using hEdge
    exact .cons hEdge' (.refl _)

/-- Every actual subdivision of a retained source root edge remains in
the same scale forest, with no target same-block premise. -/
theorem DynamicBlockState.root_endpoint_scale_path
    {root parent : (Frame.ofMountain p.reduced).Node} {k : Nat}
    (endpoint : EffectiveRootEndpoint p start references root ambient)
    (hParent : (Frame.ofMountain p.reduced).P root = some parent)
    (hScale : Row.jump ((Frame.ofMountain p.reduced).height root)
      ((Frame.ofMountain p.reduced).height parent) ≤ k) :
    Relation.ReflTransGen (fun u v => (Frame.ofMountain ambient).scaleParent k u = some v)
      endpoint.keyNode ((s.base_preserved.trans s.start_preserved).mapNode parent) := by
  let preserved := s.base_preserved.trans s.start_preserved
  have hNormal := build_normal_of_success p.reduced_build
  have hReal : Real root := real_of_value_pos hNormal.toOrdered
    ((P_value hNormal.toOrdered hParent).1.trans (P_value hNormal.toOrdered hParent).2)
  apply (s.root_endpoint_parent_path hLast hStartRun endpoint hParent).scale_path
    s.ambient_valid (s.mountainSums_of_start_run history hLast hStartRun)
    (s.mountainRawGeometry_of_start_run history hLast hStartRun).rawRowGeometry
    endpoint.keyNode_ref (preserved.mapNode_ref parent) (endpoint.keyNode_real s.ambient_valid hReal)
  rw [endpoint.keyNode_height, preserved.mapNode_height]
  exact (s.root_endpoint_parent_jump hLast endpoint hParent).le.trans hScale

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.root_endpoint_below_upper
#print axioms OmegaY.Expansion.DynamicBlockState.root_endpoint_parent_jump
#print axioms OmegaY.Expansion.DynamicBlockState.root_endpoint_parent_path
#print axioms OmegaY.Expansion.DynamicBlockState.root_endpoint_scale_path
