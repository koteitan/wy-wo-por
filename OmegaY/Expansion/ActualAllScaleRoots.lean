/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualAllScaleRoots.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootEndpointScale

/-!
# All-scale root bounds for actual ordinary effective copies

Good columns remain fixed and the root/bad columns move by the real block
shift. Every scale root is handled: right roots by ordinary effective
edges, root-column sources by actual boundary subdivisions, and good roots
by exact complete-prefix preservation. Only actual source/loop/copy data
are inputs; target root inequalities and target normality are not inputs.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

def copiedKeyColumn (root shift column : Nat) : Nat :=
  if column < root then column else column + shift

theorem copiedKeyColumn_strictMono (root shift : Nat) : StrictMono (copiedKeyColumn root shift) := by
  intro a b hab
  unfold copiedKeyColumn
  split_ifs <;> omega

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)

private theorem fixed_scale_root_column (k : Nat) (source : (Frame.ofMountain p.reduced).Node) :
    (scaleRoot s.ambient_valid.toOrdered k ((s.base_preserved.trans s.start_preserved).mapNode source)).1.val =
      (scaleRoot p.reduced_valid.toOrdered k source).1.val := by
  rw [(s.base_preserved.trans s.start_preserved).mapNode_scaleRoot
    p.reduced_valid.toOrdered s.ambient_valid.toOrdered]
  exact (s.base_preserved.trans s.start_preserved).mapNode_column _

include s history hLast hStartRun

/-- Every selected or high-tail representative of a root-column source
satisfies the computed root bound at every scale. The possible extra
subdivision vertices are controlled by the actual root path theorem. -/
theorem DynamicBlockState.root_endpoint_scale_root_bound
    {root : (Frame.ofMountain p.reduced).Node} (hReal : Real root)
    (endpoint : EffectiveRootEndpoint p start references root ambient) (k : Nat) :
    (scaleRoot s.ambient_valid.toOrdered k endpoint.keyNode).1.val ≤
      copiedKeyColumn p.root.column (block * (p.reduced.size - 1 - p.root.column))
        (scaleRoot p.reduced_valid.toOrdered k root).1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  cases hp : (Frame.ofMountain p.reduced).scaleParent k root with
  | none =>
    rw [scaleRoot_eq_of_none p.reduced_valid.toOrdered hp]
    simp only [copiedKeyColumn, endpoint.source_column, Nat.lt_irrefl, ↓reduceIte]
    exact (scaleRoot_column_le s.ambient_valid.toOrdered k endpoint.keyNode).trans_eq
      (((congrArg Ref.column endpoint.keyNode_ref).trans endpoint.reference_column).trans s.boundary_copy_index.symm)
  | some parent =>
    obtain ⟨hRaw, hScale⟩ := scaleParent_some_iff.mp hp
    have hParent : (Frame.ofMountain p.reduced).P root = some parent :=
      (hNormal.rawParent_eq_P hReal).symm.trans hRaw
    have hGood : (scaleRoot p.reduced_valid.toOrdered k parent).1.val < p.root.column :=
      (scaleRoot_column_le p.reduced_valid.toOrdered k parent).trans_lt
        ((P_column_lt hNormal.toOrdered hParent).trans_eq endpoint.source_column)
    have hPath := s.root_endpoint_scale_path history hLast hStartRun endpoint hParent hScale
    have hRoots := scaleRoot_eq_of_scale_path s.ambient_valid.toOrdered hPath
    rw [scaleRoot_eq_of_parent p.reduced_valid.toOrdered hp, copiedKeyColumn, if_pos hGood,
      hRoots, fixed_scale_root_column s]

/-- All finite coordinates of every real ordinary effective source are
bounded by the corresponding genuinely computed source roots, relabeled
by the actual block's column map. This includes root/good crossings. -/
theorem DynamicBlockState.recorded_all_scale_root_bound
    {source : (Frame.ofMountain p.reduced).Node}
    (hReal : Real source) (hBefore : source.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source ambient) (k : Nat) :
    (scaleRoot s.ambient_valid.toOrdered k copy.keyNode).1.val ≤
      copiedKeyColumn p.root.column (block * (p.reduced.size - 1 - p.root.column))
        (scaleRoot p.reduced_valid.toOrdered k source).1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRaw := (s.mountainRawGeometry_of_start_run history hLast hStartRun).rawRowGeometry
  have hSourceRight : p.root.column < source.1.val := copy.state.next_lower
  cases hp : (Frame.ofMountain p.reduced).scaleParent k source with
  | none =>
    rw [scaleRoot_eq_of_none p.reduced_valid.toOrdered hp, copiedKeyColumn,
      if_neg (Nat.not_lt_of_ge hSourceRight.le)]
    exact (scaleRoot_column_le s.ambient_valid.toOrdered k copy.keyNode).trans_eq copy.keyNode_column
  | some parent =>
    obtain ⟨hParentRaw, hScale⟩ := scaleParent_some_iff.mp hp
    have hParent : (Frame.ofMountain p.reduced).P source = some parent :=
      (hNormal.rawParent_eq_P hReal).symm.trans hParentRaw
    have hParentReal : Real parent := real_of_value_pos hNormal.toOrdered (P_value hNormal.toOrdered hParent).1
    have hParentBefore : parent.1.val < next := (P_column_lt hNormal.toOrdered hParent).trans hBefore
    rw [scaleRoot_eq_of_parent p.reduced_valid.toOrdered hp]
    rcases Nat.lt_trichotomy parent.1.val p.root.column with hGood | hRoot | hRight
    · let preserved := s.base_preserved.trans s.start_preserved
      have hEdge := (s.recorded_fixed_parent history hLast hParent hSourceRight hBefore hGood copy).1
      have hActualParent := hEdge.rawParent copy.keyNode_ref (preserved.mapNode_ref parent)
      have hJump := copy.raw_parent_jump hLast hRaw hParent hActualParent
      have hRoots := scaleRoot_eq_of_raw s.ambient_valid.toOrdered hActualParent (hJump.le.trans hScale)
      have hRootGood : (scaleRoot p.reduced_valid.toOrdered k parent).1.val < p.root.column :=
        (scaleRoot_column_le p.reduced_valid.toOrdered k parent).trans_lt hGood
      rw [hRoots, copiedKeyColumn, if_pos hRootGood, fixed_scale_root_column s]
    · obtain ⟨endpoint, hEdge⟩ := s.recorded_root_parent_exists history hLast hStartRun hParent hRoot hBefore copy
      have hActualParent := hEdge.rawParent copy.keyNode_ref endpoint.keyNode_ref
      have hJump := copy.raw_parent_jump hLast hRaw hParent hActualParent
      rw [scaleRoot_eq_of_raw s.ambient_valid.toOrdered hActualParent (hJump.le.trans hScale)]
      exact s.root_endpoint_scale_root_bound history hLast hStartRun hParentReal endpoint k
    · obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hRight hParentBefore
      have hScaleParent := s.recorded_scale_parent history hLast hStartRun hParent hScale hRight hBefore copy parentCopy
      rw [scaleRoot_eq_of_parent s.ambient_valid.toOrdered hScaleParent]
      exact DynamicBlockState.recorded_all_scale_root_bound hParentReal hParentBefore parentCopy k
termination_by source.1.val
decreasing_by exact P_column_lt (build_normal_of_success p.reduced_build).toOrdered hParent

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.copiedKeyColumn_strictMono
#print axioms OmegaY.Expansion.DynamicBlockState.root_endpoint_scale_root_bound
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_all_scale_root_bound
