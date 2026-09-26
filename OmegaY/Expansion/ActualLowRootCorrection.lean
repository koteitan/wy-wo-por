/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowRootCorrection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowRootPathDepth
import OmegaY.Expansion.ActualIteratedLowBoundary
import OmegaY.Expansion.ActualFixedExitLift

/-!
# Nonnegative actual correction below the bad root

The root source index is strictly below the bad-root index. Its actual
boundary endpoint is identified with the strict selector at the original
root-upper row, using the real reference map and endpoint uniqueness.
The all-block selector path therefore starts at this very endpoint.

Raw frontier closure carries that path to the unchanged original root at
the packet's lifted cut. The same original node is also the source-event
frontier. Complete-prefix depth preservation at a common node, not equality
of the two cuts, identifies its absolute depth. The path length is the
nonnegative boundary correction and the copied child's depth increment.

The bad root itself and high-tail root sources are not claimed here.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem EffectiveRootEndpoint.source_column
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references source result) :
    source.1.val = p.root.column := by
  cases endpoint with
  | selected copy => exact copy.source_column
  | highTail copy => exact copy.source_column

/-- A root-prefix source strictly before the bad root has its actual
successor, irrespective of whether it has a numerical parent. -/
theorem Preparation.root_upper_of_before_badRoot
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {root : (Frame.ofMountain p.reduced).Node}
    (hColumn : root.1.val = p.root.column) (hBefore : root.2.val < p.root.index) :
    ∃ upper, (Frame.ofMountain p.reduced).upper root = some upper := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hBadColumn : badRoot.1 = root.1 :=
    Fin.ext ((congrArg Ref.column hBadRef).trans hColumn.symm)
  have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
  have hBadBound : p.root.index < F.length root.1 := by
    have hBound := badRoot.2.isLt
    change badRoot.2.val < F.length badRoot.1 at hBound
    simpa only [hBadColumn, hBadIndex] using hBound
  have hUpperBound : root.2.val + 1 < F.length root.1 := by omega
  change root.2.val + 1 < (Frame.ofMountain p.reduced).length root.1 at hUpperBound
  refine ⟨⟨root.1, ⟨root.2.val + 1, hUpperBound⟩⟩, ?_⟩
  simp only [Frame.upper, hUpperBound, ↓reduceDIte]

/-- The true endpoint, including an endpoint supplied through an abstract
constructor, is the actual strict selector at this low source upper. -/
theorem DynamicBlockState.low_root_endpoint_below
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {root upper : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references root ambient)
    (hReal : Real root) (hBefore : root.2.val < p.root.index)
    (hUpper : (Frame.ofMountain p.reduced).upper root = some upper) :
    below start (start.size - 1) ((Frame.ofMountain p.reduced).height upper) = .ok endpoint.reference := by
  let F := Frame.ofMountain p.reduced
  have hColumn : root.1.val = p.root.column := endpoint.source_column
  have hRootRef : Frame.ref root = ⟨p.root.column, root.2.val⟩ := congrArg₂ Ref.mk hColumn rfl
  have hInitialRead : Canonical.cellAt p.initial ⟨p.root.column, root.2.val⟩ = .ok (F.cell root) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, root.2.val⟩)
      p.initial_build p.reduced_build p.root_before_last).trans
      (by simpa only [hRootRef] using cellAt_of_frame_node p.reduced root)
  obtain ⟨nodes, hNodes, hRootRead⟩ := cellAt_ok_iff.mp hInitialRead
  have hPositive : (0 : Row) < (F.cell root).row :=
    Row.zero_lt_one.trans_le (Frame.one_le_height (build_normal_of_success p.reduced_build).toOrdered hReal)
  obtain ⟨a⟩ := s.actual_root_interval hLast hNodes hRootRead hBefore.le hPositive
  have haRoot : a.root = root := Executable.ref_injective F (a.root_ref.trans hRootRef.symm)
  obtain ⟨b, hbRoot, _, hCapMember⟩ := s.with_exact_root_cap hLast a
  have hbRoot' : b.root = root := hbRoot.trans haRoot
  have hCap : Row.bump (F.height root) b.degree = F.height upper :=
    b.cap_eq_upper_of_boundary hLast hCapMember hBefore (by simpa only [hbRoot'] using hUpper)
  obtain ⟨selected, hSelectedRef, _⟩ := s.exact_effective_root_reference hLast b hbRoot'.symm
  have hSame : selected.reference = endpoint.reference :=
    ((EffectiveRootEndpoint.selected selected).unique endpoint s.start_valid).1
  rw [← hSame, hSelectedRef, ← hCap]
  exact b.start_below

/-- All finite blocks supply an actual path from this exact low endpoint
to the original root reference. Selector identity is derived, not supplied. -/
theorem DynamicBlockState.low_root_endpoint_path
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next copies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {root : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references root ambient)
    (hReal : Real root) (hBefore : root.2.val < p.root.index) :
    RawRefPath start endpoint.reference (Frame.ref root) := by
  let F := Frame.ofMountain p.reduced
  have hColumn : root.1.val = p.root.column := endpoint.source_column
  have hRootLeft : root.1.val < front.length := hColumn ▸ p.root_before_last
  obtain ⟨upper, hUpper⟩ := p.root_upper_of_before_badRoot hColumn hBefore
  have hUpperLeft : upper.1.val < front.length :=
    (congrArg Fin.val (Frame.upper_spec hUpper).1).trans_lt hRootLeft
  have hInitialRoot : Canonical.cellAt p.initial (Frame.ref root) = .ok (F.cell root) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hRootLeft).trans
      (cellAt_of_frame_node p.reduced root)
  have hInitialUpper : Canonical.cellAt p.initial (Frame.ref upper) = .ok (F.cell upper) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hUpperLeft).trans
      (cellAt_of_frame_node p.reduced upper)
  obtain ⟨oldRoot, hOldRootRef, hOldRootCell⟩ := Canonical.frame_node_of_cellAt hInitialRoot
  obtain ⟨oldUpper, hOldUpperRef, hOldUpperCell⟩ := Canonical.frame_node_of_cellAt hInitialUpper
  have hUpperRef : Frame.ref oldUpper =
      ⟨(Frame.ref root).column, (Frame.ref root).index + 1⟩ := by
    rw [hOldUpperRef]
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  have hOldUpper : (Frame.ofMountain p.initial).upper oldRoot = some oldUpper :=
    Frame.upper_of_refs hOldRootRef hUpperRef
  have hOldReal : Real oldRoot := by
    change 0 < oldRoot.2.val
    have hIndex : oldRoot.2.val = root.2.val := congrArg Ref.index hOldRootRef
    exact hIndex ▸ hReal
  have hOldColumn : oldRoot.1.val = p.root.column :=
    (congrArg Ref.column hOldRootRef).trans hColumn
  have hOldBefore : oldRoot.2.val < p.root.index := by
    have hIndex : oldRoot.2.val = root.2.val := congrArg Ref.index hOldRootRef
    exact hIndex ▸ hBefore
  have hBelow := s.low_root_endpoint_below hLast endpoint hReal hBefore hUpper
  have hOldBelow : below start (start.size - 1) ((Frame.ofMountain p.initial).height oldUpper) =
      .ok endpoint.reference := by
    simpa only [Frame.height, hOldUpperCell] using hBelow
  have hPath := p.blocks_low_selected_path hLast hStartRun hOldReal hOldColumn hOldBefore hOldUpper hOldBelow
  simpa only [hOldRootRef] using hPath

/-- The actual path length gives both the old-boundary correction and
the copied child's absolute increment. No depth inequality is an input. -/
theorem LowRootPathDepth.correction_of_below_badRoot
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next copies : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {child lastBad root : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {childCopy : EffectiveCopyOccurrence p block start references child ambient}
    (data : LowRootPathDepth s child lastBad root sourceEvent childCopy)
    (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hBefore : root.2.val < p.root.index) :
    ∃ increment,
      parentDepth (eventParentMap s.start_valid.toOrdered data.start_width
          (start.size - 1) data.startEvent) (start.size - 1) =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
          (p.reduced.size - 1) sourceEvent) root.1.val + increment ∧
      parentDepth (eventParentMap s.ambient_valid.toOrdered data.copied.target_width
          (ambient.size - 1) data.copied.targetEvent) data.copied.childNode.1.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
          (p.reduced.size - 1) sourceEvent) child.1.val + increment := by
  have hNormal := build_normal_of_success p.reduced_build
  have hReal : Real root := data.source_root_frontier ▸
    (eventFrontier_spec hNormal.toOrdered sourceEvent root.1).2.1
  have hPath := s.low_root_endpoint_path hLast hStartRun data.rootCopy hReal hBefore
  let original := s.base_preserved.mapNode root
  have hOriginalRef : Frame.ref original = Frame.ref root := s.base_preserved.mapNode_ref root
  have hRaw := (p.blocks_raw_geometry_of_run hLast hStartRun).rawRowGeometry
  have hFather := (p.blocks_raw_father_bound_of_run hLast hStartRun).rawFatherUpperBound
  have hBound : start.size - 1 < start.size := by have := data.start_width; omega
  obtain ⟨increment, _, hOriginalFront, hDepth⟩ := hPath.event_depth s.start_valid.toOrdered hRaw hFather
    data.start_width hBound data.start_reference hOriginalRef data.start_frontier
      (by rw [data.start_column])
  have hFixedDepth := s.base_preserved.event_parentDepth_of_common_frontier hNormal s.start_valid.toOrdered
    hRaw hFather data.copied.source_width data.start_width data.source_root_frontier hOriginalFront
  have hBoundary : parentDepth (eventParentMap s.start_valid.toOrdered data.start_width
        (start.size - 1) data.startEvent) (start.size - 1) =
      parentDepth (eventParentMap hNormal.toOrdered data.copied.source_width
        (p.reduced.size - 1) sourceEvent) root.1.val + increment := by
    rw [data.start_column, s.base_preserved.mapNode_column] at hDepth
    exact hDepth.trans (congrArg (· + increment) hFixedDepth)
  refine ⟨increment, hBoundary, ?_⟩
  have hBalance := data.depth_balance
  rw [hBoundary] at hBalance
  omega

theorem LowRootPathDepth.depth_le_of_below_badRoot
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next copies : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {child lastBad root : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {childCopy : EffectiveCopyOccurrence p block start references child ambient}
    (data : LowRootPathDepth s child lastBad root sourceEvent childCopy)
    (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hBefore : root.2.val < p.root.index) :
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
        (p.reduced.size - 1) sourceEvent) child.1.val ≤
      parentDepth (eventParentMap s.ambient_valid.toOrdered data.copied.target_width
        (ambient.size - 1) data.copied.targetEvent) data.copied.childNode.1.val := by
  obtain ⟨increment, _, hDepth⟩ := data.correction_of_below_badRoot hLast hStartRun hBefore
  rw [hDepth]
  exact Nat.le_add_right _ _

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveRootEndpoint.source_column
#print axioms OmegaY.Expansion.Preparation.root_upper_of_before_badRoot
#print axioms OmegaY.Expansion.DynamicBlockState.low_root_endpoint_below
#print axioms OmegaY.Expansion.DynamicBlockState.low_root_endpoint_path
#print axioms OmegaY.Expansion.LowRootPathDepth.correction_of_below_badRoot
#print axioms OmegaY.Expansion.LowRootPathDepth.depth_le_of_below_badRoot
