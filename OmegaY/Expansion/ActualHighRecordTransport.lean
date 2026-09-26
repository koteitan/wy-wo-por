/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighRecordTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighRootCandidateRecognition
import OmegaY.Expansion.HistoryRawInvariants
import OmegaY.Expansion.SourceRecordTransfer

/-!
# Transporting actual source records across all columns at a high cut

The image of a source frontier is the true target frontier at that same
cut. Good columns retain their index; the root column becomes the current
block-start last column; bad columns use the actual block displacement.
Every mapped edge is proved from recorded copy executions or the actual
root-boundary correspondence, before numerical recognition in new columns.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace DynamicBlockState

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
  (s : DynamicBlockState p block start references next ambient)

include s in
private theorem recordColumn_bound (sourceColumn : Nat) (hBefore : sourceColumn < next) :
    copiedColumnIndex p.root.column (block * (p.reduced.size - 1 - p.root.column)) sourceColumn <
      ambient.size := by
  have hSize := s.size_eq
  have hLower := s.next_lower
  unfold copiedColumnIndex
  split <;> omega

/-- The actual, inclusive target frontier in the column used by copying. -/
noncomputable def recordFrontier (cut : Row) (hOne : (1 : Row) ≤ cut)
    (source : (Frame.ofMountain p.reduced).Node) (hBefore : source.1.val < next) :
    (Frame.ofMountain ambient).Node :=
  frontierAt s.ambient_valid.toOrdered cut hOne
    ⟨copiedColumnIndex p.root.column (block * (p.reduced.size - 1 - p.root.column)) source.1.val,
      s.recordColumn_bound source.1.val hBefore⟩

theorem recordFrontier_column (cut : Row) (hOne : (1 : Row) ≤ cut)
    (source : (Frame.ofMountain p.reduced).Node) (hBefore : source.1.val < next) :
    (s.recordFrontier cut hOne source hBefore).1.val =
      copiedColumnIndex p.root.column (block * (p.reduced.size - 1 - p.root.column)) source.1.val :=
  congrArg Fin.val (frontierAt_spec s.ambient_valid.toOrdered hOne _).1

theorem recordFrontier_at (cut : Row) (hOne : (1 : Row) ≤ cut)
    (source : (Frame.ofMountain p.reduced).Node) (hBefore : source.1.val < next) :
    frontierAt s.ambient_valid.toOrdered cut hOne (s.recordFrontier cut hOne source hBefore).1 =
      s.recordFrontier cut hOne source hBefore := by
  unfold recordFrontier
  rw [(frontierAt_spec s.ambient_valid.toOrdered hOne _).1]

theorem recordFrontier_real (cut : Row) (hOne : (1 : Row) ≤ cut)
    (source : (Frame.ofMountain p.reduced).Node) (hBefore : source.1.val < next) :
    Real (s.recordFrontier cut hOne source hBefore) :=
  (frontierAt_spec s.ambient_valid.toOrdered hOne _).2.1

theorem recordFrontier_fixed {cut : Row} (hOne : (1 : Row) ≤ cut)
    {source : (Frame.ofMountain p.reduced).Node} (hBefore : source.1.val < next)
    (hFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hOne source.1 = source)
    (hFixed : source.1.val < p.root.column) :
    Frame.ref (s.recordFrontier cut hOne source hBefore) = Frame.ref source ∧
      (Frame.ofMountain ambient).cell (s.recordFrontier cut hOne source hBefore) =
        (Frame.ofMountain p.reduced).cell source := by
  have hMappedFront := frontierAt_of_same_column (build_normal_of_success p.reduced_build).toOrdered
    s.ambient_valid.toOrdered hOne hFront (s.base_ambient.mapNode_ref source)
    (s.base_ambient _ source.1.isLt)
  have hc : (s.base_ambient.mapNode source).1 = (s.recordFrontier cut hOne source hBefore).1 := by
    apply Fin.ext
    rw [s.base_ambient.mapNode_column, s.recordFrontier_column]
    simp only [copiedColumnIndex, if_pos hFixed]
  have he : s.base_ambient.mapNode source = s.recordFrontier cut hOne source hBefore := by
    rw [hc, s.recordFrontier_at] at hMappedFront
    exact hMappedFront.symm
  exact ⟨he ▸ s.base_ambient.mapNode_ref source, he ▸ s.base_ambient.mapNode_cell source⟩

theorem recordFrontier_copied (hLast : 1 < last)
    {cut : Row} (hOne : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    {source : (Frame.ofMountain p.reduced).Node} (hBefore : source.1.val < next)
    (hFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hOne source.1 = source)
    (hRight : p.root.column < source.1.val)
    (copy : EffectiveCopyOccurrence p block start references source ambient) :
    Frame.ref (s.recordFrontier cut hOne source hBefore) = copy.outputRef ∧
      (Frame.ofMountain ambient).cell (s.recordFrontier cut hOne source hBefore) = copy.read.outputCell := by
  have hSpec := frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered hOne source.1
  obtain ⟨actual, hRef, hCell, hActualFront⟩ := copy.frontierAt_high_of_bounds hLast s.ambient_valid
    hOne hHigh (hFront ▸ hSpec.2.1) (hFront ▸ hSpec.2.2.1)
    (by simpa only [hFront] using hSpec.2.2.2.2)
  have hc : actual.1 = (s.recordFrontier cut hOne source hBefore).1 := by
    apply Fin.ext
    rw [s.recordFrontier_column]
    simp only [copiedColumnIndex, if_neg (not_lt_of_ge hRight.le)]
    exact (congrArg Ref.column hRef).trans copy.source_column
  have he : actual = s.recordFrontier cut hOne source hBefore := by
    rw [hc, s.recordFrontier_at] at hActualFront
    exact hActualFront.symm
  exact ⟨he ▸ hRef, he ▸ hCell⟩

/-- The root image is recovered from the genuine outer run. Its outgoing
source P is fixed, and becomes an actual raw edge from the image; its
numerical value is equal even if its own lower row has changed. -/
theorem recordFrontier_root (hLast : 1 < last) {copies : Nat}
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {cut : Row} (hOne : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    {source : (Frame.ofMountain p.reduced).Node} (hBefore : source.1.val < next)
    (hFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hOne source.1 = source)
    (hRoot : source.1.val = p.root.column) :
    (Frame.ofMountain ambient).value (s.recordFrontier cut hOne source hBefore) =
      (Frame.ofMountain p.reduced).value source ∧
    (∀ parent, (Frame.ofMountain p.reduced).P source = some parent →
      parent.1.val < p.root.column ∧
      RawRefEdge ambient (Frame.ref (s.recordFrontier cut hOne source hBefore)) (Frame.ref parent)) := by
  obtain ⟨_, boundary, hBoundaryColumn, _, hBoundaryFront, _, hParents, _⟩ :=
    p.blocks_reduced_root_frontier_correspondence hLast hStartRun hOne hHigh hRoot hFront
  have hValue := p.blocks_root_value_at_frontiers hLast hStartRun s.start_valid
    hOne hHigh hRoot hFront hBoundaryColumn hBoundaryFront
  have hMappedFront := frontierAt_of_same_column s.start_valid.toOrdered s.ambient_valid.toOrdered
    hOne hBoundaryFront (s.start_preserved.mapNode_ref boundary) (s.start_preserved _ boundary.1.isLt)
  have hc : (s.start_preserved.mapNode boundary).1 = (s.recordFrontier cut hOne source hBefore).1 := by
    apply Fin.ext
    rw [s.start_preserved.mapNode_column, s.recordFrontier_column]
    simp only [copiedColumnIndex, hRoot, lt_self_iff_false, if_false]
    have hSize := s.start_size
    omega
  have he : s.start_preserved.mapNode boundary = s.recordFrontier cut hOne source hBefore := by
    rw [hc, s.recordFrontier_at] at hMappedFront
    exact hMappedFront.symm
  refine ⟨(congrArg Cell.value (he ▸ s.start_preserved.mapNode_cell boundary)).trans hValue, ?_⟩
  intro parent hParent
  obtain ⟨hFixed, hEdge, _⟩ := hParents parent hParent
  refine ⟨hFixed, ?_⟩
  have hRef : Frame.ref (s.recordFrontier cut hOne source hBefore) = Frame.ref boundary :=
    he ▸ s.start_preserved.mapNode_ref boundary
  simpa only [hRef] using hEdge.preserve s.start_preserved

/-- Every actual source record edge at a high common cut maps to one
genuine stored edge, including the edge out of the changing root boundary.
The copied graph's numerical P is not used. -/
theorem high_record_parent
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {copies : Nat}
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {cut : Row} (hOne : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    {source parent : (Frame.ofMountain p.reduced).Node}
    (hBefore : source.1.val < next) (hParentBefore : parent.1.val < next)
    (hFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hOne source.1 = source)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent) :
    (Frame.ofMountain ambient).rawParent (s.recordFrontier cut hOne source hBefore) =
      some (s.recordFrontier cut hOne parent hParentBefore) := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hParentLeft := Frame.P_column_lt hNormal.toOrdered hParent
  have hReal : Real source := hFront ▸ (frontierAt_spec hNormal.toOrdered hOne source.1).2.1
  have hParentFront := hNormal.frontierAt_parent hOne source.1 (by simpa only [hFront] using hParent)
  by_cases hFixed : source.1.val < p.root.column
  · have hParentFixed := hParentLeft.trans hFixed
    have hSourceRef := (s.recordFrontier_fixed hOne hBefore hFront hFixed).1
    have hParentRef := (s.recordFrontier_fixed hOne hParentBefore hParentFront hParentFixed).1
    exact ((RawRefEdge.of_rawParent ((hNormal.rawParent_eq_P hReal).trans hParent)).preserve
      s.base_ambient).rawParent hSourceRef hParentRef
  · by_cases hRoot : source.1.val = p.root.column
    · obtain ⟨_, hParents⟩ := s.recordFrontier_root hLast hStartRun hOne hHigh hBefore hFront hRoot
      obtain ⟨hParentFixed, hEdge⟩ := hParents parent hParent
      have hParentRef := (s.recordFrontier_fixed hOne hParentBefore hParentFront hParentFixed).1
      exact hEdge.rawParent rfl hParentRef
    · have hRight : p.root.column < source.1.val := lt_of_le_of_ne (Nat.le_of_not_gt hFixed) (Ne.symm hRoot)
      obtain ⟨sourceCopy⟩ := s.prior_effective_occurrence history hLast hRight hBefore
      have hSourceRef := (s.recordFrontier_copied hLast hOne hHigh hBefore hFront hRight sourceCopy).1
      by_cases hParentFixed : parent.1.val < p.root.column
      · have hParentRef := (s.recordFrontier_fixed hOne hParentBefore hParentFront hParentFixed).1
        exact (s.recorded_fixed_parent history hLast hParent hRight hBefore hParentFixed sourceCopy).1.rawParent
          hSourceRef hParentRef
      · by_cases hParentRoot : parent.1.val = p.root.column
        · obtain ⟨endpoint, hEdge⟩ := s.recorded_root_parent_exists
            history hLast hStartRun hParent hParentRoot hBefore sourceCopy
          obtain ⟨node, hNodeRef, _⟩ := Canonical.frame_node_of_cellAt endpoint.result_read
          have hRawEdge := hEdge.rawParent hSourceRef hNodeRef
          obtain ⟨hRaw, hFather⟩ := s.raw_invariants_of_start_run history hLast hStartRun
          have hNodeFront := frontierAt_raw_parent_of_bound s.ambient_valid.toOrdered hRaw hFather hOne
            (s.recordFrontier cut hOne source hBefore).1
            (by rw [s.recordFrontier_at]; exact hRawEdge)
          have hEndpointColumn : endpoint.reference.column = start.size - 1 := by
            cases endpoint with
            | selected endpoint => exact endpoint.reference_column
            | highTail endpoint => exact endpoint.reference_column
          have hc : node.1 = (s.recordFrontier cut hOne parent hParentBefore).1 := by
            apply Fin.ext
            have hNodeColumn := (congrArg Ref.column hNodeRef).trans hEndpointColumn
            change node.1.val = start.size - 1 at hNodeColumn
            rw [s.recordFrontier_column]
            simp only [copiedColumnIndex, hParentRoot, lt_self_iff_false, if_false]
            have hSize := s.start_size
            omega
          have he : node = s.recordFrontier cut hOne parent hParentBefore := by
            rw [hc, s.recordFrontier_at] at hNodeFront
            exact hNodeFront.symm
          exact he ▸ hRawEdge
        · have hParentRight : p.root.column < parent.1.val :=
            lt_of_le_of_ne (Nat.le_of_not_gt hParentFixed) (Ne.symm hParentRoot)
          obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hParentRight hParentBefore
          have hParentRef := (s.recordFrontier_copied hLast hOne hHigh hParentBefore
            hParentFront hParentRight parentCopy).1
          exact (s.recorded_effective_parent history hLast hParent hParentRight hBefore
            sourceCopy parentCopy).rawParent hSourceRef hParentRef

/-- Entire source P-record paths are transported from the actual run,
including root crossings and their fixed good-prefix tails. -/
theorem high_record_path
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {copies : Nat}
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {cut : Row} (hOne : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    {source parent : (Frame.ofMountain p.reduced).Node}
    (hBefore : source.1.val < next) (hParentBefore : parent.1.val < next)
    (hFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hOne source.1 = source)
    (path : ParentPath (Frame.ofMountain p.reduced) source parent) :
    RawRefPath ambient (Frame.ref (s.recordFrontier cut hOne source hBefore))
      (Frame.ref (s.recordFrontier cut hOne parent hParentBefore)) := by
  have hNormal := build_normal_of_success p.reduced_build
  induction path with
  | refl source => exact .refl _
  | @cons source middle parent hEdge tail ih =>
    have hMiddleBefore := (Frame.P_column_lt hNormal.toOrdered hEdge).trans hBefore
    have hMiddleFront := hNormal.frontierAt_parent hOne source.1 (by simpa only [hFront] using hEdge)
    exact .cons (RawRefEdge.of_rawParent
      (s.high_record_parent history hLast hStartRun hOne hHigh hBefore hMiddleBefore hFront hEdge))
      (ih hMiddleBefore hParentBefore hMiddleFront)

end DynamicBlockState
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recordFrontier_fixed
#print axioms OmegaY.Expansion.DynamicBlockState.recordFrontier_copied
#print axioms OmegaY.Expansion.DynamicBlockState.recordFrontier_root
#print axioms OmegaY.Expansion.DynamicBlockState.high_record_parent
#print axioms OmegaY.Expansion.DynamicBlockState.high_record_path
