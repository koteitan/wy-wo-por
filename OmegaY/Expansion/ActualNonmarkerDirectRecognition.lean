/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonmarkerDirectRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAnyHighDirectParent
import OmegaY.Expansion.ActualLowEffectiveCandidate

/-!
# Direct numerical recognition at every nonmarker height

The executable own-cell copy and the independently proved stored edge
have the same candidate-parent column when source Q equals source P.
Raw frontier closure identifies their endpoints, and actual backfill
supplies the strict value inequality. No height threshold or numerical
induction hypothesis is needed. Parentless source tops are also excluded
from every some-parent recognition obligation.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem EffectiveCopyOccurrence.rawParent_none_of_source_parent_none
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    (hLast : 1 < last) (hReal : Real source)
    (hParent : (Frame.ofMountain p.reduced).P source = none)
    {node : (Frame.ofMountain ambient).Node} (hRef : Frame.ref node = copy.outputRef) :
    (Frame.ofMountain ambient).rawParent node = none := by
  have hNormal := build_normal_of_success p.reduced_build
  have hTop : (Frame.ofMountain p.reduced).upper source = none := by
    cases hUpper : (Frame.ofMountain p.reduced).upper source with
    | none => rfl
    | some upper =>
      obtain ⟨parent, hP, _⟩ := hNormal.upper_step source upper hReal hUpper
      rw [hParent] at hP
      cases hP
  exact rawParent_none_of_upper_none (copy.top_upper_none hLast hTop hRef)

/-- All fixed, root-boundary and copied parent columns are handled by
their actual recorded edges. This theorem also covers low raised copies. -/
theorem DynamicBlockState.recorded_nonmarker_direct_parent_all
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {source parent : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hDirect : (Frame.ofMountain p.reduced).Q source = some parent)
    (hBefore : source.1.val < next)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index) :
    ∃ node father : (Frame.ofMountain ambient).Node,
      Frame.ref node = copy.outputRef ∧
      (Frame.ofMountain ambient).cell node = copy.read.outputCell ∧
      (Frame.ofMountain ambient).Q node = some father ∧
      (Frame.ofMountain ambient).rawParent node = some father ∧
      (Frame.ofMountain ambient).P node = some father := by
  let G := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hNoPrem := (copy.state.column_data_parent_inputs hLast source.1.isLt copy.data).1
  obtain ⟨copied, hCopy, hShape⟩ := copy.read.nonmarker_copy_execution hNoPrem hUnmarked
  obtain ⟨node, candidate, hRef, hCell, hQ, _, hColumn, _, _⟩ :=
    copy.candidate_frontier_all_columns s.ambient_valid hReal hCopy hShape hDirect
  have hNodeReal : Real node := by
    have hIndex := congrArg Ref.index hRef
    change node.2.val = copy.read.outputIndex at hIndex
    change 0 < node.2.val
    rw [hIndex]
    exact copy.read.output_real hReal
  have hStored : ∃ father : G.Node, G.rawParent node = some father ∧ candidate.1 = father.1 := by
    by_cases hFixed : parent.1.val < p.root.column
    · obtain ⟨hEdge, hRead⟩ := s.recorded_fixed_parent history hLast hParent
        copy.state.next_lower hBefore hFixed copy
      obtain ⟨father, hFatherRef, _⟩ := Canonical.frame_node_of_cellAt hRead
      refine ⟨father, hEdge.rawParent hRef hFatherRef, Fin.ext ?_⟩
      have hFatherColumn := congrArg Ref.column hFatherRef
      rw [if_pos hFixed] at hColumn
      exact hColumn.trans hFatherColumn.symm
    · by_cases hRoot : parent.1.val = p.root.column
      · obtain ⟨endpoint, hEdge⟩ := s.recorded_root_parent_exists
          history hLast hStartRun hParent hRoot hBefore copy
        obtain ⟨father, hFatherRef, _⟩ := Canonical.frame_node_of_cellAt endpoint.result_read
        have hEndpointColumn : endpoint.reference.column = start.size - 1 := by
          cases endpoint with
          | selected endpoint => exact endpoint.reference_column
          | highTail endpoint => exact endpoint.reference_column
        refine ⟨father, hEdge.rawParent hRef hFatherRef, Fin.ext ?_⟩
        have hFatherColumn : father.1.val = start.size - 1 :=
          (congrArg Ref.column hFatherRef).trans hEndpointColumn
        simp only [hRoot, lt_self_iff_false, ↓reduceIte] at hColumn
        exact hColumn.trans ((show p.root.column + block * (p.reduced.size - 1 - p.root.column) =
          start.size - 1 by rw [s.start_size]; omega).trans hFatherColumn.symm)
      · have hRight : p.root.column < parent.1.val := by omega
        obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hRight
          ((Frame.P_column_lt hNormal.toOrdered hParent).trans hBefore)
        obtain ⟨father, hFatherRef, _⟩ := Canonical.frame_node_of_cellAt parentCopy.output_read
        refine ⟨father, (s.recorded_effective_parent history hLast hParent hRight hBefore
          copy parentCopy).rawParent hRef hFatherRef, Fin.ext ?_⟩
        have hFatherColumn := (congrArg Ref.column hFatherRef).trans parentCopy.source_column
        rw [if_neg hFixed] at hColumn
        exact hColumn.trans hFatherColumn.symm
  obtain ⟨father, hRaw, hSameColumn⟩ := hStored
  obtain ⟨hRawGeometry, hFatherBound⟩ := s.raw_invariants_of_start_run history hLast hStartRun
  have hSame := Frame.Q_eq_rawParent_of_column s.ambient_valid.toOrdered hRawGeometry hFatherBound
    hNodeReal hQ hRaw hSameColumn
  subst candidate
  exact ⟨node, father, hRef, hCell, hQ, hRaw,
    (s.mountainSums_of_start_run history hLast hStartRun).P_of_Q_rawParent
      s.ambient_valid hNodeReal hQ hRaw⟩

/-- Complete-column preservation carries the direct answer to a later
actual result, including a surviving earlier block after final truncation. -/
theorem DynamicBlockState.nonmarker_direct_rawParent_eq_P_preserved
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient result : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hPreserved : PreservesColumns ambient result)
    (hResult : (Frame.ofMountain result).Ordered)
    {source parent : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hDirect : (Frame.ofMountain p.reduced).Q source = some parent)
    (hBefore : source.1.val < next)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {node : (Frame.ofMountain result).Node} (hRef : Frame.ref node = copy.outputRef) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  obtain ⟨old, father, hOldRef, _, _, hRaw, hP⟩ :=
    s.recorded_nonmarker_direct_parent_all history hLast hStartRun copy hParent hDirect hBefore hUnmarked
  have hSame : hPreserved.mapNode old = node := Executable.ref_injective _
    ((hPreserved.mapNode_ref old).trans (hOldRef.trans hRef.symm))
  have hMappedRaw := hPreserved.mapNode_rawParent hRaw
  have hMappedP := hPreserved.mapNode_P s.ambient_valid.toOrdered hResult hP
  rw [hSame] at hMappedRaw hMappedP
  exact hMappedRaw.trans hMappedP.symm

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.rawParent_none_of_source_parent_none
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_nonmarker_direct_parent_all
#print axioms OmegaY.Expansion.DynamicBlockState.nonmarker_direct_rawParent_eq_P_preserved
