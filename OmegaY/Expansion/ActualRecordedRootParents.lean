/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRecordedRootParents.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAllRootParents
import OmegaY.Expansion.RecordedEffectiveEdges

/-!
# Root-column effective edges in the actual copy history

Root endpoints are unique at the same block start, including the mutually
exclusive selected-prefix and high-tail cases. The real history recovers
each earlier source-column execution; preservation and uniqueness then
align its effective edge with arbitrary endpoint certificates chosen in
the current mountain. No numerical parent assertion for the new graph
is used.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem tail_reference_eq {mountain : Mountain}
    (hValid : MountainValid mountain) {left right : Ref} {a b : Cell}
    (hA : Canonical.cellAt mountain left = .ok a)
    (hB : Canonical.cellAt mountain right = .ok b)
    (hColumn : left.column = right.column) (hRow : a.row = b.row) : left = right := by
  obtain ⟨nodes, hNodes, hLeft⟩ := cellAt_ok_iff.mp hA
  obtain ⟨others, hOthers, hRight⟩ := cellAt_ok_iff.mp hB
  have he : others = nodes := Option.some.inj (hOthers.symm.trans (hColumn ▸ hNodes))
  subst others
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hCV : ColumnValid mountain left.column nodes := hNodesEq ▸ hValid _ hc
  have hIndex := column_read_index_eq_of_row hCV hLeft hRight hRow
  exact congrArg₂ Ref.mk hColumn hIndex

theorem EffectiveRootTailOccurrence.unique
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start leftResult rightResult : Mountain}
    {source : (Frame.ofMountain p.reduced).Node}
    (left : EffectiveRootTailOccurrence p start source leftResult)
    (right : EffectiveRootTailOccurrence p start source rightResult)
    (hValid : MountainValid start) :
    left.reference = right.reference ∧ left.target = right.target := by
  have hRef := tail_reference_eq hValid left.start_read right.start_read
    (left.reference_column.trans right.reference_column.symm)
    (left.target_row.trans right.target_row.symm)
  exact ⟨hRef, Except.ok.inj
    (left.start_read.symm.trans (by simpa only [hRef] using right.start_read))⟩

/-- A selected reference represents a source strictly below the old
last-top threshold; it therefore cannot also be a high-tail occurrence. -/
theorem EffectiveRootReference.source_below_lastTop
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveRootReference p start references source result) :
    (Frame.ofMountain p.reduced).height source < p.lastTop.row :=
  (copy.target_lower.trans_lt copy.target_below).trans_le copy.cap_top

def EffectiveRootEndpoint.extend
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result later : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveRootEndpoint p start references source result)
    (hPreserved : PreservesColumns result later) :
    EffectiveRootEndpoint p start references source later :=
  match copy with
  | .selected selectedCopy => .selected (selectedCopy.extend hPreserved)
  | .highTail tail => .highTail (tail.extend hPreserved)

@[simp] theorem EffectiveRootEndpoint.extend_reference
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result later : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveRootEndpoint p start references source result)
    (hPreserved : PreservesColumns result later) :
    (copy.extend hPreserved).reference = copy.reference := by
  cases copy <;> rfl

@[simp] theorem EffectiveRootEndpoint.extend_target
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result later : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveRootEndpoint p start references source result)
    (hPreserved : PreservesColumns result later) :
    (copy.extend hPreserved).target = copy.target := by
  cases copy <;> rfl

/-- Both the concrete reference and complete cell are determined by the
source and start mountain. No choice of exact cap or later result changes
them. The cross-constructor cases are excluded by their source heights. -/
theorem EffectiveRootEndpoint.unique
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start leftResult rightResult : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (left : EffectiveRootEndpoint p start references source leftResult)
    (right : EffectiveRootEndpoint p start references source rightResult)
    (hValid : MountainValid start) :
    left.reference = right.reference ∧ left.target = right.target := by
  cases left with
  | selected selected =>
      cases right with
      | selected other => exact selected.unique other hValid
      | highTail tail => exact False.elim ((not_le_of_gt selected.source_below_lastTop) tail.source_high)
  | highTail tail =>
      cases right with
      | selected selected => exact False.elim ((not_le_of_gt selected.source_below_lastTop) tail.source_high)
      | highTail other => exact tail.unique other hValid

/-- The earlier child execution supplies its root endpoint. Its raw
edge persists to the current recorded prefix and is identified with any
chosen effective occurrence of the child. -/
theorem DynamicBlockState.recorded_root_parent_exists
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (_s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hRootColumn : parent.1.val = p.root.column) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient) :
    ∃ rootCopy : EffectiveRootEndpoint p start references parent ambient,
      RawRefEdge ambient childCopy.outputRef rootCopy.reference := by
  have hParentLeft := Frame.P_column_lt (build_normal_of_success p.reduced_build).toOrdered hParent
  have hChildRight : p.root.column < child.1.val := hRootColumn ▸ hParentLeft
  obtain ⟨before, column, oldState, _, hRun, hPreserve, _⟩ :=
    history.column_with_history hChildRight hBefore
  obtain ⟨localChild, localRoot, _, _, hEdge⟩ :=
    oldState.actual_root_effective_parent hLast hStartRun hParent rfl hRootColumn hRun
  have hChildEq : localChild.outputRef = childCopy.outputRef :=
    ((localChild.extend hPreserve).unique childCopy).1
  refine ⟨localRoot.extend hPreserve, ?_⟩
  simpa only [hChildEq, EffectiveRootEndpoint.extend_reference] using hEdge.preserve hPreserve

/-- Endpoint uniqueness upgrades the existential historical result to
the caller's chosen actual root endpoint. -/
theorem DynamicBlockState.recorded_root_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hRootColumn : parent.1.val = p.root.column) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (rootCopy : EffectiveRootEndpoint p start references parent ambient) :
    RawRefEdge ambient childCopy.outputRef rootCopy.reference := by
  obtain ⟨actualRoot, hEdge⟩ := s.recorded_root_parent_exists
    history hLast hStartRun hParent hRootColumn hBefore childCopy
  exact (actualRoot.unique rootCopy s.start_valid).1 ▸ hEdge

/-- Two source children with the same root-column numerical parent
have actual effective raw edges to one and the same boundary endpoint.
There is no premise about their output upper heights or numerical P. -/
theorem DynamicBlockState.recorded_common_root_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {left right parent : (Frame.ofMountain p.reduced).Node}
    (hLeftParent : (Frame.ofMountain p.reduced).P left = some parent)
    (hRightParent : (Frame.ofMountain p.reduced).P right = some parent)
    (hRootColumn : parent.1.val = p.root.column)
    (hLeftBefore : left.1.val < next) (hRightBefore : right.1.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references left ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references right ambient) :
    ∃ rootCopy : EffectiveRootEndpoint p start references parent ambient,
      RawRefEdge ambient leftCopy.outputRef rootCopy.reference ∧
      RawRefEdge ambient rightCopy.outputRef rootCopy.reference := by
  obtain ⟨rootCopy, hLeft⟩ := s.recorded_root_parent_exists
    history hLast hStartRun hLeftParent hRootColumn hLeftBefore leftCopy
  exact ⟨rootCopy, hLeft, s.recorded_root_parent
    history hLast hStartRun hRightParent hRootColumn hRightBefore rightCopy rootCopy⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveRootEndpoint.unique
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_root_parent_exists
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_root_parent
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_common_root_parent
