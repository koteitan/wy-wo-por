/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootTailParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootEffectiveSeams

/-!
# Actual effective parents in the high tail of the root column

A high root-column node is represented by the actual current boundary
node at the same height. It need not belong to the block's reference map:
the reference caps end at the old terminal top. The high support used to
find this node is derived from the successful outer loop.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A concrete high-tail endpoint retained from the block's starting
boundary. This certificate contains no outgoing-parent assertion. -/
structure EffectiveRootTailOccurrence {front : List Nat} {last : Nat}
    (p : Preparation front last) (start : Mountain)
    (source : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  reference : Ref
  target : Cell
  source_column : source.1.val = p.root.column
  source_high : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source
  reference_column : reference.column = start.size - 1
  start_read : Canonical.cellAt start reference = .ok target
  result_read : Canonical.cellAt result reference = .ok target
  target_row : target.row = (Frame.ofMountain p.reduced).height source

def EffectiveRootTailOccurrence.extend
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result later : Mountain} {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveRootTailOccurrence p start source result)
    (hPreserved : PreservesColumns result later) :
    EffectiveRootTailOccurrence p start source later := by
  have hRead : Canonical.cellAt later copy.reference = .ok copy.target := by
    obtain ⟨nodes, hNodes, hIndex⟩ := cellAt_ok_iff.mp copy.result_read
    exact cellAt_ok_iff.mpr ⟨nodes, hPreserved.column_read hNodes, hIndex⟩
  exact { copy with result_read := hRead }

/-- Every high root-column numerical parent has an actual effective raw
edge to its equal-height boundary representative. Source and output
geometry are read from the genuine column run; output numerical search
agreement is not assumed. -/
theorem DynamicBlockState.actual_high_root_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRootColumn : parent.1.val = p.root.column)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (rootCopy : EffectiveRootTailOccurrence p start parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      childCopy.read.outputCell.row = (Frame.ofMountain p.reduced).height child ∧
      RawRefEdge (ambient.push column) childCopy.outputRef rootCopy.reference := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hChildHigh : p.lastTop.row ≤ F.height child :=
    hHigh.trans (Frame.P_height_le hNormal.toOrdered hParent)
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead := d.frame_source_read hSource (rfl : child.1.val = child.1.val)
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    have hr := d.frame_source_read hSource (congrArg Fin.val (Frame.upper_spec hUpper).1)
    simpa only [(Frame.upper_spec hUpper).2] using hr
  have hUpperRef : Frame.ref sourceUpper = ⟨child.1.val, child.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  obtain ⟨upper, candidate, hUpperOut, _, hCopy, hShape⟩ := s.effective_high_upper_execution
    hLast child.1.isLt d hParentPower hParentLow hNoPremature read hSourceUpper hChildHigh
  have hExecutable := (Executable.findParent_ref_iff hNormal.toOrdered child parent).mpr hParent
  obtain ⟨reference, target, hBelow, hTargetRead, hReferenceColumn, hTargetRow⟩ :=
    s.below_high_root_parent hLast hStartRun hExecutable hUpper hRootColumn hHigh
  have hBoundaryColumn : reference.column = start.size - 1 :=
    hReferenceColumn.trans s.boundary_copy_index
  have hBoundaryBound : reference.column < start.size := by
    have hb := RootRowsInColumn.column_lt s.boundary_rows
    simpa only [hBoundaryColumn] using hb
  have hStartRead : Canonical.cellAt start reference = .ok target := by
    have he := cellAt_eq_of_column_eq (s.start_preserved reference.column hBoundaryBound)
    exact he.symm.trans hTargetRead
  have hChildReal : Frame.Real child := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, _, _, hStored⟩ := hNormal.upper_step child sourceUpper hChildReal hUpper
  have he : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  change (F.cell sourceUpper).left = some (Frame.ref parent) at hStored
  have hSourceUpperRead : lookup ambient (Frame.ref sourceUpper) = .ok (F.cell sourceUpper) :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp
      (p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced sourceUpper)))
  have hNonzero : (F.cell sourceUpper).row ≠ 0 := by
    have hOne := Frame.one_le_height hNormal.toOrdered (upper_real hUpper)
    intro hz
    change (1 : Row) ≤ (F.cell sourceUpper).row at hOne
    rw [hz] at hOne
    exact (not_le_of_gt Row.zero_lt_one) hOne
  have hParentRefColumn : (Frame.ref parent).column = p.root.column := hRootColumn
  have hSelected : below ambient ((Frame.ref parent).column +
      block * (p.reduced.size - 1 - p.root.column)) (F.height sourceUpper) = .ok reference := by
    rw [hParentRefColumn]
    exact hBelow
  have hDestination : reference.column < (Frame.ref sourceUpper).column +
      block * (p.reduced.size - 1 - p.root.column) := by
    rw [hReferenceColumn, hUpperRef]
    exact Nat.add_lt_add_right s.next_lower _
  have hNotFixed : ¬ (Frame.ref parent).column < p.root.column := by rw [hParentRefColumn]; omega
  have hExpected : copyEdge ambient (Frame.ref sourceUpper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column (F.height sourceUpper) =
        .ok ⟨F.height sourceUpper, 0, some reference⟩ := by
    simp [copyEdge, hSourceUpperRead, hNonzero, leftOf, hStored, hNotFixed, hSelected,
      Nat.not_le_of_gt hDestination]
  rw [hUpperRef] at hExpected
  have hCandidate : candidate = (⟨F.height sourceUpper, 0, some reference⟩ : Cell) :=
    Except.ok.inj (hCopy.symm.trans hExpected)
  let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  let rootRead : EffectiveRootTailOccurrence p start parent ambient :=
    ⟨reference, target, hRootColumn, hHigh, hBoundaryColumn, hStartRead, hTargetRead, hTargetRow⟩
  let rootCopy := rootRead.extend (PreservesColumns.push ambient column)
  refine ⟨childCopy, rootCopy, rfl, rfl,
    s.effective_high_row hLast child.1.isLt read hChildHigh,
    read.outputCell, upper, target, read.output_read, ?_, ?_, rootCopy.result_read⟩
  · exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
      EffectiveCopyRead.outputRef], hUpperOut⟩
  · exact hShape.2.symm.trans (congrArg Cell.left hCandidate)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_root_effective_parent
