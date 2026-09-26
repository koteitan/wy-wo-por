/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualAllRootParents.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootTailParent

/-!
# Exhaustive actual effective edges into the source root column

The parent is either in the root prefix (including the bad root) or in
the high tail. These genuinely different boundary occurrences are kept
separate. The theorem below requires only a source numerical parent,
the real block state and runs, and its source column being the root.
Neither source marker status nor a cap/height case is a premise.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The two actual boundary representations of a source root-column
node. A reference is selected from the current boundary map; a tail
occurrence is an equal-height node derived from high-row support. -/
inductive EffectiveRootEndpoint {front : List Nat} {last : Nat}
    (p : Preparation front last) (start : Mountain) (references : List Ref)
    (source : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  | selected (copy : EffectiveRootReference p start references source result)
  | highTail (copy : EffectiveRootTailOccurrence p start source result)

def EffectiveRootEndpoint.reference
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node} :
    EffectiveRootEndpoint p start references source result → Ref
  | .selected copy => copy.reference
  | .highTail copy => copy.reference

def EffectiveRootEndpoint.target
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node} :
    EffectiveRootEndpoint p start references source result → Cell
  | .selected copy => copy.target
  | .highTail copy => copy.target

theorem EffectiveRootEndpoint.result_read
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveRootEndpoint p start references source result) :
    Canonical.cellAt result copy.reference = .ok copy.target := by
  cases copy with
  | selected copy => exact copy.result_read
  | highTail copy => exact copy.result_read

/-- Every actual root-column node strictly above the bad root is at
least as high as the old terminal top, even when the source root column
has large gaps between its rows. -/
theorem Preparation.root_node_after_badRoot_is_high
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hColumn : parent.1.val = p.root.column) (hAfter : p.root.index < parent.2.val) :
    p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent := by
  let F := Frame.ofMountain p.reduced
  have hRootBound : p.root.index < F.length parent.1 := lt_trans hAfter parent.2.isLt
  let root : F.Node := ⟨parent.1, ⟨p.root.index, hRootBound⟩⟩
  have hRootRef : Frame.ref root = p.root := by
    exact congrArg₂ Ref.mk hColumn rfl
  have hParentBound : parent.2.val < F.length parent.1 := parent.2.isLt
  have hUpperBound : p.root.index + 1 < F.length parent.1 := by omega
  let upper : F.Node := ⟨parent.1, ⟨p.root.index + 1, hUpperBound⟩⟩
  have hUpper : F.upper root = some upper := by
    simp only [Frame.upper, root, hUpperBound, ↓reduceDIte, upper]
  have hHigh := p.reduced_badRoot_upper_bound hLast hRootRef hUpper
  have hIndex : (⟨p.root.index + 1, hUpperBound⟩ : Fin (F.length parent.1)) ≤ parent.2 := by
    change p.root.index + 1 ≤ parent.2.val
    omega
  exact hHigh.trans ((p.reduced_valid.toOrdered.rows_strict parent.1).monotone hIndex)

/-- Complete root-column parent coverage at one actual copy-column
step. The selected raw edge is a conclusion of the actual execution.
The outgoing path of its boundary endpoint, and numerical parent search
in the returned graph, are deliberately not asserted here. -/
theorem DynamicBlockState.actual_root_effective_parent
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
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (rootCopy : EffectiveRootEndpoint p start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef rootCopy.reference := by
  subst next
  by_cases hMarked : BucketMem p.marked (Frame.ref child).column (Frame.ref child)
  · obtain ⟨childCopy, rootCopy, hBefore, hColumn, _, hEdge⟩ :=
      s.actual_marker_effective_root_parent hLast hParent rfl hRootColumn hMarked hRun
    exact ⟨childCopy, .selected rootCopy, hBefore, hColumn, hEdge⟩
  · obtain ⟨d, _, _, _⟩ := s.column_data hLast child.1.isLt
    have hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index := by
      intro hIndex
      obtain ⟨marker, hMember, hMarkerIndex⟩ := List.mem_map.mp hIndex
      have hMarkerColumn := d.marker_columns marker hMember
      have he : marker = Frame.ref child := by
        exact congrArg₂ Ref.mk hMarkerColumn hMarkerIndex
      apply hMarked
      change Frame.ref child ∈ p.marked[child.1.val]?.getD []
      exact he ▸ hMember
    by_cases hBefore : parent.2.val < p.root.index
    · obtain ⟨childCopy, rootCopy, hBeforeCopy, hColumn, hEdge⟩ :=
        s.actual_lower_root_effective_parent_all_uppers hLast hParent rfl hRootColumn
          hBefore hUnmarked hRun
      exact ⟨childCopy, .selected rootCopy, hBeforeCopy, hColumn, hEdge⟩
    · by_cases hAt : parent.2.val = p.root.index
      · have hRootRef : Frame.ref parent = p.root := by
          exact congrArg₂ Ref.mk hRootColumn hAt
        obtain ⟨childCopy, rootCopy, hBeforeCopy, hColumn, hEdge⟩ :=
          s.actual_badRoot_effective_parent hLast hStartRun hParent hRootRef rfl hUnmarked hRun
        exact ⟨childCopy, .selected rootCopy, hBeforeCopy, hColumn, hEdge⟩
      · have hHigh := p.root_node_after_badRoot_is_high hLast hRootColumn (by omega)
        obtain ⟨childCopy, rootCopy, hBeforeCopy, hColumn, _, hEdge⟩ :=
          s.actual_high_root_effective_parent hLast hStartRun hParent rfl hRootColumn hHigh hRun
        exact ⟨childCopy, .highTail rootCopy, hBeforeCopy, hColumn, hEdge⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.root_node_after_badRoot_is_high
#print axioms OmegaY.Expansion.DynamicBlockState.actual_root_effective_parent
