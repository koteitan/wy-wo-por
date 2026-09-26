/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonrootEffectiveParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualStationaryEffectiveParent
import OmegaY.Expansion.ActualEffectiveMarkerParent
import OmegaY.Expansion.ActualRaisedSeamParent

/-!
# Every source edge with a strictly-right father has an effective raw copy

The real effective read is either a marker occurrence or an unmarked
occurrence. Its row cannot decrease, so the latter is stationary or raised;
the source successor is either marked or unmarked. These exhaustive tests
are performed inside the proof. No row case, desired parent endpoint, or
copied numerical-normality certificate is required from the caller.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Complete local effective-edge transport for a source numerical father
strictly right of the bad-root column. Both endpoint certificates are
constructed from the actual current run and its prior-copy history. -/
theorem DynamicBlockState.actual_nonroot_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (parentCopy : EffectiveCopyOccurrence p block start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef parentCopy.outputRef := by
  subst next
  by_cases hMarked : BucketMem p.marked child.1.val (Frame.ref child)
  · obtain ⟨childCopy, parentCopy, hBefore, hColumn, _, hEdge⟩ :=
      s.actual_marker_effective_parent history hLast hParent rfl hRight hMarked hRun
    exact ⟨childCopy, parentCopy, hBefore, hColumn, hEdge⟩
  · let F := Frame.ofMountain p.reduced
    obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
    have hSource : p.reduced[child.1.val]? = some d.sources :=
      (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
    have hSourceRead := d.frame_source_read hSource (rfl : child.1.val = child.1.val)
    obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hSourceRead
    have hUnmarked : child.2.val ∉ d.bucket.map Ref.index := by
      intro hMem
      obtain ⟨marker, hm, hIndex⟩ := List.mem_map.mp hMem
      have hColumn := d.marker_columns marker hm
      have hRef : marker = Frame.ref child := by
        cases marker
        simp only [Frame.ref, Ref.mk.injEq]
        exact ⟨hColumn, hIndex⟩
      exact hMarked (hRef ▸ hm)
    let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
      ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
    have hLower : F.height child ≤ read.outputCell.row := read.source_row_le_output
    rcases eq_or_lt_of_le hLower with hStationary | hRaised
    · obtain ⟨parentCopy, hEdge⟩ := s.stationary_effective_parent_of_occurrence
        history hLast hParent rfl hRight hUnmarked hRun childCopy hStationary.symm
      exact ⟨childCopy, parentCopy, rfl, rfl, hEdge⟩
    · by_cases hUpperMarked : child.2.val + 1 ∈ d.bucket.map Ref.index
      · obtain ⟨actualChild, parentCopy, hBefore, hColumn, _, hEdge⟩ :=
          s.actual_raised_seam_parent_of_read history hLast hParent rfl hRight d read hUpperMarked hRaised
        exact ⟨actualChild, parentCopy, hBefore, hColumn, hEdge⟩
      · obtain ⟨branch⟩ := s.raised_source_contour_of_effective_read rfl read hUnmarked hUpperMarked hRaised
        exact s.actual_raised_contour_effective_parent history hLast hParent rfl hRight branch hRun

/-- Independently selected occurrences give the same exact raw edge.
Uniqueness follows from the actual preserved output column, not copied
first-smaller correctness or a supplied parent correspondence. -/
theorem DynamicBlockState.nonroot_effective_edge_of_occurrences
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
    (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
    (parentCopy : EffectiveCopyOccurrence p block start references parent (ambient.push column)) :
    RawRefEdge (ambient.push column) childCopy.outputRef parentCopy.outputRef := by
  obtain ⟨actualChild, actualParent, _, _, hEdge⟩ :=
    s.actual_nonroot_effective_parent history hLast hParent hChildColumn hRight hRun
  exact (actualChild.unique childCopy).1 ▸ ((actualParent.unique parentCopy).1 ▸ hEdge)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_nonroot_effective_parent
#print axioms OmegaY.Expansion.DynamicBlockState.nonroot_effective_edge_of_occurrences
