/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RecordedEffectiveEdges.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.HistoryPrefix
import OmegaY.Expansion.EffectiveOccurrenceUnique
import OmegaY.Expansion.ActualNonrootEffectiveParent
import OmegaY.Expansion.ActualFixedEffectiveParent

/-!
# Effective edges throughout an actual recorded copy prefix

Local edge proofs apply when their child column is being appended. The
actual history can recover that earlier state and its own earlier history.
Complete-column preservation and uniqueness of effective occurrences then
identify the same edge in the current mountain, for any chosen endpoint
certificates. Parent columns strictly to either side of the root are covered;
the root boundary itself is handled separately.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem DynamicBlockState.recorded_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (_s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient) :
    RawRefEdge ambient childCopy.outputRef parentCopy.outputRef := by
  have hParentLeft := Frame.P_column_lt (build_normal_of_success p.reduced_build).toOrdered hParent
  obtain ⟨before, column, oldState, oldHistory, hRun, hPreserve, _⟩ :=
    history.column_with_history (hRight.trans hParentLeft) hBefore
  obtain ⟨localChild, localParent, _, _, hEdge⟩ :=
    oldState.actual_nonroot_effective_parent oldHistory hLast hParent rfl hRight hRun
  have hChildEq : localChild.outputRef = childCopy.outputRef :=
    ((localChild.extend hPreserve).unique childCopy).1
  have hParentEq : localParent.outputRef = parentCopy.outputRef :=
    ((localParent.extend hPreserve).unique parentCopy).1
  simpa only [hChildEq, hParentEq] using hEdge.preserve hPreserve

/-- The fixed-good-parent case is likewise present at every later
recorded prefix, with its original source reference and full cell retained. -/
theorem DynamicBlockState.recorded_fixed_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (_s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildRight : p.root.column < child.1.val) (hBefore : child.1.val < next)
    (hFixed : parent.1.val < p.root.column)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient) :
    RawRefEdge ambient childCopy.outputRef (Frame.ref parent) ∧
      Canonical.cellAt ambient (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent) := by
  obtain ⟨before, column, oldState, _, hRun, hPreserve, _⟩ :=
    history.column_with_history hChildRight hBefore
  obtain ⟨localChild, _, _, hEdge, hRead⟩ :=
    oldState.actual_fixed_parent hLast hParent rfl hFixed hRun
  have hChildEq : localChild.outputRef = childCopy.outputRef :=
    ((localChild.extend hPreserve).unique childCopy).1
  refine ⟨by simpa only [hChildEq] using hEdge.preserve hPreserve, ?_⟩
  obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  exact cellAt_ok_iff.mpr ⟨nodes, hPreserve.column_read hNodes, hCell⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_effective_parent
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_fixed_parent
