/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectivePaths.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RecordedEffectiveEdges

/-!
# Actual source ancestor paths inside a copied block

The preceding local edge results and the recorded executions identify every
edge of a source ancestor path which stays strictly right of the root column.
The endpoint occurrences may have been obtained independently: uniqueness
identifies them with the local execution witnesses. These are stored paths,
not an assertion that numerical parent search has already been recovered.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem DynamicBlockState.recorded_effective_path
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (path : Frame.ParentPath (Frame.ofMountain p.reduced) child parent)
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient) :
    RawRefPath ambient childCopy.outputRef parentCopy.outputRef := by
  have hNormal := build_normal_of_success p.reduced_build
  induction path with
  | refl source =>
      have he := (childCopy.unique parentCopy).1
      exact he ▸ RawRefPath.refl childCopy.outputRef
  | @cons child middle parent hEdge tail ih =>
      have hMiddleRight : p.root.column < middle.1.val :=
        hRight.trans_le (tail.column_le hNormal.toOrdered)
      have hMiddleBefore : middle.1.val < next :=
        (Frame.P_column_lt hNormal.toOrdered hEdge).trans hBefore
      obtain ⟨middleCopy⟩ := s.prior_effective_occurrence history hLast hMiddleRight hMiddleBefore
      exact RawRefPath.cons
        (s.recorded_effective_parent history hLast hEdge hMiddleRight hBefore childCopy middleCopy)
        (ih hRight hMiddleBefore middleCopy parentCopy)

/-- A path may then leave the bad part for its original good-part parent.
The copied path's last edge and original endpoint read are both consequences
of the real execution; no output path is supplied as a premise. -/
theorem DynamicBlockState.recorded_effective_path_to_fixed
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child lastBad parent : (Frame.ofMountain p.reduced).Node}
    (path : Frame.ParentPath (Frame.ofMountain p.reduced) child lastBad)
    (hEdge : (Frame.ofMountain p.reduced).P lastBad = some parent)
    (hRight : p.root.column < lastBad.1.val) (hBefore : child.1.val < next)
    (hFixed : parent.1.val < p.root.column)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient) :
    RawRefPath ambient childCopy.outputRef (Frame.ref parent) ∧
      Canonical.cellAt ambient (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent) := by
  have hLastBefore : lastBad.1.val < next :=
    (path.column_le (build_normal_of_success p.reduced_build).toOrdered).trans_lt hBefore
  obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hRight hLastBefore
  obtain ⟨hLastEdge, hRead⟩ := s.recorded_fixed_parent history hLast hEdge hRight hLastBefore hFixed lastCopy
  exact ⟨(s.recorded_effective_path history hLast path hRight hBefore childCopy lastCopy).trans
    (.cons hLastEdge (.refl _)), hRead⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_effective_path
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_effective_path_to_fixed
