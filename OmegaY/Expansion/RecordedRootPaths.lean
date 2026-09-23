/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RecordedRootPaths.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRecordedRootParents
import OmegaY.Expansion.ActualEffectivePaths
import OmegaY.Geometry.PathBranch

/-!
# Actual effective ancestor paths ending in the root column

Every source edge strictly before the endpoint has an effective copied
father; the final edge reaches the uniquely selected actual root endpoint.
The path is obtained from recorded executions. No outgoing path from that
boundary endpoint, or copied numerical-parent recognition, is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem DynamicBlockState.recorded_effective_path_to_root
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {child root : (Frame.ofMountain p.reduced).Node}
    (path : Frame.ParentPath (Frame.ofMountain p.reduced) child root)
    (hRootColumn : root.1.val = p.root.column)
    (hChildRight : p.root.column < child.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (rootCopy : EffectiveRootEndpoint p start references root ambient) :
    RawRefPath ambient childCopy.outputRef rootCopy.reference := by
  have hNormal := build_normal_of_success p.reduced_build
  induction path with
  | refl source => omega
  | @cons child middle root hParent tail ih =>
      rcases tail.eq_or_column_lt hNormal.toOrdered with he | hRootBefore
      · subst middle
        exact .cons (s.recorded_root_parent history hLast hStartRun hParent hRootColumn hBefore
          childCopy rootCopy) (.refl _)
      · have hMiddleRight : p.root.column < middle.1.val := hRootColumn ▸ hRootBefore
        have hMiddleBefore : middle.1.val < next := (Frame.P_column_lt hNormal.toOrdered hParent).trans hBefore
        obtain ⟨middleCopy⟩ := s.prior_effective_occurrence history hLast hMiddleRight hMiddleBefore
        exact .cons (s.recorded_effective_parent history hLast hParent hMiddleRight hBefore childCopy middleCopy)
          (ih hRootColumn hMiddleRight hMiddleBefore middleCopy rootCopy)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_effective_path_to_root
