/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RecordedRootFrontierProjection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RecordedRootPaths
import OmegaY.Expansion.InitialBoundaryFrontierPath
import OmegaY.Expansion.ActualMarkedFrontierCopy
import OmegaY.Expansion.ActualLowPathDepth

/-!
# Root endpoints and downward projection of actual recorded paths

The recorded source path constructs its boundary endpoint. A separate
canonical projection lemma moves an already established numerical path
to an arbitrary lower cut. No endpoint path or projected path is assumed.
-/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem build_parent_path_cut_projection {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {child parent : (Frame.ofMountain mountain).Node}
    (hReal : Real child) (path : ParentPath (Frame.ofMountain mountain) child parent)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hBelow : cut ≤ (Frame.ofMountain mountain).height child) :
    ParentPath (Frame.ofMountain mountain)
      (frontierAt (build_normal_of_success hBuild).toOrdered cut hCut child.1)
      (frontierAt (build_normal_of_success hBuild).toOrdered cut hCut parent.1) := by
  let F := Frame.ofMountain mountain
  have hNormal := build_normal_of_success hBuild
  obtain ⟨event, hEvent, hRow⟩ := real_height_at_event hNormal.toOrdered hReal
  obtain ⟨floor, hFloor, hFloorCut, _, hFront⟩ := event_floor_at_cut hNormal.toOrdered hCut
  have hOrder : floor ≤ event := by
    by_contra hn
    have hFloorEnd : floor ≤ F.lastEvent := hFloor
    have hStrict := F.eventCut_strict_step (show event < F.lastEvent by omega)
    have hLe := F.eventCut_monotone (show event + 1 ≤ floor by omega)
    exact (not_lt_of_ge (hFloorCut.trans (hBelow.trans_eq hRow.symm))) (hStrict.trans_le hLe)
  have hChildFront : eventFrontier hNormal.toOrdered event child.1 = child :=
    frontierAt_of_height_eq hNormal.toOrdered (F.eventCut_one_le event) hRow.symm
  have hProjected := build_parent_path_event_projection hBuild hWidth hOrder hEvent hChildFront path
  simpa only [hFront] using hProjected

theorem DynamicBlockState.recorded_effective_path_to_root_exists
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {child root : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child root)
    (hRootColumn : root.1.val = p.root.column)
    (hChildRight : p.root.column < child.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient) :
    ∃ rootCopy : EffectiveRootEndpoint p start references root ambient,
      RawRefPath ambient childCopy.outputRef rootCopy.reference := by
  have hNormal := build_normal_of_success p.reduced_build
  induction path with
  | refl source => omega
  | @cons child middle root hParent tail ih =>
    rcases tail.eq_or_column_lt hNormal.toOrdered with he | hRootBefore
    · subst middle
      obtain ⟨rootCopy, hEdge⟩ := s.recorded_root_parent_exists
        history hLast hStartRun hParent hRootColumn hBefore childCopy
      exact ⟨rootCopy, .cons hEdge (.refl _)⟩
    · have hMiddleRight : p.root.column < middle.1.val := hRootColumn ▸ hRootBefore
      have hMiddleBefore : middle.1.val < next := (P_column_lt hNormal.toOrdered hParent).trans hBefore
      obtain ⟨middleCopy⟩ := s.prior_effective_occurrence history hLast hMiddleRight hMiddleBefore
      obtain ⟨rootCopy, hTail⟩ := ih hRootColumn hMiddleRight hMiddleBefore middleCopy
      exact ⟨rootCopy, .cons (s.recorded_effective_parent history hLast hParent
        hMiddleRight hBefore childCopy middleCopy) hTail⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_parent_path_cut_projection
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_effective_path_to_root_exists
