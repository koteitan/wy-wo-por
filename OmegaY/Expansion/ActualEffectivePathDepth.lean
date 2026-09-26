/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectivePathDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectivePaths
import OmegaY.Expansion.RawPathFrontier
import OmegaY.Expansion.HistoryRawInvariants

/-!
# Equal edge counts along actual effective copies at event frontiers

Once the initial source and effective nodes are identified at chosen event
frontiers, their entire source ancestor path stays at those frontiers. The
actual copied edges give the same number of steps on both sides. Thus the
relative depth balance is a conclusion, not a certificate supplied by the
caller. Selecting the appropriate paired events remains a separate task.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.recorded_effective_path_frontier_steps
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hRaw : (Frame.ofMountain ambient).RawRowGeometry)
    (hFather : (Frame.ofMountain ambient).RawFatherUpperBound)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {sourceBound targetBound sourceEvent targetEvent : Nat}
    {child parent : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child parent)
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient)
    {u v : (Frame.ofMountain ambient).Node}
    (hU : Frame.ref u = childCopy.outputRef) (hV : Frame.ref v = parentCopy.outputRef)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent child.1 = child)
    (hTargetFront : eventFrontier s.ambient_valid.toOrdered targetEvent u.1 = u)
    (hSourceBound : child.1.val ≤ sourceBound) (hTargetBound : u.1.val ≤ targetBound) :
    ∃ length,
      Forests.ParentSteps (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
          hSourceWidth sourceBound sourceEvent) child.1.val parent.1.val length ∧
      Forests.ParentSteps (eventParentMap s.ambient_valid.toOrdered
          hTargetWidth targetBound targetEvent) u.1.val v.1.val length ∧
      eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent parent.1 = parent ∧
      eventFrontier s.ambient_valid.toOrdered targetEvent v.1 = v := by
  have hNormal := build_normal_of_success p.reduced_build
  induction path generalizing u with
  | refl source =>
      have he : u = v := Executable.ref_injective _
        (hU.trans ((childCopy.unique parentCopy).1.trans hV.symm))
      subst u
      exact ⟨0, .nil _, .nil _, hSourceFront, hTargetFront⟩
  | @cons child middle parent hEdge tail ih =>
      have hMiddleRight : p.root.column < middle.1.val :=
        hRight.trans_le (tail.column_le hNormal.toOrdered)
      have hMiddleBefore : middle.1.val < next :=
        (P_column_lt hNormal.toOrdered hEdge).trans hBefore
      obtain ⟨middleCopy⟩ := s.prior_effective_occurrence history hLast hMiddleRight hMiddleBefore
      have hActualEdge := s.recorded_effective_parent history hLast hEdge hMiddleRight hBefore childCopy middleCopy
      obtain ⟨q, hQRef, _⟩ := Canonical.frame_node_of_cellAt middleCopy.output_read
      have hRawEdge : (Frame.ofMountain ambient).rawParent u = some q := hActualEdge.rawParent hU hQRef
      have hNewTargetFront := eventFrontier_raw_parent_of_bound s.ambient_valid.toOrdered hRaw hFather
        targetEvent u.1 (by simpa only [hTargetFront] using hRawEdge)
      have hTargetMap : eventParentMap s.ambient_valid.toOrdered hTargetWidth targetBound targetEvent
          u.1.val = some q.1.val := by
        rw [eventParentMap_raw_at s.ambient_valid.toOrdered hTargetWidth targetEvent u.1 hTargetBound,
          hTargetFront, hRawEdge]
        rfl
      have hNewSourceFront := hNormal.eventFrontier_parent sourceEvent child.1
        (by simpa only [hSourceFront] using hEdge)
      have hSourceMap : eventParentMap hNormal.toOrdered hSourceWidth sourceBound sourceEvent
          child.1.val = some middle.1.val := by
        rw [hNormal.eventParentMap_at hSourceWidth sourceEvent child.1 hSourceBound, hSourceFront, hEdge]
        rfl
      have hNewSourceBound := (P_column_lt hNormal.toOrdered hEdge).le.trans hSourceBound
      have hNewTargetBound := (rawParent_column_lt s.ambient_valid.toOrdered hRawEdge).le.trans hTargetBound
      obtain ⟨length, hSourceSteps, hTargetSteps, hSourceEnd, hTargetEnd⟩ :=
        ih hRight hMiddleBefore middleCopy parentCopy hQRef hV hNewSourceFront hNewTargetFront
          hNewSourceBound hNewTargetBound
      exact ⟨length + 1, .cons hSourceMap hSourceSteps, .cons hTargetMap hTargetSteps,
        hSourceEnd, hTargetEnd⟩

/-- Actual effective ancestor paths have exactly the source depth difference
at every pair of frontiers containing their initial nodes. No depth equality,
edge correspondence or output Normal is a premise. -/
theorem DynamicBlockState.recorded_effective_path_depth_balance
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {sourceBound targetBound sourceEvent targetEvent : Nat}
    (hSourceSize : sourceBound < p.reduced.size) (hTargetSize : targetBound < ambient.size)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child parent)
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient)
    {u v : (Frame.ofMountain ambient).Node}
    (hU : Frame.ref u = childCopy.outputRef) (hV : Frame.ref v = parentCopy.outputRef)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent child.1 = child)
    (hTargetFront : eventFrontier s.ambient_valid.toOrdered targetEvent u.1 = u)
    (hSourceBound : child.1.val ≤ sourceBound) (hTargetBound : u.1.val ≤ targetBound) :
    let sourceMap := eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth sourceBound sourceEvent
    let targetMap := eventParentMap s.ambient_valid.toOrdered hTargetWidth targetBound targetEvent
    parentDepth targetMap u.1.val + parentDepth sourceMap parent.1.val =
      parentDepth sourceMap child.1.val + parentDepth targetMap v.1.val := by
  obtain ⟨hRaw, hFather⟩ := s.raw_invariants_of_start_run history hLast hStartRun
  obtain ⟨length, hSourceSteps, hTargetSteps, _, _⟩ := s.recorded_effective_path_frontier_steps history hLast
    hRaw hFather hSourceWidth hTargetWidth path hRight hBefore childCopy parentCopy hU hV
      hSourceFront hTargetFront hSourceBound hTargetBound
  have hSourceDepth : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth sourceBound sourceEvent) child.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth sourceBound sourceEvent) parent.1.val + length := hSourceSteps.depth
    (eventParentMap_leftward (build_normal_of_success p.reduced_build).toOrdered hSourceWidth hSourceSize sourceEvent)
  have hTargetDepth : parentDepth (eventParentMap s.ambient_valid.toOrdered
        hTargetWidth targetBound targetEvent) u.1.val =
      parentDepth (eventParentMap s.ambient_valid.toOrdered
        hTargetWidth targetBound targetEvent) v.1.val + length := hTargetSteps.depth
    (eventParentMap_leftward s.ambient_valid.toOrdered hTargetWidth hTargetSize targetEvent)
  dsimp only
  omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_effective_path_frontier_steps
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_effective_path_depth_balance
