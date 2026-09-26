/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFirstSplitAll.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFirstSplitEvent
import OmegaY.Expansion.ActualMixedMarkerFrontier
import OmegaY.Expansion.ActualFirstDifferenceDepth

/-!
# An actual shared event at the first depth split, for all markers

Source numerical recovery constructs the last common predecessor parent.
Both source frontiers then advance, with one new row and one new geometric
candidate. The actual nonmarker, common-marker and mixed-marker copy cases
construct a common target event. Mixed copies need not have equal rows.

Combining this actual event with the complete source-parent classification
preserves the strict first-difference depth comparison. Earlier inserted
target events remain a separate obligation; no full word sampling or
numerical reconstruction is claimed here.
-/

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

/-- A genuine depth split after one shared source parent determines both
the common next row and the common next candidate, without assumptions on
the next numerical parents or next marker status. -/
theorem Normal.common_parent_depth_split_geometry {F : Frame} (hF : F.Normal)
    (hWidth : 0 < F.width) {bound event : Nat} (hBound : bound < F.width)
    (hEvent : event < F.lastEvent) (left right : Fin F.width)
    (hLeftBound : left.val ≤ bound) (hRightBound : right.val ≤ bound)
    {parent : F.Node}
    (hLeft : F.P (eventFrontier hF.toOrdered event left) = some parent)
    (hRight : F.P (eventFrontier hF.toOrdered event right) = some parent)
    (hDifferent : parentDepth (eventParentMap hF.toOrdered hWidth bound (event + 1)) left.val ≠
      parentDepth (eventParentMap hF.toOrdered hWidth bound (event + 1)) right.val) :
    F.height (eventFrontier hF.toOrdered (event + 1) left) =
        F.height (eventFrontier hF.toOrdered (event + 1) right) ∧
      F.Q (eventFrontier hF.toOrdered (event + 1) left) =
        some (eventFrontier hF.toOrdered (event + 1) parent.1) ∧
      F.Q (eventFrontier hF.toOrdered (event + 1) right) =
        some (eventFrontier hF.toOrdered (event + 1) parent.1) := by
  obtain ⟨hUpperLeft, hUpperRight⟩ := hF.common_parent_depth_split_step hWidth hBound hEvent
    left right hLeftBound hRightBound hLeft hRight hDifferent
  have hLeftChanged : eventFrontier hF.toOrdered (event + 1) left ≠ eventFrontier hF.toOrdered event left := by
    intro he
    have hi := (upper_spec hUpperLeft).2
    rw [he] at hi
    omega
  have hRightChanged : eventFrontier hF.toOrdered (event + 1) right ≠ eventFrontier hF.toOrdered event right := by
    intro he
    have hi := (upper_spec hUpperRight).2
    rw [he] at hi
    omega
  have hLeftRow := (eventFrontier_advance hF.toOrdered hEvent left hLeftChanged).2
  have hRightRow := (eventFrontier_advance hF.toOrdered hEvent right hRightChanged).2
  have hLeftRaw := (hF.rawParent_eq_P (eventFrontier_spec hF.toOrdered event left).2.1).trans hLeft
  have hRightRaw := (hF.rawParent_eq_P (eventFrontier_spec hF.toOrdered event right).2.1).trans hRight
  exact ⟨hLeftRow.trans hRightRow.symm,
    eventFrontier_moving_raw_candidate hF.toOrdered hEvent left hLeftChanged hLeftRaw,
    eventFrontier_moving_raw_candidate hF.toOrdered hEvent right hRightChanged hRightRaw⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- A shared actual event without requiring equal physical row heights. -/
structure EffectiveSharedEvent {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z : (Frame.ofMountain p.reduced).Node}
    (uCopy : EffectiveCopyOccurrence p block start references u result)
    (zCopy : EffectiveCopyOccurrence p block start references z result)
    (hValid : MountainValid result) where
  uNode : (Frame.ofMountain result).Node
  zNode : (Frame.ofMountain result).Node
  event : Nat
  u_ref : Frame.ref uNode = uCopy.outputRef
  z_ref : Frame.ref zNode = zCopy.outputRef
  u_cell : (Frame.ofMountain result).cell uNode = uCopy.read.outputCell
  z_cell : (Frame.ofMountain result).cell zNode = zCopy.read.outputCell
  event_end : event ≤ (Frame.ofMountain result).lastEvent
  u_frontier : eventFrontier hValid.toOrdered event uNode.1 = uNode
  z_frontier : eventFrontier hValid.toOrdered event zNode.1 = zNode

def EffectiveSameRowEvent.toShared
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z : (Frame.ofMountain p.reduced).Node}
    {uCopy : EffectiveCopyOccurrence p block start references u result}
    {zCopy : EffectiveCopyOccurrence p block start references z result}
    {hValid : MountainValid result} (data : EffectiveSameRowEvent uCopy zCopy hValid) :
    EffectiveSharedEvent uCopy zCopy hValid :=
  ⟨data.uNode, data.zNode, data.event, data.u_ref, data.z_ref, data.u_cell, data.z_cell,
    data.event_end, data.u_frontier, data.z_frontier⟩

def SharedContourFrontier.toShared
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z : (Frame.ofMountain p.reduced).Node}
    {uCopy : EffectiveCopyOccurrence p block start references u result}
    {zCopy : EffectiveCopyOccurrence p block start references z result}
    {cut : Row} {hValid : MountainValid result} (data : SharedContourFrontier uCopy zCopy cut hValid) :
    EffectiveSharedEvent uCopy zCopy hValid :=
  ⟨data.uNode, data.zNode, data.event, data.u_ref, data.z_ref, data.u_cell, data.z_cell,
    data.event_end, data.u_frontier, data.z_frontier⟩

def EffectiveSharedEvent.symm
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z : (Frame.ofMountain p.reduced).Node}
    {uCopy : EffectiveCopyOccurrence p block start references u result}
    {zCopy : EffectiveCopyOccurrence p block start references z result}
    {hValid : MountainValid result} (data : EffectiveSharedEvent uCopy zCopy hValid) :
    EffectiveSharedEvent zCopy uCopy hValid :=
  ⟨data.zNode, data.uNode, data.event, data.z_ref, data.u_ref, data.z_cell, data.u_cell,
    data.event_end, data.z_frontier, data.u_frontier⟩

private theorem source_marked_index_iff {front : List Nat} {last : Nat}
    (p : Preparation front last) (node : (Frame.ofMountain p.reduced).Node) :
    node.2.val ∈ (p.marked[node.1.val]?.getD []).map Ref.index ↔
      BucketMem p.marked node.1.val (Frame.ref node) := by
  constructor
  · intro h
    obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
    have he : marker = Frame.ref node := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
    exact he ▸ hm
  · intro h
    exact List.mem_map.mpr ⟨Frame.ref node, h, rfl⟩

/-- The one-step split constructs a shared event in all four combinations
of marker status. The source row/candidate synchrony is itself a theorem. -/
theorem actual_split_event_all
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    (hLast : 1 < last) (hValid : MountainValid result)
    (hWidth : 0 < p.reduced.size) {bound event : Nat} (hBound : bound < p.reduced.size)
    (hEvent : event < (Frame.ofMountain p.reduced).lastEvent)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBound : left.val ≤ bound) (hRightBound : right.val ≤ bound)
    (uCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) result)
    (zCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) result)
    (nextUCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) left) result)
    (nextZCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) right) result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hLeft : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) = some parent)
    (hRight : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) = some parent)
    (hDifferent : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hWidth bound (event + 1)) left.val ≠
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hWidth bound (event + 1)) right.val) :
    Nonempty (EffectiveSharedEvent nextUCopy nextZCopy hValid) := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨hRows, hUQ, hZQ⟩ := hNormal.common_parent_depth_split_geometry hWidth hBound hEvent
    left right hLeftBound hRightBound hLeft hRight hDifferent
  have hUColumn := (eventFrontier_spec hNormal.toOrdered (event + 1) left).1
  have hZColumn := (eventFrontier_spec hNormal.toOrdered (event + 1) right).1
  have hUFront : frontierAt hNormal.toOrdered ((Frame.ofMountain p.reduced).eventCut (event + 1))
      ((Frame.ofMountain p.reduced).eventCut_one_le (event + 1))
      (eventFrontier hNormal.toOrdered (event + 1) left).1 =
        eventFrontier hNormal.toOrdered (event + 1) left := by rw [hUColumn]; rfl
  have hZFront : frontierAt hNormal.toOrdered ((Frame.ofMountain p.reduced).eventCut (event + 1))
      ((Frame.ofMountain p.reduced).eventCut_one_le (event + 1))
      (eventFrontier hNormal.toOrdered (event + 1) right).1 =
        eventFrontier hNormal.toOrdered (event + 1) right := by rw [hZColumn]; rfl
  by_cases hUMarked : BucketMem p.marked (eventFrontier hNormal.toOrdered (event + 1) left).1.val
      (Frame.ref (eventFrontier hNormal.toOrdered (event + 1) left))
  · by_cases hZMarked : BucketMem p.marked (eventFrontier hNormal.toOrdered (event + 1) right).1.val
        (Frame.ref (eventFrontier hNormal.toOrdered (event + 1) right))
    · obtain ⟨data⟩ := nextUCopy.shared_contour_frontier_of_marked nextZCopy hValid hUMarked hZMarked
        ((Frame.ofMountain p.reduced).eventCut_one_le (event + 1)) hUFront hZFront
      exact ⟨data.toShared⟩
    · have hZUnmarked := fun hm => hZMarked ((source_marked_index_iff p _).mp hm)
      obtain ⟨data⟩ := nextUCopy.shared_contour_frontier_mixed_candidate nextZCopy hLast hValid
        hUMarked hZUnmarked hRows hUQ hZQ ((Frame.ofMountain p.reduced).eventCut_one_le (event + 1))
          hUFront hZFront
      exact ⟨data.toShared⟩
  · have hUUnmarked := fun hm => hUMarked ((source_marked_index_iff p _).mp hm)
    by_cases hZMarked : BucketMem p.marked (eventFrontier hNormal.toOrdered (event + 1) right).1.val
        (Frame.ref (eventFrontier hNormal.toOrdered (event + 1) right))
    · obtain ⟨data⟩ := nextZCopy.shared_contour_frontier_mixed_candidate nextUCopy hLast hValid
        hZMarked hUUnmarked hRows.symm hZQ hUQ ((Frame.ofMountain p.reduced).eventCut_one_le (event + 1))
          hZFront hUFront
      exact ⟨data.toShared.symm⟩
    · have hZUnmarked := fun hm => hZMarked ((source_marked_index_iff p _).mp hm)
      obtain ⟨data⟩ := actual_nonmarker_split_event hLast hValid hWidth hBound hEvent left right
        hLeftBound hRightBound uCopy zCopy nextUCopy nextZCopy
          (by simpa only [hUColumn] using hUUnmarked) (by simpa only [hZColumn] using hZUnmarked)
          hLeft hRight hDifferent
      exact ⟨data.toShared⟩

/-- One original common parent and equality at all earlier source depths
determine the actual shared event of the first split, for every marker case. -/
theorem DynamicBlockState.actual_first_split_event_all
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hWidth : 0 < p.reduced.size) {bound previous event : Nat} (hBound : bound < p.reduced.size)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBound : left.val ≤ bound) (hRightBound : right.val ≤ bound)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) ambient)
    (hCommon : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hStart : previous + 1 ≤ event) (hEvent : event ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hEarlier : ∀ r, previous + 1 ≤ r → r < event →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hWidth bound r) left.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hWidth bound r) right.val)
    (hDifferent : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hWidth bound event) left.val ≠
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hWidth bound event) right.val) :
    Nonempty (EffectiveSharedEvent leftCopy rightCopy s.ambient_valid) := by
  obtain ⟨before, parent, hEventEq, _, hBefore, hOldLeft, hOldRight⟩ :=
    build_first_split_previous_parent p.reduced_build hWidth hBound left right hLeftBound hRightBound
      hCommon hStart hEvent hEarlier hDifferent
  subst event
  have hNormal := build_normal_of_success p.reduced_build
  have hOldLCol := (eventFrontier_spec hNormal.toOrdered before left).1
  have hOldRCol := (eventFrontier_spec hNormal.toOrdered before right).1
  have hNewLCol := (eventFrontier_spec hNormal.toOrdered (before + 1) left).1
  have hNewRCol := (eventFrontier_spec hNormal.toOrdered (before + 1) right).1
  have hLeftRight : p.root.column < left.val := by simpa only [hNewLCol] using leftCopy.state.next_lower
  have hRightRight : p.root.column < right.val := by simpa only [hNewRCol] using rightCopy.state.next_lower
  obtain ⟨oldLeftCopy⟩ := s.prior_effective_occurrence history hLast
    (show p.root.column < (eventFrontier hNormal.toOrdered before left).1.val by simpa only [hOldLCol] using hLeftRight)
    (show (eventFrontier hNormal.toOrdered before left).1.val < next by simpa only [hOldLCol] using hLeftBefore)
  obtain ⟨oldRightCopy⟩ := s.prior_effective_occurrence history hLast
    (show p.root.column < (eventFrontier hNormal.toOrdered before right).1.val by simpa only [hOldRCol] using hRightRight)
    (show (eventFrontier hNormal.toOrdered before right).1.val < next by simpa only [hOldRCol] using hRightBefore)
  exact actual_split_event_all hLast s.ambient_valid hWidth hBound hBefore left right hLeftBound hRightBound
    oldLeftCopy oldRightCopy leftCopy rightCopy hOldLeft hOldRight hDifferent

/-- The true first differing source depth has a corresponding actual
target event with the same strict order, without target-frontier inputs. -/
theorem DynamicBlockState.actual_first_split_depth_lt_all
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {previous event : Nat} (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) ambient)
    (hCommon : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hStart : previous + 1 ≤ event) (hEvent : event ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hEarlier : ∀ r, previous + 1 ≤ r → r < event →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) r) left.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) r) right.val)
    (hStrict : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) event) left.val <
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) event) right.val) :
    ∃ data : EffectiveSharedEvent leftCopy rightCopy s.ambient_valid,
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) data.event)
          data.uNode.1.val <
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) data.event)
          data.zNode.1.val := by
  have hBound : p.reduced.size - 1 < p.reduced.size := by omega
  have hLeftBound : left.val ≤ p.reduced.size - 1 := by have := left.isLt; change left.val < p.reduced.size at this; omega
  have hRightBound : right.val ≤ p.reduced.size - 1 := by have := right.isLt; change right.val < p.reduced.size at this; omega
  obtain ⟨data⟩ := s.actual_first_split_event_all history hLast hSourceWidth hBound left right
    hLeftBound hRightBound hLeftBefore hRightBefore leftCopy rightCopy hCommon hStart hEvent hEarlier
      (ne_of_lt hStrict)
  have hNormal := build_normal_of_success p.reduced_build
  have hLeftColumn := (eventFrontier_spec hNormal.toOrdered event left).1
  have hRightColumn := (eventFrontier_spec hNormal.toOrdered event right).1
  refine ⟨data, ?_⟩
  exact s.first_difference_depth_lt_at_frontiers history hLast hStartRun hSourceWidth hTargetWidth
    (by simpa only [hLeftColumn] using hLeftBefore) (by simpa only [hRightColumn] using hRightBefore)
    leftCopy rightCopy data.u_ref data.z_ref
    (by simpa only [hLeftColumn, hRightColumn] using hCommon) hStart hEvent
    (by simpa only [hLeftColumn, hRightColumn] using hEarlier)
    (by rw [hLeftColumn]) (by rw [hRightColumn]) data.u_frontier data.z_frontier
    (by simpa only [hLeftColumn, hRightColumn] using hStrict)

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.common_parent_depth_split_geometry
#print axioms OmegaY.Expansion.actual_split_event_all
#print axioms OmegaY.Expansion.DynamicBlockState.actual_first_split_event_all
#print axioms OmegaY.Expansion.DynamicBlockState.actual_first_split_depth_lt_all
