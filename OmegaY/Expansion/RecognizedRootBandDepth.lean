/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RecognizedRootBandDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RecognizedPrefix
import OmegaY.Expansion.CanonicalDepthAntitone
import OmegaY.Expansion.ActualContourEventOrder

/-!
# Root-depth lower bounds throughout the earlier lifted band

The already constructed root-path packet gives a nonnegative boundary
correction at its own lifted endpoint, including the highest bad root.
The strict-left induction reconstructs the complete block-start prefix.
Its actual event depths are antitone, so the lower bound holds at every
earlier cut, including cuts introduced only in later copied columns.
Actual floor events and prefix preservation identify those depths.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem LowRootPathDepth.boundary_depth_le_at_earlier_cut_of_left_recognition
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next copies : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {child lastBad root : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {childCopy : EffectiveCopyOccurrence p block start references child ambient}
    (data : LowRootPathDepth s child lastBad root sourceEvent childCopy)
    (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent)
    {targetEvent : Nat}
    (hCut : (Frame.ofMountain ambient).eventCut targetEvent ≤
      childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) :
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      data.copied.source_width (p.reduced.size - 1) sourceEvent) root.1.val ≤
      parentDepth (eventParentMap s.ambient_valid.toOrdered data.copied.target_width
        (ambient.size - 1) targetEvent) (start.size - 1) := by
  obtain ⟨values, _, hBuild⟩ := p.blocks_reconstruct_of_left_recognition hLast hStartRun
    s.start_preserved s.ambient_valid.toOrdered hKnown
  obtain ⟨increment, hCorrection, _⟩ := data.correction hLast hStartRun
  have hOne := (Frame.ofMountain ambient).eventCut_one_le targetEvent
  obtain ⟨earlier, hEarlierEnd, hBelow, _, hFrontiers⟩ :=
    event_floor_at_cut s.start_valid.toOrdered hOne
  have hRows : (Frame.ofMountain start).eventCut earlier ≤
      (Frame.ofMountain start).eventCut data.startEvent :=
    data.start_event_maximal _ ((Frame.ofMountain start).eventCut_mem earlier)
      (hBelow.trans hCut)
  have hOrder := event_index_le_of_cut_le hEarlierEnd data.start_event_end hRows
  have hBound : start.size - 1 < start.size := by have := data.start_width; omega
  have hDepthOrder := build_event_parentDepth_antitone hBuild data.start_width hBound hOrder
    data.start_event_end (Nat.le_refl (start.size - 1))
  have hTransferred := s.start_preserved.event_parentDepth_at_common_cut s.start_valid.toOrdered
    s.ambient_valid.toOrdered data.start_width data.copied.target_width hOne hFrontiers
    (fun _ => rfl) hBound
  rw [hTransferred]
  have hBaseline : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      data.copied.source_width (p.reduced.size - 1) sourceEvent) root.1.val ≤
      parentDepth (eventParentMap s.start_valid.toOrdered data.start_width
        (start.size - 1) data.startEvent) (start.size - 1) := by
    rw [hCorrection]
    exact Nat.le_add_right _ _
  exact hBaseline.trans hDepthOrder

end OmegaY.Expansion

#print axioms OmegaY.Expansion.LowRootPathDepth.boundary_depth_le_at_earlier_cut_of_left_recognition
