/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedDepthWordTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedDepthWords

/-!
# Execution-derived complete copied depth-word comparison

The two complete families of source occurrences and the initial target
event floor are recovered from the actual copying history. The result
preserves equality, strict comparison and non-strict comparison of the
complete finite words, with no assumed target event sampling or comparison.
The source columns are copied columns, strictly to the right of the root.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.actual_copied_depth_word_transport
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftRight : p.root.column < left.val) (hRightRight : p.root.column < right.val)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (hColumn : right.val ≤ left.val) {previous : Nat}
    (hEnd : previous ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hCommon : (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent) :
    ∃ floor : EventCutFloor (Frame.ofMountain ambient)
        (jointEventCut (s.eventCopies history hLast left hLeftRight hLeftBefore)
          (s.eventCopies history hLast right hRightRight hRightBefore) previous),
      let sourceForests := (Frame.ofMountain p.reduced).frontierForests
        (bottomCandidateMap (p.reduced.size - 1))
        (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth)
        (p.reduced.size - 1)
      let targetForests := (Frame.ofMountain ambient).frontierForests
        (bottomCandidateMap (ambient.size - 1))
        (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1)
      let sourceEnd := (Frame.ofMountain p.reduced).lastEvent
      let targetEnd := (Frame.ofMountain ambient).lastEvent
      let targetLeft := left.val + block * (p.reduced.size - 1 - p.root.column)
      let targetRight := right.val + block * (p.reduced.size - 1 - p.root.column)
      (Forests.DepthWordEq sourceForests (previous + 1) sourceEnd left.val right.val →
        Forests.DepthWordEq targetForests (floor.event + 1) targetEnd targetLeft targetRight) ∧
      (Forests.DepthWordLt sourceForests (previous + 1) sourceEnd left.val right.val →
        Forests.DepthWordLt targetForests (floor.event + 1) targetEnd targetLeft targetRight) ∧
      (Forests.DepthWordLe sourceForests (previous + 1) sourceEnd left.val right.val →
        Forests.DepthWordLe targetForests (floor.event + 1) targetEnd targetLeft targetRight) := by
  let leftCopies := s.eventCopies history hLast left hLeftRight hLeftBefore
  let rightCopies := s.eventCopies history hLast right hRightRight hRightBefore
  obtain ⟨floor⟩ := eventCutFloor_exists s.ambient_valid.toOrdered
    (jointEventCut_one_le leftCopies rightCopies previous)
  have hEq := s.copied_depthWordEq history hLast hStartRun hSourceWidth hTargetWidth left right
    hLeftBefore hRightBefore hColumn leftCopies rightCopies hCommon floor hEnd
  have hLt := s.copied_depthWordLt history hLast hStartRun hSourceWidth hTargetWidth left right
    hLeftBefore hRightBefore hColumn leftCopies rightCopies hCommon floor hKnown
  exact ⟨floor, hEq, hLt, fun h => h.elim (fun he => Or.inl (hEq he)) (fun hl => Or.inr (hLt hl))⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_copied_depth_word_transport
