/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighBlockerRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FinalHighEventSuffix
import OmegaY.Expansion.FinalHighDepth
import OmegaY.Expansion.FinalCopyIndices
import OmegaY.Expansion.ActualEffectiveRecognition
import OmegaY.Expansion.ActualCommonParentUpper
import OmegaY.Expansion.ActualStationaryMarkerUpper
import OmegaY.Expansion.ActualHighMarkerStationary

/-!
# Actual numerical recognition above an unchanged high common upper

For a copied source record with a right-side parent, an actual common
upper at or above Z keeps its row. A source marker in this branch is
necessarily stationary. The full returned expansion has
the source's absolute depths there. Sampling the suffix at that exact
upper transports the source blocker comparison; no target value or word
inequality is an input. Numerical recognition is used only strictly left
of the current column and strictly above the current node.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem EffectiveCopyOccurrence.upper_height_of_high
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source sourceUpper : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    (hSourceUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height sourceUpper)
    {target targetUpper : (Frame.ofMountain result).Node}
    (hTargetRef : Frame.ref target = copy.outputRef)
    (hTargetUpper : (Frame.ofMountain result).upper target = some targetUpper) :
    (Frame.ofMountain result).height targetUpper = (Frame.ofMountain p.reduced).height sourceUpper := by
  obtain ⟨upperCell, hRead, hRow⟩ := copy.upper_lift_read hLast hUnmarked hSourceUpper
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hRead
  have he : upper = targetUpper := Option.some.inj
    ((Frame.upper_of_refs hTargetRef hUpperRef).symm.trans hTargetUpper)
  obtain ⟨degree, hLift, hCap⟩ := copy.state.marker_caps_below_lastTop hLast copy.data
    source.1.isLt copy.read.marker copy.read.marker_mem
  rw [← he, Frame.height, hUpperCell, hRow]
  exact Row.lift_eq_of_ge_cap (copy.data.marker_data copy.read.marker copy.read.marker_mem).target_lower
    hLift (hCap.trans hHigh)

namespace SourceBlockerCopyPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : SourceBlockerCopyPacket p block start references sourceU sourceParent result)

/-- The source word inequality is transported at its own actual upper
threshold and then converted back to the target numerical inequality.
This discharges the blocker premise for this high-upper branch. -/
theorem high_upper_barrier_of_row
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hUpperRow : (Frame.ofMountain result).height packet.pair.uUpper =
      (Frame.ofMountain p.reduced).height packet.sourceUUpper)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height packet.sourceUUpper)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    (Frame.ofMountain result).value packet.pair.u ≤ (Frame.ofMountain result).value packet.pair.z := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hBlock := packet.pair.uCopy.block_le hLast hCopies hRun
  have hSourceWidth : 0 < p.reduced.size := (Nat.zero_le sourceU.1.val).trans_lt sourceU.1.isLt
  have hTargetWidth : 0 < result.size := (Nat.zero_le packet.pair.u.1.val).trans_lt packet.pair.u.1.isLt
  have hURight := hParentRight.trans (P_column_lt hNormal.toOrdered packet.source_parent)
  have hZRight := hParentRight.trans (P_column_lt hNormal.toOrdered packet.source_last_parent)
  have hUColumn : packet.pair.u.1.val = sourceU.1.val + block * (p.reduced.size - 1 - p.root.column) :=
    (congrArg Ref.column packet.pair.u_ref).trans packet.pair.uCopy.source_column
  have hZColumn : packet.pair.z.1.val = packet.blocker.1.val + block * (p.reduced.size - 1 - p.root.column) :=
    (congrArg Ref.column packet.pair.z_ref).trans packet.pair.zCopy.source_column
  have hUDepth : HighCutDepthMatch hNormal.toOrdered hValid.toOrdered hSourceWidth hTargetWidth
      p.lastTop.row sourceU.1.val packet.pair.u.1.val := by
    intro sourceEvent targetEvent hSourceEvent _ hHighEvent hCut
    change parentDepth (eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent)
      packet.pair.u.1.val = parentDepth (eventParentMap hNormal.toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) sourceU.1.val
    have hDepth := p.expandDiagram_high_depth_at_equal_cut hLast hCopies hRun hValid
      hSourceWidth hTargetWidth hBlock hURight hSourceEvent hHighEvent hCut
        (by rw [← hUColumn]; exact packet.pair.u.1.isLt)
    simpa only [← hUColumn] using hDepth
  have hZDepth : HighCutDepthMatch hNormal.toOrdered hValid.toOrdered hSourceWidth hTargetWidth
      p.lastTop.row packet.blocker.1.val packet.pair.z.1.val := by
    intro sourceEvent targetEvent hSourceEvent _ hHighEvent hCut
    change parentDepth (eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent)
      packet.pair.z.1.val = parentDepth (eventParentMap hNormal.toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) packet.blocker.1.val
    have hDepth := p.expandDiagram_high_depth_at_equal_cut hLast hCopies hRun hValid
      hSourceWidth hTargetWidth hBlock hZRight hSourceEvent hHighEvent hCut
        (by rw [← hZColumn]; exact packet.pair.z.1.isLt)
    simpa only [← hZColumn] using hDepth
  obtain ⟨sourceEvent, hSourceEnd, hSourceCut, hSourceWord⟩ := packet.source_depth_word
  obtain ⟨targetEvent, hTargetEnd, hTargetCut, hComparison⟩ :=
    packet.target_depth_word_comparison hLegal hRun hLeft hHigher
  have hSourceStart : F.highEventStart (F.height packet.sourceUUpper) = sourceEvent + 1 := by
    rw [← hSourceCut]
    exact F.highEventStart_eventCut (Nat.succ_le_of_lt hSourceEnd)
  have hTargetStart : T.highEventStart (F.height packet.sourceUUpper) = targetEvent + 1 := by
    rw [← hUpperRow, ← hTargetCut]
    exact T.highEventStart_eventCut (Nat.succ_le_of_lt hTargetEnd)
  have hWords := (p.expandDiagram_high_suffix_word_comparison hLast hCopies hRun hHigh hValid.toOrdered
    hSourceWidth hTargetWidth (bottomCandidateMap sourceU.1.val) (bottomCandidateMap packet.pair.u.1.val)
      sourceU.1.isLt packet.pair.u.1.isLt le_rfl packet.blocker_before.le le_rfl packet.pair.z_column
      hUDepth hZDepth).2.2
  rw [hSourceStart, hTargetStart] at hWords
  exact hComparison.mp (hWords.mpr hSourceWord)

theorem high_upper_barrier
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height packet.sourceUUpper)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    (Frame.ofMountain result).value packet.pair.u ≤ (Frame.ofMountain result).value packet.pair.z := by
  apply packet.high_upper_barrier_of_row hLast hLegal hCopies hRun hParentRight ?_ hHigh hLeft hHigher
  by_cases hMarkedIndex : sourceU.2.val ∈ (p.marked[sourceU.1.val]?.getD []).map Ref.index
  · have hMarked : BucketMem p.marked sourceU.1.val (Frame.ref sourceU) := by
      obtain ⟨marker, hm, hIndex⟩ := List.mem_map.mp hMarkedIndex
      have hColumn := (p.marker_iff.mp hm).1
      have hRef : marker = Frame.ref sourceU := by
        cases marker
        simp only [Frame.ref, Ref.mk.injEq]
        exact ⟨hColumn, hIndex⟩
      exact hRef ▸ hm
    have hStationary := packet.pair.uCopy.stationary_of_marked_high_upper hLast hMarked packet.source_u_upper hHigh
    exact packet.pair.uCopy.upper_height_of_stationary_marker hLast hMarked packet.source_parent
      hParentRight hStationary packet.source_u_upper packet.pair.u_ref packet.pair.u_upper
  · exact packet.pair.uCopy.upper_height_of_high hLast hMarkedIndex packet.source_u_upper
      hHigh packet.pair.u_ref packet.pair.u_upper

theorem recognize_high_upper
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height packet.sourceUUpper)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent :=
  packet.recognize_of_barrier hLast (expandDiagram_valid_of_success hLegal hRun)
    (expandDiagram_equations hLegal hRun).1 hLeft hParentRight
    (packet.high_upper_barrier hLast hLegal hCopies hRun hParentRight hHigh hLeft hHigher)

end SourceBlockerCopyPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.upper_height_of_high
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.high_upper_barrier
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.recognize_high_upper
