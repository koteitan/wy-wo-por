/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedBlockerWord.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedDepthWordTransport
import OmegaY.Expansion.ActualCommonParentWordStart
import OmegaY.Expansion.HighEventSuffix

/-!
# The complete actual word for a copied source blocker

Both comparison columns are actual copied columns. Their event families
are recovered from the copying history and aligned with the packet by
uniqueness of executed occurrences. The equal initial interval is removed
at the packet's actual common upper row. Only recognition of the complete
block-start prefix is used; no output numerical comparison or normality is
assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

set_option maxHeartbeats 1600000

private theorem contourCut_eq_of_source_eq
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {left right : (Frame.ofMountain p.reduced).Node}
    (leftCopy : EffectiveCopyOccurrence p block start references left result)
    (rightCopy : EffectiveCopyOccurrence p block start references right result)
    (hSource : left = right) (cut : Row) :
    leftCopy.contourCut cut = rightCopy.contourCut cut := by
  cases hSource
  exact leftCopy.contourCut_unique rightCopy cut

theorem DynamicBlockState.actual_copied_blocker_word
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
    (packet : AnySourceBlockerPacket p block start references sourceU sourceParent ambient)
    (hBefore : sourceU.1.val < next)
    (hBlockerRight : p.root.column < packet.blocker.1.val)
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent) :
    let T := Frame.ofMountain ambient
    let hWidth := (Nat.zero_le packet.pair.u.1.val).trans_lt packet.pair.u.1.isLt
    let full := T.frontierForests (bottomCandidateMap (ambient.size - 1))
      (eventFrontierNat s.ambient_valid.toOrdered hWidth) (ambient.size - 1)
    Forests.DepthWordLe full (T.highEventStart (T.height packet.pair.uUpper))
      T.lastEvent packet.pair.u.1.val packet.pair.z.1.val := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceWidth : 0 < p.reduced.size := (Nat.zero_le sourceU.1.val).trans_lt sourceU.1.isLt
  have hTargetWidth : 0 < ambient.size := (Nat.zero_le packet.pair.u.1.val).trans_lt packet.pair.u.1.isLt
  have hURight : p.root.column < sourceU.1.val := packet.pair.uCopy.state.next_lower
  have hZBefore : packet.blocker.1.val < next := packet.blocker_before.trans hBefore
  obtain ⟨zCopy, hZRef, _⟩ : ∃ zCopy : EffectiveCopyOccurrence p block start references packet.blocker ambient,
      Frame.ref packet.pair.z = zCopy.outputRef ∧ T.cell packet.pair.z = zCopy.read.outputCell := by
    rcases packet.pair.z_origin with hFixed | hCopied
    · exact False.elim ((not_lt_of_ge hFixed.1) hBlockerRight)
    · exact hCopied.2
  obtain ⟨previous, hPrevious, _, hUFront, hZFront, hCommon, hSourceWord⟩ := packet.source_full_depth_word
  let leftCopies := s.eventCopies history hLast sourceU.1 hURight hBefore
  let rightCopies := s.eventCopies history hLast packet.blocker.1 hBlockerRight hZBefore
  obtain ⟨floor, _, _, hLe⟩ := s.actual_copied_depth_word_transport history hLast hStartRun
    hSourceWidth hTargetWidth sourceU.1 packet.blocker.1 hURight hBlockerRight hBefore hZBefore
    packet.blocker_before.le hPrevious.le hCommon hKnown
  have hTargetWord := hLe hSourceWord
  have hJoint : jointEventCut leftCopies rightCopies previous =
      max (packet.pair.uCopy.contourCut (F.eventCut previous)) (zCopy.contourCut (F.eventCut previous)) := by
    unfold jointEventCut
    rw [contourCut_eq_of_source_eq (leftCopies previous) packet.pair.uCopy hUFront,
      contourCut_eq_of_source_eq (rightCopies previous) zCopy hZFront]
  let pairFloor : EventCutFloor T
      (max (packet.pair.uCopy.contourCut (F.eventCut previous)) (zCopy.contourCut (F.eventCut previous))) :=
    { event := floor.event
      event_end := floor.event_end
      below := by simpa only [← hJoint] using floor.below
      maximal := by
        intro row hMem hRow
        exact floor.maximal row hMem (hRow.trans_eq hJoint.symm) }
  obtain ⟨upperPrevious, hUpperPrevious, hUpperCut, _, _⟩ :=
    Frame.upper_at_positive_event s.ambient_valid.toOrdered packet.pair.u_real packet.pair.u_upper
  have hUpperRef : Frame.ref packet.pair.uUpper =
      ⟨packet.pair.uCopy.outputRef.column, packet.pair.uCopy.outputRef.index + 1⟩ := by
    have hSpec := Frame.upper_spec packet.pair.u_upper
    have hUColumn := congrArg Ref.column packet.pair.u_ref
    have hUIndex := congrArg Ref.index packet.pair.u_ref
    exact congrArg₂ Ref.mk ((congrArg Fin.val hSpec.1).trans hUColumn)
      (hSpec.2.trans (congrArg (fun index => index + 1) hUIndex))
  have hUpperRead : Canonical.cellAt ambient
      ⟨packet.pair.uCopy.outputRef.column, packet.pair.uCopy.outputRef.index + 1⟩ =
      .ok (T.cell packet.pair.uUpper) := by
    rw [← hUpperRef]
    exact Canonical.cellAt_of_frame_node ambient packet.pair.uUpper
  have hStarts := s.common_parent_word_start_iff history hLast hStartRun hBefore hZBefore
    packet.blocker_before.le packet.pair.uCopy zCopy hSourceWidth hTargetWidth
    packet.source_parent packet.source_last_parent packet.source_u_upper packet.source_z_upper
    (F.eventCut_one_le previous) hUFront hZFront pairFloor
    (Nat.succ_le_of_lt hUpperPrevious) hUpperRead hUpperCut
  have hOutputWord : Forests.DepthWordLe
      (T.frontierForests (bottomCandidateMap (ambient.size - 1))
        (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1))
      (pairFloor.event + 1) T.lastEvent packet.pair.uCopy.outputRef.column zCopy.outputRef.column := by
    simpa only [pairFloor, packet.pair.uCopy.source_column, zCopy.source_column] using hTargetWord
  have hBoundedWord := hStarts.2.2.2.mp hOutputWord
  have hUColumn : packet.pair.u.1.val = packet.pair.uCopy.outputRef.column :=
    congrArg Ref.column packet.pair.u_ref
  have hZColumn : packet.pair.z.1.val = zCopy.outputRef.column := congrArg Ref.column hZRef
  have hBounds := Frame.depthWord_bound_iff s.ambient_valid.toOrdered hTargetWidth
    (bottomCandidateMap packet.pair.uCopy.outputRef.column) (bottomCandidateMap (ambient.size - 1))
    (start := upperPrevious + 1) (finish := T.lastEvent)
    (show packet.pair.uCopy.outputRef.column < T.width by rw [← hUColumn]; exact packet.pair.u.1.isLt)
    le_rfl (show zCopy.outputRef.column ≤ packet.pair.uCopy.outputRef.column by
      rw [← hUColumn, ← hZColumn]; exact packet.pair.z_column)
  have hFullWord := hBounds.2.2.mp hBoundedWord
  have hStart : T.highEventStart (T.height packet.pair.uUpper) = upperPrevious + 1 := by
    rw [← hUpperCut]
    exact T.highEventStart_eventCut (Nat.succ_le_of_lt hUpperPrevious)
  change Forests.DepthWordLe
    (T.frontierForests (bottomCandidateMap (ambient.size - 1))
      (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1))
    (T.highEventStart (T.height packet.pair.uUpper)) T.lastEvent packet.pair.u.1.val packet.pair.z.1.val
  rw [hStart, hUColumn, hZColumn]
  exact hFullWord

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_copied_blocker_word
