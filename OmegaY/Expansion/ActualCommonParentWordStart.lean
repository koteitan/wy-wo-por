/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonParentWordStart.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSplitStableInterval
import OmegaY.Expansion.DepthWordStart
import OmegaY.Expansion.ActualAnyLastBlocker

/-!
# Genuine numerical-comparison starts from actual common-parent copies

The full copied word begins just after the floor of the shared contour
cut. The numerical comparison begins at the actual common upper event and
uses only columns through the current child. The entire removed prefix is
proved equal from actual copied upper reads. Column-bound independence then
gives the exact Eq/Lt/Le equivalence, without copied normality or a target
value inequality. The common source parent may be fixed, root, or copied.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.common_parent_word_start_iff
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {u z nextU nextZ parent : (Frame.ofMountain p.reduced).Node}
    (hUBefore : u.1.val < next) (hZBefore : z.1.val < next) (hColumn : z.1.val ≤ u.1.val)
    (uCopy : EffectiveCopyOccurrence p block start references u ambient)
    (zCopy : EffectiveCopyOccurrence p block start references z ambient)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUUpper : (Frame.ofMountain p.reduced).upper u = some nextU)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some nextZ)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z)
    (floor : EventCutFloor (Frame.ofMountain ambient) (max (uCopy.contourCut cut) (zCopy.contourCut cut)))
    {upperEvent : Nat} (hUpperEnd : upperEvent ≤ (Frame.ofMountain ambient).lastEvent)
    {upperCell : Cell}
    (hUpperRead : Canonical.cellAt ambient ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok upperCell)
    (hUpperCut : (Frame.ofMountain ambient).eventCut upperEvent = upperCell.row) :
    let T := Frame.ofMountain ambient
    let full := T.frontierForests (bottomCandidateMap (ambient.size - 1))
      (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1)
    let bounded := T.frontierForests (bottomCandidateMap uCopy.outputRef.column)
      (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) uCopy.outputRef.column
    floor.event + 1 ≤ upperEvent ∧
      (Forests.DepthWordEq full (floor.event + 1) T.lastEvent uCopy.outputRef.column zCopy.outputRef.column ↔
        Forests.DepthWordEq bounded upperEvent T.lastEvent uCopy.outputRef.column zCopy.outputRef.column) ∧
      (Forests.DepthWordLt full (floor.event + 1) T.lastEvent uCopy.outputRef.column zCopy.outputRef.column ↔
        Forests.DepthWordLt bounded upperEvent T.lastEvent uCopy.outputRef.column zCopy.outputRef.column) ∧
      (Forests.DepthWordLe full (floor.event + 1) T.lastEvent uCopy.outputRef.column zCopy.outputRef.column ↔
        Forests.DepthWordLe bounded upperEvent T.lastEvent uCopy.outputRef.column zCopy.outputRef.column) := by
  let T := Frame.ofMountain ambient
  let full := T.frontierForests (bottomCandidateMap (ambient.size - 1))
    (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1)
  obtain ⟨actualU, actualZ, hReadU, _, _, hBelow, hStable⟩ :=
    s.common_parent_upper_stable_interval history hLast hStartRun hUBefore hZBefore uCopy zCopy
      hSourceWidth hTargetWidth hUP hZP hUUpper hZUpper hCut hUFront hZFront
  have hActual : actualU = upperCell := Except.ok.inj (hReadU.symm.trans hUpperRead)
  have hActualRow : actualU.row = T.eventCut upperEvent := (congrArg Cell.row hActual).trans hUpperCut.symm
  have hStart : floor.event + 1 ≤ upperEvent := floor.next_le_of_cut_lt (hBelow.trans_eq hActualRow)
  have hPrefix : ∀ event, floor.event + 1 ≤ event → event < upperEvent →
      Forests.eventDepth full event uCopy.outputRef.column = Forests.eventDepth full event zCopy.outputRef.column := by
    intro event hEventStart hEventEnd
    have hLower := floor.cut_lt_of_next_le hEventStart (hEventEnd.le.trans hUpperEnd)
    have hHigher : T.eventCut event < actualU.row :=
      ((T.eventCut_strict_step (hEventEnd.trans_le hUpperEnd)).trans_le
        (T.eventCut_monotone (Nat.succ_le_of_lt hEventEnd))).trans_eq hActualRow.symm
    exact hStable event hLower.le hHigher
  have hBound : uCopy.outputRef.column < T.width := by
    obtain ⟨nodes, hNodes, _⟩ := cellAt_ok_iff.mp uCopy.output_read
    exact (Array.getElem?_eq_some_iff.mp hNodes).1
  have hZColumn : zCopy.outputRef.column ≤ uCopy.outputRef.column := by
    rw [zCopy.source_column, uCopy.source_column]
    omega
  have hBounds := Frame.depthWord_bound_iff s.ambient_valid.toOrdered hTargetWidth
    (bottomCandidateMap uCopy.outputRef.column) (bottomCandidateMap (ambient.size - 1))
    (start := upperEvent) (finish := T.lastEvent) hBound le_rfl hZColumn
  exact ⟨hStart,
    (Forests.depthWordEq_trim_equal_prefix hStart hPrefix).trans hBounds.1.symm,
    (Forests.depthWordLt_trim_equal_prefix hStart hPrefix).trans hBounds.2.1.symm,
    (Forests.depthWordLe_trim_equal_prefix hStart hPrefix).trans hBounds.2.2.symm⟩

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

/-- The genuine source comparison start, its predecessor frontiers, and
the full-width source word are returned together. This applies to all
three parent locations and both fixed and copied source blockers. -/
theorem source_full_depth_word :
    let F := Frame.ofMountain p.reduced
    let hN := build_normal_of_success p.reduced_build
    let hWidth := (Nat.zero_le sourceU.1.val).trans_lt sourceU.1.isLt
    let full := F.frontierForests (bottomCandidateMap (p.reduced.size - 1))
      (eventFrontierNat hN.toOrdered hWidth) (p.reduced.size - 1)
    ∃ previous, previous < F.lastEvent ∧ F.eventCut (previous + 1) = F.height packet.sourceUUpper ∧
      eventFrontier hN.toOrdered previous sourceU.1 = sourceU ∧
      eventFrontier hN.toOrdered previous packet.blocker.1 = packet.blocker ∧
      F.P (eventFrontier hN.toOrdered previous sourceU.1) =
        F.P (eventFrontier hN.toOrdered previous packet.blocker.1) ∧
      Forests.DepthWordLe full (previous + 1) F.lastEvent sourceU.1.val packet.blocker.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  have hWidth : 0 < p.reduced.size := (Nat.zero_le sourceU.1.val).trans_lt sourceU.1.isLt
  obtain ⟨previous, hPrevious, hCut, hWord⟩ := packet.source_depth_word
  have hUFront := (eventFrontier_pair_of_upper_cut hNormal.toOrdered hPrevious packet.source_u_upper hCut).1
  have hZFront := (eventFrontier_pair_of_upper_cut hNormal.toOrdered hPrevious packet.source_z_upper
    (hCut.trans packet.source_upper_height)).1
  have hBounds := Frame.depthWord_bound_iff hNormal.toOrdered hWidth
    (bottomCandidateMap sourceU.1.val) (bottomCandidateMap (p.reduced.size - 1))
    (start := previous + 1) (finish := (Frame.ofMountain p.reduced).lastEvent)
    sourceU.1.isLt le_rfl packet.blocker_before.le
  refine ⟨previous, hPrevious, hCut, hUFront, hZFront, ?_, hBounds.2.2.mp hWord⟩
  rw [hUFront, hZFront]
  exact packet.source_parent.trans packet.source_last_parent.symm

end AnySourceBlockerPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.common_parent_word_start_iff
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.source_full_depth_word
