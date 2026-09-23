/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSharedContourCut.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowPathDepth
import OmegaY.Expansion.RawCommonFrontierDepth

/-!+# A shared actual cut while source frontier parents agree

Each unmarked source frontier is copied to the frontier of its own lifted
cut. If two such source frontiers have the same actual source parent, their
copied immediate uppers have the same height. The maximum of the two lifted
cuts therefore lies in both actual frontier intervals. Its finite floor
event is shared by both columns, even when the two lifts are different.

This is a pointwise synchrony result. Agreement only in an earlier candidate
forest does not supply the common current parent used here, and no global
monotone event sampling is asserted.
-/

namespace OmegaY.Geometry.Frame

theorem frontierAt_common_upper_max {F : Frame} (hF : F.Ordered)
    {left right leftUpper rightUpper : F.Node} {leftCut rightCut : Row}
    (hLeftCut : (1 : Row) ≤ leftCut) (hRightCut : (1 : Row) ≤ rightCut)
    (hLeft : frontierAt hF leftCut hLeftCut left.1 = left)
    (hRight : frontierAt hF rightCut hRightCut right.1 = right)
    (hLeftUpper : F.upper left = some leftUpper)
    (hRightUpper : F.upper right = some rightUpper)
    (hSame : F.height leftUpper = F.height rightUpper) :
    let hCut : (1 : Row) ≤ max leftCut rightCut := hLeftCut.trans (le_max_left _ _)
    frontierAt hF (max leftCut rightCut) hCut left.1 = left ∧
      frontierAt hF (max leftCut rightCut) hCut right.1 = right := by
  have hl := frontierAt_spec hF hLeftCut left.1
  have hr := frontierAt_spec hF hRightCut right.1
  have hlBelow : F.height left ≤ leftCut := hLeft ▸ hl.2.2.1
  have hrBelow : F.height right ≤ rightCut := hRight ▸ hr.2.2.1
  have hlUpper : leftCut < F.height leftUpper :=
    hl.2.2.2.2 leftUpper (hLeft.symm ▸ hLeftUpper)
  have hrUpper : rightCut < F.height rightUpper :=
    hr.2.2.2.2 rightUpper (hRight.symm ▸ hRightUpper)
  have hMax : max leftCut rightCut < F.height leftUpper := max_lt
    hlUpper (hrUpper.trans_eq hSame.symm)
  constructor
  · apply frontierAt_eq_of_upper_barrier hF (hLeftCut.trans (le_max_left _ _)) (node := left)
    · exact hlBelow.trans (le_max_left _ _)
    · intro upper hUpper
      have he := Option.some.inj (hLeftUpper.symm.trans hUpper)
      exact he ▸ hMax
  · apply frontierAt_eq_of_upper_barrier hF (hLeftCut.trans (le_max_left _ _)) (node := right)
    · exact hrBelow.trans (le_max_right _ _)
    · intro upper hUpper
      have he := Option.some.inj (hRightUpper.symm.trans hUpper)
      exact he ▸ hMax.trans_eq hSame

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

private theorem frame_upper_of_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : Frame.ref before = ⟨column, index⟩)
    (hAfter : Frame.ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

/-- Both actual occurrences at their own cuts, at the shared maximum cut,
and at the one event enumerated below that maximum. -/
structure SharedContourFrontier {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z : (Frame.ofMountain p.reduced).Node}
    (uCopy : EffectiveCopyOccurrence p block start references u result)
    (zCopy : EffectiveCopyOccurrence p block start references z result)
    (cut : Row) (hValid : MountainValid result) where
  u_cut_one : (1 : Row) ≤ uCopy.contourCut cut
  z_cut_one : (1 : Row) ≤ zCopy.contourCut cut
  shared_cut_one : (1 : Row) ≤ max (uCopy.contourCut cut) (zCopy.contourCut cut)
  uNode : (Frame.ofMountain result).Node
  zNode : (Frame.ofMountain result).Node
  u_ref : Frame.ref uNode = uCopy.outputRef
  z_ref : Frame.ref zNode = zCopy.outputRef
  u_cell : (Frame.ofMountain result).cell uNode = uCopy.read.outputCell
  z_cell : (Frame.ofMountain result).cell zNode = zCopy.read.outputCell
  u_own : frontierAt hValid.toOrdered (uCopy.contourCut cut) u_cut_one uNode.1 = uNode
  z_own : frontierAt hValid.toOrdered (zCopy.contourCut cut) z_cut_one zNode.1 = zNode
  u_shared : frontierAt hValid.toOrdered (max (uCopy.contourCut cut) (zCopy.contourCut cut))
    shared_cut_one uNode.1 = uNode
  z_shared : frontierAt hValid.toOrdered (max (uCopy.contourCut cut) (zCopy.contourCut cut))
    shared_cut_one zNode.1 = zNode
  event : Nat
  event_end : event ≤ (Frame.ofMountain result).lastEvent
  event_below : (Frame.ofMountain result).eventCut event ≤
    max (uCopy.contourCut cut) (zCopy.contourCut cut)
  event_maximal : ∀ row ∈ (Frame.ofMountain result).eventCuts,
    row ≤ max (uCopy.contourCut cut) (zCopy.contourCut cut) →
      row ≤ (Frame.ofMountain result).eventCut event
  all_frontiers : ∀ column, eventFrontier hValid.toOrdered event column =
    frontierAt hValid.toOrdered (max (uCopy.contourCut cut) (zCopy.contourCut cut)) shared_cut_one column

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {u z : (Frame.ofMountain p.reduced).Node}
  (uCopy : EffectiveCopyOccurrence p block start references u result)
  (zCopy : EffectiveCopyOccurrence p block start references z result)

/-- The source-frontier premises are at one actual source cut, so their
overlap and the common upper row are derived without a source row-order
premise. Every target frontier and the shared event are conclusions. -/
theorem shared_contour_frontier (hLast : 1 < last) (hValid : MountainValid result)
    (hUUnmarked : u.2.val ∉ (p.marked[u.1.val]?.getD []).map Ref.index)
    (hZUnmarked : z.2.val ∉ (p.marked[z.1.val]?.getD []).map Ref.index)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    Nonempty (SharedContourFrontier uCopy zCopy cut hValid) := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨uUpper, hUUpper⟩ := hNormal.upper_of_parent hUP
  obtain ⟨zUpper, hZUpper⟩ := hNormal.upper_of_parent hZP
  have hu := frontierAt_spec hNormal.toOrdered hCut u.1
  have hz := frontierAt_spec hNormal.toOrdered hCut z.1
  have huBelow : (Frame.ofMountain p.reduced).height u ≤ cut := hUFront ▸ hu.2.2.1
  have hzBelow : (Frame.ofMountain p.reduced).height z ≤ cut := hZFront ▸ hz.2.2.1
  have huAbove : cut < (Frame.ofMountain p.reduced).height uUpper :=
    hu.2.2.2.2 uUpper (hUFront.symm ▸ hUUpper)
  have hzAbove : cut < (Frame.ofMountain p.reduced).height zUpper :=
    hz.2.2.2.2 zUpper (hZFront.symm ▸ hZUpper)
  have hSourceSame : (Frame.ofMountain p.reduced).height uUpper =
      (Frame.ofMountain p.reduced).height zUpper := by
    rcases le_total ((Frame.ofMountain p.reduced).height z) ((Frame.ofMountain p.reduced).height u) with hle | hle
    · exact hNormal.common_parent_upper_rows hUP hZP hUUpper hZUpper hle
        (huBelow.trans_lt hzAbove)
    · exact (hNormal.common_parent_upper_rows hZP hUP hZUpper hUUpper hle
        (hzBelow.trans_lt huAbove)).symm
  obtain ⟨upperUCell, upperZCell, hURead, hZRead, hSame⟩ :=
    uCopy.common_parent_upper_rows zCopy hLast hUUnmarked hZUnmarked hUP hZP hUUpper hZUpper hSourceSame
  obtain ⟨hUCut, uNode, hURef, hUCell, hUOwn⟩ :=
    uCopy.frontierAt_own_lift hLast hValid hUUnmarked hCut hUFront
  obtain ⟨hZCut, zNode, hZRef, hZCell, hZOwn⟩ :=
    zCopy.frontierAt_own_lift hLast hValid hZUnmarked hCut hZFront
  obtain ⟨upperU, hUpperURef, hUpperUCell⟩ := Canonical.frame_node_of_cellAt hURead
  obtain ⟨upperZ, hUpperZRef, hUpperZCell⟩ := Canonical.frame_node_of_cellAt hZRead
  have hActualUUpper := frame_upper_of_refs hURef hUpperURef
  have hActualZUpper := frame_upper_of_refs hZRef hUpperZRef
  have hRows : (Frame.ofMountain result).height upperU = (Frame.ofMountain result).height upperZ := by
    change ((Frame.ofMountain result).cell upperU).row = ((Frame.ofMountain result).cell upperZ).row
    rw [hUpperUCell, hUpperZCell]
    exact hSame
  obtain ⟨hUShared, hZShared⟩ := frontierAt_common_upper_max hValid.toOrdered hUCut hZCut
    hUOwn hZOwn hActualUUpper hActualZUpper hRows
  have hShared : (1 : Row) ≤ max (uCopy.contourCut cut) (zCopy.contourCut cut) :=
    hUCut.trans (le_max_left _ _)
  obtain ⟨event, hEvent, hBelow, hMax, hFrontiers⟩ := event_floor_at_cut hValid.toOrdered hShared
  exact ⟨⟨hUCut, hZCut, hShared, uNode, zNode, hURef, hZRef, hUCell, hZCell,
    hUOwn, hZOwn, hUShared, hZShared, event, hEvent, hBelow, hMax, hFrontiers⟩⟩

end EffectiveCopyOccurrence

namespace SharedContourFrontier

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {u z : (Frame.ofMountain p.reduced).Node}
  {uCopy : EffectiveCopyOccurrence p block start references u result}
  {zCopy : EffectiveCopyOccurrence p block start references z result}
  {cut : Row} {hValid : MountainValid result}
  (data : SharedContourFrontier uCopy zCopy cut hValid)

theorem u_frontier : eventFrontier hValid.toOrdered data.event data.uNode.1 = data.uNode :=
  (data.all_frontiers data.uNode.1).trans data.u_shared

theorem z_frontier : eventFrontier hValid.toOrdered data.event data.zNode.1 = data.zNode :=
  (data.all_frontiers data.zNode.1).trans data.z_shared

/-- An earlier own-cut certificate may use any event at which this same
actual occurrence is the frontier. Raw geometry transports its depth to
the shared event without assuming equality of the two cut maps. -/
theorem u_depth (hRaw : (Frame.ofMountain result).RawRowGeometry)
    (hFather : (Frame.ofMountain result).RawFatherUpperBound)
    (hWidth : 0 < result.size) {bound : Nat} (hBound : bound < result.size)
    (hNode : data.uNode.1.val ≤ bound) {ownEvent : Nat}
    (hOwn : eventFrontier hValid.toOrdered ownEvent data.uNode.1 = data.uNode) :
    parentDepth (eventParentMap hValid.toOrdered hWidth bound data.event) data.uNode.1.val =
      parentDepth (eventParentMap hValid.toOrdered hWidth bound ownEvent) data.uNode.1.val :=
  raw_event_parentDepth_of_common_frontier hValid.toOrdered hRaw hFather hWidth hBound
    hNode hOwn data.u_frontier

theorem z_depth (hRaw : (Frame.ofMountain result).RawRowGeometry)
    (hFather : (Frame.ofMountain result).RawFatherUpperBound)
    (hWidth : 0 < result.size) {bound : Nat} (hBound : bound < result.size)
    (hNode : data.zNode.1.val ≤ bound) {ownEvent : Nat}
    (hOwn : eventFrontier hValid.toOrdered ownEvent data.zNode.1 = data.zNode) :
    parentDepth (eventParentMap hValid.toOrdered hWidth bound data.event) data.zNode.1.val =
      parentDepth (eventParentMap hValid.toOrdered hWidth bound ownEvent) data.zNode.1.val :=
  raw_event_parentDepth_of_common_frontier hValid.toOrdered hRaw hFather hWidth hBound
    hNode hOwn data.z_frontier

end SharedContourFrontier
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.frontierAt_common_upper_max
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.shared_contour_frontier
#print axioms OmegaY.Expansion.SharedContourFrontier.u_frontier
#print axioms OmegaY.Expansion.SharedContourFrontier.z_frontier
#print axioms OmegaY.Expansion.SharedContourFrontier.u_depth
#print axioms OmegaY.Expansion.SharedContourFrontier.z_depth
