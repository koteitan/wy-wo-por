/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSplitStableInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentEventInterval

/-!
# The stable interval immediately before any true source split

Old source frontiers share a parent. Their actual copied immediate uppers
have one row regardless of old marker status. Every target event before
that row and above the old shared cut has equal depth. When either new
source upper is marked, the common upper is exactly its physical row.
The new numerical parents are unrestricted throughout this module.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

private theorem marked_index_iff {front : List Nat} {last : Nat}
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

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {u z nextU nextZ parent : (Frame.ofMountain p.reduced).Node}
  (uCopy : EffectiveCopyOccurrence p block start references u result)
  (zCopy : EffectiveCopyOccurrence p block start references z result)

theorem common_parent_upper_reads_all (hLast : 1 < last)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUUpper : (Frame.ofMountain p.reduced).upper u = some nextU)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some nextZ)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    ∃ upperU upperZ,
      Canonical.cellAt result ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok upperU ∧
      Canonical.cellAt result ⟨zCopy.outputRef.column, zCopy.outputRef.index + 1⟩ = .ok upperZ ∧
      (Frame.ofMountain p.reduced).height nextU = (Frame.ofMountain p.reduced).height nextZ ∧
      upperU.row = upperZ.row := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hu := frontierAt_spec hNormal.toOrdered hCut u.1
  have hz := frontierAt_spec hNormal.toOrdered hCut z.1
  have hUReal : Real u := hUFront ▸ hu.2.1
  have hZReal : Real z := hZFront ▸ hz.2.1
  have hULow : F.height u ≤ cut := hUFront ▸ hu.2.2.1
  have hZLow : F.height z ≤ cut := hZFront ▸ hz.2.2.1
  have hSourceRows : F.height nextU = F.height nextZ := by
    rcases le_total (F.height z) (F.height u) with hle | hle
    · exact hNormal.common_parent_upper_rows hUP hZP hUUpper hZUpper hle
        (hULow.trans_lt (hz.2.2.2.2 nextZ (hZFront.symm ▸ hZUpper)))
    · exact (hNormal.common_parent_upper_rows hZP hUP hZUpper hUUpper hle
        (hZLow.trans_lt (hu.2.2.2.2 nextU (hUFront.symm ▸ hUUpper)))).symm
  have hMarkedIff := p.common_parent_marked_iff_at_cut hUP hZP hCut hUFront hZFront
  by_cases hm : BucketMem p.marked u.1.val (Frame.ref u)
  · obtain ⟨upperU, hReadU, hRowU⟩ := uCopy.upper_lift_read_all hLast hUReal hUUpper
    obtain ⟨upperZ, hReadZ, hRowZ⟩ := zCopy.upper_lift_read_all hLast hZReal hZUpper
    refine ⟨upperU, upperZ, hReadU, hReadZ, hSourceRows, ?_⟩
    rw [hRowU, hRowZ, uCopy.contourCut_function_eq_of_marked_frontiers zCopy hm
      (hMarkedIff.mp hm) hCut hUFront hZFront, hSourceRows]
  · obtain ⟨upperU, upperZ, hReadU, hReadZ, hRows⟩ := uCopy.common_parent_upper_rows zCopy hLast
      (fun hi => hm ((marked_index_iff p u).mp hi))
      (fun hi => hm (hMarkedIff.mpr ((marked_index_iff p z).mp hi)))
      hUP hZP hUUpper hZUpper hSourceRows
    exact ⟨upperU, upperZ, hReadU, hReadZ, hSourceRows, hRows⟩

theorem ownCut_lt_actual_upper (hLast : 1 < last) (hValid : MountainValid result)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    {upperCell : Cell}
    (hUpperRead : Canonical.cellAt result ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok upperCell) :
    uCopy.contourCut cut < upperCell.row := by
  obtain ⟨hLift, node, hRef, _, hAt⟩ := uCopy.frontierAt_own_lift_all hLast hValid hCut hFront
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hUpper := Frame.upper_of_refs hRef hUpperRef
  exact ((frontierAt_spec hValid.toOrdered hLift node.1).2.2.2.2 upper (hAt.symm ▸ hUpper)).trans_eq
    (congrArg Cell.row hUpperCell)

end EffectiveCopyOccurrence

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)

include s history hLast hStartRun

theorem DynamicBlockState.common_parent_upper_stable_interval
    {u z nextU nextZ parent : (Frame.ofMountain p.reduced).Node}
    (hUBefore : u.1.val < next) (hZBefore : z.1.val < next)
    (uCopy : EffectiveCopyOccurrence p block start references u ambient)
    (zCopy : EffectiveCopyOccurrence p block start references z ambient)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUUpper : (Frame.ofMountain p.reduced).upper u = some nextU)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some nextZ)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    ∃ upperU upperZ,
      Canonical.cellAt ambient ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok upperU ∧
      Canonical.cellAt ambient ⟨zCopy.outputRef.column, zCopy.outputRef.index + 1⟩ = .ok upperZ ∧
      upperU.row = upperZ.row ∧
      max (uCopy.contourCut cut) (zCopy.contourCut cut) < upperU.row ∧
      ∀ event, max (uCopy.contourCut cut) (zCopy.contourCut cut) ≤ (Frame.ofMountain ambient).eventCut event →
        (Frame.ofMountain ambient).eventCut event < upperU.row →
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
          uCopy.outputRef.column =
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
          zCopy.outputRef.column := by
  obtain ⟨upperU, upperZ, hReadU, hReadZ, _, hRows⟩ :=
    uCopy.common_parent_upper_reads_all zCopy hLast hUP hZP hUUpper hZUpper hCut hUFront hZFront
  have hBound : max (uCopy.contourCut cut) (zCopy.contourCut cut) < upperU.row := max_lt
    (uCopy.ownCut_lt_actual_upper hLast s.ambient_valid hCut hUFront hReadU)
    ((zCopy.ownCut_lt_actual_upper hLast s.ambient_valid hCut hZFront hReadZ).trans_eq hRows.symm)
  refine ⟨upperU, upperZ, hReadU, hReadZ, hRows, hBound, ?_⟩
  intro event hLow hHigh
  have hULow : uCopy.read.outputCell.row ≤ (Frame.ofMountain ambient).eventCut event :=
    (uCopy.output_row_le_contourCut (hUFront ▸
      (frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered hCut u.1).2.2.1)).trans
      ((le_max_left _ _).trans hLow)
  have hZLow : zCopy.read.outputCell.row ≤ (Frame.ofMountain ambient).eventCut event :=
    (zCopy.output_row_le_contourCut (hZFront ▸
      (frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered hCut z.1).2.2.1)).trans
      ((le_max_right _ _).trans hLow)
  exact s.copied_depth_eq_at_frontiers_of_source_cut history hLast hStartRun hUBefore hZBefore
    uCopy zCopy hSourceWidth hTargetWidth hCut hUFront hZFront (hUP.trans hZP.symm)
    (uCopy.frontierAt_of_upper_read s.ambient_valid ((Frame.ofMountain ambient).eventCut_one_le event) hReadU hULow hHigh)
    (zCopy.frontierAt_of_upper_read s.ambient_valid ((Frame.ofMountain ambient).eventCut_one_le event) hReadZ hZLow
      (hHigh.trans_eq hRows))

theorem DynamicBlockState.before_marked_split_interval
    {u z nextU nextZ parent : (Frame.ofMountain p.reduced).Node}
    (hUBefore : u.1.val < next) (hZBefore : z.1.val < next)
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
    (hMarked : BucketMem p.marked nextU.1.val (Frame.ref nextU) ∨
      BucketMem p.marked nextZ.1.val (Frame.ref nextZ)) :
    max (uCopy.contourCut cut) (zCopy.contourCut cut) < (Frame.ofMountain p.reduced).height nextU ∧
      ∀ event, max (uCopy.contourCut cut) (zCopy.contourCut cut) ≤ (Frame.ofMountain ambient).eventCut event →
        (Frame.ofMountain ambient).eventCut event < (Frame.ofMountain p.reduced).height nextU →
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
          uCopy.outputRef.column =
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
          zCopy.outputRef.column := by
  obtain ⟨upperU, upperZ, hReadU, hReadZ, hRows, hBound, hStable⟩ :=
    s.common_parent_upper_stable_interval history hLast hStartRun hUBefore hZBefore uCopy zCopy
      hSourceWidth hTargetWidth hUP hZP hUUpper hZUpper hCut hUFront hZFront
  have hPhysical : upperU.row = (Frame.ofMountain p.reduced).height nextU := by
    rcases hMarked with hu | hz
    · have hReal : Real u := hUFront ▸
        (frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered hCut u.1).2.1
      obtain ⟨actual, hActual, hRow⟩ := uCopy.upper_physical_row_of_marked hLast hReal hUUpper hu
      exact (congrArg Cell.row (Except.ok.inj (hReadU.symm.trans hActual))).trans hRow
    · have hReal : Real z := hZFront ▸
        (frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered hCut z.1).2.1
      obtain ⟨actual, hActual, hRow⟩ := zCopy.upper_physical_row_of_marked hLast hReal hZUpper hz
      obtain ⟨_, _, _, _, hSourceRows, _⟩ :=
        uCopy.common_parent_upper_reads_all zCopy hLast hUP hZP hUUpper hZUpper hCut hUFront hZFront
      exact hRows.trans ((congrArg Cell.row (Except.ok.inj (hReadZ.symm.trans hActual))).trans
        (hRow.trans hSourceRows.symm))
  exact ⟨hBound.trans_eq hPhysical, fun event hLow hHigh => hStable event hLow (hHigh.trans_eq hPhysical.symm)⟩

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.common_parent_upper_reads_all
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.ownCut_lt_actual_upper
#print axioms OmegaY.Expansion.DynamicBlockState.common_parent_upper_stable_interval
#print axioms OmegaY.Expansion.DynamicBlockState.before_marked_split_interval
