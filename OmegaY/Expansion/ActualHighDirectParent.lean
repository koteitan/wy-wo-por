/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighDirectParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveCandidate
import OmegaY.Expansion.RecordedEffectiveEdges
import OmegaY.Expansion.ActualCommonMarkerBands
import OmegaY.Geometry.ReferenceLadder

/-!
# Actual numerical recognition for a high direct source candidate

The source Q is its source P, and this candidate is above the common
last-top threshold. Actual execution supplies the copied Q identity,
the raw edge, positivity and backfill sums. No numerical recognition
assumption on any target node is needed in this direct-hit branch.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem MountainSums.P_of_Q_rawParent {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {u parent : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hQ : (Frame.ofMountain mountain).Q u = some parent)
    (hRaw : (Frame.ofMountain mountain).rawParent u = some parent) :
    (Frame.ofMountain mountain).P u = some parent := by
  obtain ⟨upper, hUpper, _⟩ := Frame.rawParent_spec hRaw
  obtain ⟨actual, hActual, _, hPositive, hSmall, _⟩ := hSums.rawParent_upper hValid hReal hUpper
  have he : actual = parent := Option.some.inj (hActual.symm.trans hRaw)
  subst actual
  exact (Frame.P_iff hValid.toOrdered).mpr ⟨parent, hQ, .here hPositive hSmall⟩

theorem DynamicBlockState.recorded_high_direct_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {source parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hDirect : (Frame.ofMountain p.reduced).Q source = some parent)
    (hParentRight : p.root.column < parent.1.val) (hBefore : source.1.val < next)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent) :
    ∃ (sourceCopy : EffectiveCopyOccurrence p block start references source ambient)
      (parentCopy : EffectiveCopyOccurrence p block start references parent ambient)
      (u father : (Frame.ofMountain ambient).Node),
      Frame.ref u = sourceCopy.outputRef ∧ Frame.ref father = parentCopy.outputRef ∧
      (Frame.ofMountain ambient).Q u = some father ∧
      (Frame.ofMountain ambient).rawParent u = some father ∧
      (Frame.ofMountain ambient).P u = some father ∧
      findParent ambient sourceCopy.outputRef = .ok parentCopy.outputRef := by
  have hNormal := build_normal_of_success p.reduced_build
  have hParentLeft := Frame.P_column_lt hNormal.toOrdered hParent
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨sourceCopy⟩ := s.prior_effective_occurrence history hLast
    (hParentRight.trans hParentLeft) hBefore
  obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast
    hParentRight (hParentLeft.trans hBefore)
  have hSourceHigh := hHigh.trans (Frame.Q_height_le hNormal.toOrdered hDirect)
  have hUnmarked := sourceCopy.state.high_source_not_marked hLast source.1.isLt
    sourceCopy.data sourceCopy.read.source_at hSourceHigh
  obtain ⟨u, father, hURef, hFatherRef, hQ, _⟩ := sourceCopy.candidate_eq_high hLast
    s.ambient_valid hUnmarked parentCopy hDirect hParentRight.le hHigh
  have hRaw := (s.recorded_effective_parent history hLast hParent hParentRight hBefore
    sourceCopy parentCopy).rawParent hURef hFatherRef
  have hUReal : Frame.Real u := by
    have hIndex := congrArg Ref.index hURef
    change u.2.val = sourceCopy.read.outputIndex at hIndex
    change 0 < u.2.val
    rw [hIndex]
    exact sourceCopy.read.output_real hSourceReal
  have hP := (s.mountainSums_of_start_run history hLast hStartRun).P_of_Q_rawParent
    s.ambient_valid hUReal hQ hRaw
  refine ⟨sourceCopy, parentCopy, u, father, hURef, hFatherRef, hQ, hRaw, hP, ?_⟩
  simpa only [hURef, hFatherRef] using (Executable.findParent_ref_iff s.ambient_valid.toOrdered u father).mpr hP

end OmegaY.Expansion

#print axioms OmegaY.Expansion.MountainSums.P_of_Q_rawParent
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_high_direct_parent
