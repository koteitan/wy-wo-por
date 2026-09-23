/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualDirectParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighDirectParent
import OmegaY.Expansion.ActualStationaryEffectiveCandidate

/-!
# Numerical parent recognition for every nonmarker direct source hit

The actual source Q equals its P and that parent is strictly right of the
root. The copied node and copied candidate may rise independently. Their
actual Q identity and stored edge, with positive backfill sums, give the
copied numerical parent without any target recognition assumption.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem DynamicBlockState.recorded_nonmarker_direct_parent
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
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index) :
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
  obtain ⟨u, father, hURef, hFatherRef, hQ, _⟩ := sourceCopy.candidate_eq_nonmarker hLast
    s.ambient_valid hUnmarked parentCopy hParent hDirect hParentRight
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

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_nonmarker_direct_parent
