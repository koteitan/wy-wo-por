/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PhysicalRootRecordGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PhysicalRootCommonBand

/-!
# Physical candidate and common-parent geometry including root parents

A source candidate strictly right of the root is itself a same-row marker
even when the accepted source parent lies in the root column. Its actual
physical copy is the new Q. Common physical source-parent edges also have
one actual copied parent: raw frontier closure identifies it by column and
cut, without numerical-parent recognition of the current copied nodes.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem Preparation.marked_candidate_of_right
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {source candidate parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    (hCandidateRight : p.root.column < candidate.1.val) :
    BucketMem p.marked candidate.1.val (Frame.ref candidate) ∧
      (Frame.ofMountain p.reduced).height candidate = (Frame.ofMountain p.reduced).height source := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hCandidateReal := Frame.Q_real hNormal.toOrdered hReal hCandidate
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hRight, low, hLowReal, hColumn, hIndex, hPath, hRow⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mp hMarked
  have hTail : ParentPath F parent low := by
    cases hPath with
    | refl =>
        have he := congrArg Fin.val hColumn
        omega
    | @cons source next low hNext tail =>
        have he : next = parent := Option.some.inj (hNext.symm.trans hParent)
        exact he ▸ tail
  obtain ⟨actual, hActual, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  have he : actual = candidate := Option.some.inj (hActual.symm.trans hCandidate)
  subst actual
  have hCandidatePath := trace.parentPath hNormal.toOrdered (hNormal.real_positive candidate hCandidateReal)
  have hParentRow := (build_marked_parent_bounds p.reduced_build hMarkers hParent hMarked).2
  have hSame : F.height candidate = F.height source := le_antisymm
    (Frame.Q_height_le hNormal.toOrdered hCandidate)
    (hParentRow ▸ hCandidatePath.height_le hNormal.toOrdered)
  refine ⟨(build_markers_real_member_iff_parentPath p.reduced_build hMarkers hCandidateReal).mpr
    ⟨(congrArg Ref.column hRootRef).trans_lt hCandidateRight, low, hLowReal, hColumn, hIndex,
      hCandidatePath.trans hTail, hSame.trans hRow⟩, hSame⟩

namespace PhysicalMarkerRead

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  {copy : EffectiveCopyOccurrence p block start references source result}
  (physical : PhysicalMarkerRead copy)

/-- The old Q needs to be strictly right of the root; the accepted parent
does not. Nondirect root-parent source searches satisfy precisely this
condition. The actual output Q is the physical, not raised effective, copy.
-/
theorem candidate_eq_of_candidate_right (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    {candidateCopy : EffectiveCopyOccurrence p block start references candidate result}
    (candidatePhysical : PhysicalMarkerRead candidateCopy)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hCandidateRight : p.root.column < candidate.1.val) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = physical.outputRef ∧
      Frame.ref actualCandidate = candidatePhysical.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result physical.outputRef = .ok candidatePhysical.outputRef := by
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨_, hSourceRows⟩ := p.marked_candidate_of_right hParent hCandidate hMarked hCandidateRight
  have hOutputRows : candidatePhysical.cell.row = physical.cell.row :=
    candidatePhysical.source_row.trans (hSourceRows.trans physical.source_row.symm)
  obtain ⟨actualSource, actualCandidate, hSourceRef, _, hActualQ, hSearch,
      hColumn, hCut, hFront⟩ := physical.candidate_frontier hValid hMarked hReal hCandidate hCandidateRight.le
  obtain ⟨expected, hExpectedRef, hExpectedCell⟩ :=
    Canonical.frame_node_of_cellAt candidatePhysical.output_read
  have hExpectedRow : G.height expected = physical.cell.row := by
    change (G.cell expected).row = _
    rw [hExpectedCell, hOutputRows]
  have hColumns : expected.1 = actualCandidate.1 := Fin.ext
    ((congrArg Ref.column hExpectedRef).trans candidatePhysical.source_column |>.trans hColumn.symm)
  have hExpectedFront : Frame.frontierAt hValid.toOrdered physical.cell.row hCut expected.1 = expected := by
    apply Frame.frontierAt_eq_of_upper_barrier hValid.toOrdered hCut
    · exact hExpectedRow.le
    · intro upper hUpper
      rw [← hExpectedRow]
      have hSpec := Frame.upper_spec hUpper
      rcases upper with ⟨column, index⟩
      dsimp only at hSpec
      obtain ⟨hColumnEq, hIndex⟩ := hSpec
      subst column
      exact hValid.toOrdered.rows_strict expected.1 (by change expected.2.val < index.val; omega)
  rw [hColumns, hFront] at hExpectedFront
  have hActualRef : Frame.ref actualCandidate = candidatePhysical.outputRef :=
    (congrArg Frame.ref hExpectedFront).trans hExpectedRef
  exact ⟨actualSource, actualCandidate, hSourceRef, hActualRef, hActualQ,
    by simpa only [hActualRef] using hSearch⟩

end PhysicalMarkerRead
end OmegaY.Expansion

namespace OmegaY.Geometry.Frame

private theorem physical_frontier_self {F : Frame} (hF : F.Ordered)
    (u : F.Node) (hCut : (1 : Row) ≤ F.height u) :
    frontierAt hF (F.height u) hCut u.1 = u := by
  apply frontierAt_eq_of_upper_barrier hF hCut le_rfl
  intro upper hUpper
  obtain ⟨hColumn, hIndex⟩ := upper_spec hUpper
  rcases upper with ⟨column, index⟩
  dsimp only at hColumn hIndex
  subst column
  exact hF.rows_strict u.1 (by change u.2.val < index.val; omega)

/-- Common raw-parent column and common child height suffice to identify
the actual parent endpoints under the independently proved raw frontier
barrier. No numerical P of either child is required. -/
theorem rawParent_eq_of_child_height_parent_column {F : Frame} (hF : F.Ordered)
    (hRaw : F.RawRowGeometry) (hFather : F.RawFatherUpperBound)
    {u z uParent zParent : F.Node} (hUReal : Real u) (hZReal : Real z)
    (hUP : F.rawParent u = some uParent) (hZP : F.rawParent z = some zParent)
    (hRow : F.height u = F.height z) (hColumn : uParent.1 = zParent.1) : uParent = zParent := by
  have hCut := one_le_height hF hUReal
  have hZCut := one_le_height hF hZReal
  have hUFront := frontierAt_raw_parent_of_bound hF hRaw hFather hCut u.1
    (by simpa only [physical_frontier_self hF u hCut] using hUP)
  have hZFront := frontierAt_raw_parent_of_bound hF hRaw hFather hZCut z.1
    (by simpa only [physical_frontier_self hF z hZCut] using hZP)
  have hUFront' : frontierAt hF (F.height z) hZCut zParent.1 = uParent := by
    simpa only [hRow, hColumn] using hUFront
  exact hUFront'.symm.trans hZFront

end OmegaY.Geometry.Frame

#print axioms OmegaY.Expansion.Preparation.marked_candidate_of_right
#print axioms OmegaY.Expansion.PhysicalMarkerRead.candidate_eq_of_candidate_right
#print axioms OmegaY.Geometry.Frame.rawParent_eq_of_child_height_parent_column
