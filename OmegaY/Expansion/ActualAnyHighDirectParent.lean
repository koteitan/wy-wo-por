/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualAnyHighDirectParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAnyHighCandidate
import OmegaY.Expansion.ActualHighDirectParent
import OmegaY.Expansion.HistoryRawInvariants

/-!
# High direct numerical recognition, with all source-parent columns

Only the source current node must lie at or above the old last-top row.
Its numerical parent may be below that row, and may be in the fixed good
part, the root column, or a copied column. The direct source Q=P case is
recognized from actual candidate columns and actual stored edges. No
numerical recognition hypothesis on any new node is used.
-/

namespace OmegaY.Geometry.Frame

/-- Q and a raw parent in the same column are identical under the raw
father bound: both are the actual frontier at the current node's height.
This does not assert that their columns are always the same. -/
theorem Q_eq_rawParent_of_column {F : Frame} (hF : F.Ordered)
    (hRaw : F.RawRowGeometry) (hFather : F.RawFatherUpperBound)
    {u candidate parent : F.Node} (hReal : Real u)
    (hQ : F.Q u = some candidate) (hParent : F.rawParent u = some parent)
    (hColumn : candidate.1 = parent.1) : candidate = parent := by
  have hOne := one_le_height hF hReal
  have hSelf : frontierAt hF (F.height u) hOne u.1 = u := by
    apply frontierAt_eq_of_upper_barrier hF hOne le_rfl
    intro upper hUpper
    obtain ⟨hColumn, hIndex⟩ := upper_spec hUpper
    rcases upper with ⟨column, index⟩
    dsimp only at hColumn hIndex
    subst column
    apply hF.rows_strict u.1
    change u.2.val < index.val
    omega
  have hPFront : frontierAt hF (F.height u) hOne parent.1 = parent :=
    frontierAt_raw_parent_of_bound hF hRaw hFather hOne u.1
      (by simpa only [hSelf] using hParent)
  have hQFront : frontierAt hF (F.height u) hOne candidate.1 = candidate :=
    frontierAt_eq_of_upper_barrier hF hOne (Q_height_le hF hQ)
      (fun _ hUpper => Q_upper_gt hF hQ hUpper)
  rw [hColumn, hPFront] at hQFront
  exact hQFront.symm

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame

/-- Complete direct-hit recognition for an actual high copied current
node. The returned parent is the actual Q and the actual stored parent;
its provenance includes the changing root-boundary case. -/
theorem DynamicBlockState.recorded_any_high_direct_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {source parent : (Frame.ofMountain p.reduced).Node}
    (sourceCopy : EffectiveCopyOccurrence p block start references source ambient)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hDirect : (Frame.ofMountain p.reduced).Q source = some parent)
    (hBefore : source.1.val < next)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source) :
    ∃ u father : (Frame.ofMountain ambient).Node,
      Frame.ref u = sourceCopy.outputRef ∧
      (Frame.ofMountain ambient).cell u = sourceCopy.read.outputCell ∧
      (Frame.ofMountain ambient).Q u = some father ∧
      (Frame.ofMountain ambient).rawParent u = some father ∧
      (Frame.ofMountain ambient).P u = some father ∧
      findParent ambient sourceCopy.outputRef = .ok (Frame.ref father) ∧
      ∃ hOne : (1 : Row) ≤ (Frame.ofMountain p.reduced).height source,
        HighCandidateOrigin s parent ((Frame.ofMountain p.reduced).height source) hOne father := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨u, candidate, hURef, hUCell, hQ, _, hOne, _, hOrigin⟩ :=
    s.actual_any_high_candidate history hLast hStartRun sourceCopy hBefore hSourceReal hHigh hDirect
  have hUReal : Real u := by
    have hIndex := congrArg Ref.index hURef
    change u.2.val = sourceCopy.read.outputIndex at hIndex
    change 0 < u.2.val
    rw [hIndex]
    exact sourceCopy.read.output_real hSourceReal
  obtain ⟨hRaw, hFather⟩ := s.raw_invariants_of_start_run history hLast hStartRun
  have hRawCandidate : G.rawParent u = some candidate := by
    rcases hOrigin with ⟨hFixed, hRef, _⟩ | ⟨hRoot, boundary, hBoundaryColumn, _, hRef, _, _⟩ |
        ⟨hRight, parentCopy, hRef, _⟩
    · exact (s.recorded_fixed_parent history hLast hParent sourceCopy.state.next_lower
        hBefore hFixed sourceCopy).1.rawParent hURef hRef
    · obtain ⟨endpoint, hEdge⟩ := s.recorded_root_parent_exists
        history hLast hStartRun hParent hRoot hBefore sourceCopy
      obtain ⟨rawParent, hRawRef, _⟩ := Canonical.frame_node_of_cellAt endpoint.result_read
      have hStored := hEdge.rawParent hURef hRawRef
      have hEndpointColumn : endpoint.reference.column = start.size - 1 := by
        cases endpoint with
        | selected endpoint => exact endpoint.reference_column
        | highTail endpoint => exact endpoint.reference_column
      have hColumns : candidate.1 = rawParent.1 := Fin.ext
        (((congrArg Ref.column hRef).trans hBoundaryColumn).trans
          ((congrArg Ref.column hRawRef).trans hEndpointColumn).symm)
      have hEq := Frame.Q_eq_rawParent_of_column s.ambient_valid.toOrdered hRaw hFather
        hUReal hQ hStored hColumns
      exact hEq ▸ hStored
    · exact (s.recorded_effective_parent history hLast hParent hRight hBefore
        sourceCopy parentCopy).rawParent hURef hRef
  have hP := (s.mountainSums_of_start_run history hLast hStartRun).P_of_Q_rawParent
    s.ambient_valid hUReal hQ hRawCandidate
  refine ⟨u, candidate, hURef, hUCell, hQ, hRawCandidate, hP, ?_, hOne, hOrigin⟩
  simpa only [hURef] using (Executable.findParent_ref_iff s.ambient_valid.toOrdered u candidate).mpr hP

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Q_eq_rawParent_of_column
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_any_high_direct_parent
