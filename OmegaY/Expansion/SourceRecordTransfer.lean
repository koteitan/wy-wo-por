/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SourceRecordTransfer.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalEventProjection
import OmegaY.Geometry.RecordParentBound
import OmegaY.Geometry.RecordBarrier

/-!
# Transferring source records through stored copied endpoints

The target assumptions below are geometric reads plus numerical recognition
restricted to columns strictly left of the current column. In particular,
an edge is not assumed to map to a target P edge: its actual upper stores an
endpoint whose column and row identify the image of the source parent.
Orderedness and the already established strict-left induction hypothesis
then recover that P edge. Source canonical event projection supplies the
whole source record chain in the final build-specific theorem.

This does not assert that these geometric image reads have been assembled
for every copy/fill case, that the current target Q equals the first image,
or that source numerical barriers transfer to target values.
-/

namespace OmegaY.Geometry.Frame

/-- Identify a stored endpoint by its actual column and height, then use
only the strict-left numerical induction hypothesis. -/
theorem P_of_left_stored_coordinates {T : Frame} (hT : T.Ordered)
    {bound : Nat}
    (hKnown : ∀ node, node.1.val < bound → Real node → T.rawParent node = T.P node)
    {node upper endpoint intended : T.Node} (hLeft : node.1.val < bound)
    (hReal : Real node) (hUpper : T.upper node = some upper)
    (hStored : (T.cell upper).left = some (ref endpoint))
    (hColumn : endpoint.1.val = intended.1.val)
    (hRow : T.height endpoint = T.height intended) : T.P node = some intended := by
  have hEndpoint : endpoint = intended := node_eq_of_column_height hT (Fin.ext hColumn) hRow
  subst endpoint
  exact (hKnown node hLeft hReal).symm.trans (rawParent_eq_of_upper_left hUpper hStored)

/-- At one fixed source event, coordinate-correct stored legs in previously
recognized target columns transport any actual source record path. The
source chain is restricted to a strict-left prefix throughout. -/
theorem Normal.parentPath_transfer_stored_frontier {S T : Frame}
    (hS : S.Normal) (hT : T.Ordered) {sourceBound targetBound event : Nat}
    (image : Fin S.width → T.Node)
    (hImageLeft : ∀ c, c.val < sourceBound → (image c).1.val < targetBound)
    (hImageReal : ∀ c, c.val < sourceBound → Real (image c))
    (hKnown : ∀ node, node.1.val < targetBound → Real node → T.rawParent node = T.P node)
    (hStored : ∀ c, c.val < sourceBound → ∀ parent,
      S.P (eventFrontier hS.toOrdered event c) = some parent →
      ∃ upper endpoint, T.upper (image c) = some upper ∧
        (T.cell upper).left = some (ref endpoint) ∧
        endpoint.1.val = (image parent.1).1.val ∧ T.height endpoint = T.height (image parent.1))
    {q p : S.Node} (hQFront : eventFrontier hS.toOrdered event q.1 = q)
    (hQLeft : q.1.val < sourceBound) (path : ParentPath S q p) :
    ParentPath T (image q.1) (image p.1) := by
  induction path with
  | refl _ => exact .refl _
  | @cons q next p hParent rest ih =>
      have hAtFront : S.P (eventFrontier hS.toOrdered event q.1) = some next := by
        simpa only [hQFront] using hParent
      obtain ⟨upper, endpoint, hUpper, hLeg, hColumn, hRow⟩ := hStored q.1 hQLeft next hAtFront
      have hMapped := P_of_left_stored_coordinates hT hKnown (hImageLeft q.1 hQLeft)
        (hImageReal q.1 hQLeft) hUpper hLeg hColumn hRow
      have hNextFront := hS.eventFrontier_parent event q.1 hAtFront
      have hNextLeft : next.1.val < sourceBound := (P_column_lt hS.toOrdered hParent).trans hQLeft
      exact .cons hMapped (ih hNextFront hNextLeft)

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- The actual fixed-good-part/moved-bad-part column transformation. -/
def copiedColumnIndex (root shift column : Nat) : Nat :=
  if column < root then column else column + shift

theorem copiedColumnIndex_strictMono (root shift : Nat) :
    StrictMono (copiedColumnIndex root shift) := by
  intro a b hab
  unfold copiedColumnIndex
  split <;> split <;> omega

/-- The actual source build supplies the chain and its source barrier.
Physical endpoint coordinates and strict-left recognition turn its mapped
records into actual target P records. The source-value inequality is kept
explicitly on the source; no target numerical barrier is claimed. -/
theorem build_source_candidate_records_transfer
    {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {T : Frame} (hT : T.Ordered) {bound start event root shift : Nat}
    (hBound : bound < mountain.size) (hOrder : start ≤ event)
    (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (column : Fin (Frame.ofMountain mountain).width) (hColumn : column.val ≤ bound)
    {parent candidate : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P
      (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column) = some parent)
    (hCandidate : (Frame.ofMountain mountain).P
      (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start column) = some candidate)
    (hDistinct : parent.1.val ≠ candidate.1.val)
    (image : Fin (Frame.ofMountain mountain).width → T.Node) (current : T.Node)
    (hCurrentColumn : current.1.val = copiedColumnIndex root shift column.val)
    (hImageColumn : ∀ c, c.val < column.val → (image c).1.val = copiedColumnIndex root shift c.val)
    (hImageReal : ∀ c, c.val < column.val → Frame.Real (image c))
    (hKnown : ∀ node, node.1.val < current.1.val → Frame.Real node → T.rawParent node = T.P node)
    (hStored : ∀ c, c.val < column.val → ∀ sourceParent,
      (Frame.ofMountain mountain).P
        (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start c) = some sourceParent →
      ∃ upper endpoint, T.upper (image c) = some upper ∧
        (T.cell upper).left = some (Frame.ref endpoint) ∧
        endpoint.1.val = (image sourceParent.1).1.val ∧
        T.height endpoint = T.height (image sourceParent.1)) :
    Frame.ParentPath T (image candidate.1) (image parent.1) ∧
      ∃ sourceZ : (Frame.ofMountain mountain).Node,
        Frame.ParentPath (Frame.ofMountain mountain) candidate sourceZ ∧
        (Frame.ofMountain mountain).P sourceZ =
          some (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start parent.1) ∧
        Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start sourceZ.1 = sourceZ ∧
        sourceZ.1.val < column.val ∧
        (Frame.ofMountain mountain).value
          (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column) ≤
            (Frame.ofMountain mountain).value sourceZ ∧
        Frame.ParentPath T (image candidate.1) (image sourceZ.1) ∧
        T.P (image sourceZ.1) = some (image parent.1) ∧
        (image sourceZ.1).1.val < current.1.val := by
  have hS := build_normal_of_success hBuild
  have hImageLeft : ∀ c, c.val < column.val → (image c).1.val < current.1.val := by
    intro c hc
    rw [hImageColumn c hc, hCurrentColumn]
    exact copiedColumnIndex_strictMono root shift hc
  obtain ⟨path, sourceZ, pathZ, hLast, hZFront, _, hSourceBarrier⟩ :=
    build_event_parent_candidate_blocker hBuild hWidth hBound hOrder hEvent column hColumn
      hParent hCandidate hDistinct
  have hCandidateFront := hS.eventFrontier_parent start column hCandidate
  have hCandidateLeft := Frame.P_column_lt hS.toOrdered hCandidate
  have hZLeft := (pathZ.column_le hS.toOrdered).trans_lt hCandidateLeft
  have hTargetPath := hS.parentPath_transfer_stored_frontier hT image hImageLeft hImageReal
    hKnown hStored hCandidateFront hCandidateLeft path
  have hTargetZ := hS.parentPath_transfer_stored_frontier hT image hImageLeft hImageReal
    hKnown hStored hCandidateFront hCandidateLeft pathZ
  have hZParent : (Frame.ofMountain mountain).P
      (Frame.eventFrontier hS.toOrdered start sourceZ.1) =
        some (Frame.eventFrontier hS.toOrdered start parent.1) := by
    simpa only [hZFront] using hLast
  obtain ⟨upper, endpoint, hUpper, hLeg, hEndpointColumn, hEndpointRow⟩ :=
    hStored sourceZ.1 hZLeft _ hZParent
  have hMappedLast := Frame.P_of_left_stored_coordinates hT hKnown (hImageLeft sourceZ.1 hZLeft)
    (hImageReal sourceZ.1 hZLeft) hUpper hLeg hEndpointColumn hEndpointRow
  exact ⟨hTargetPath, sourceZ, pathZ, hLast, hZFront, hZLeft, hSourceBarrier,
    hTargetZ, hMappedLast, hImageLeft sourceZ.1 hZLeft⟩

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.P_of_left_stored_coordinates
#print axioms OmegaY.Geometry.Frame.Normal.parentPath_transfer_stored_frontier
#print axioms OmegaY.Expansion.copiedColumnIndex_strictMono
#print axioms OmegaY.Expansion.build_source_candidate_records_transfer
