/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawFrontier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawFrameGeometry
import OmegaY.Expansion.CanonicalFrontier

/-!
# Actual frontier geometry before numerical parent recovery

A moving event's candidate is determined by its actual stored left endpoint
and the maximum search defining Q. No P assertion is needed for that fact.

The raw father-upper bound is kept as a separate geometric obligation. Given
that bound, the independently proved raw row law supplies parent-frontier
closure and synchronous backfill on the actual finite events. Neither these
facts nor raw B plus sums alone recover numerical first-smaller parents.
-/

namespace OmegaY.Geometry.Frame

/-- This remains an independent obligation for copied graphs. It is stated
only for real lower nodes and actual upper-stored parent edges. -/
def RawFatherUpperBound (F : Frame) : Prop :=
  ∀ u parent upper parentUpper, Real u → F.rawParent u = some parent →
    F.upper u = some upper → F.upper parent = some parentUpper →
    F.height upper ≤ F.height parentUpper

theorem RawRowGeometry.at {F : Frame} (h : F.RawRowGeometry)
    {u upper parent : F.Node} (hReal : Real u) (hUpper : F.upper u = some upper)
    (hParent : F.rawParent u = some parent) :
    F.height parent ≤ F.height u ∧
      F.height upper = Row.B (F.height u) (F.height parent) := by
  obtain ⟨actual, hActual, _, hRow, hB⟩ := h u upper hReal hUpper
  have hEq : actual = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actual
  exact ⟨hRow, hB⟩

theorem Normal.rawFatherUpperBound {F : Frame} (h : F.Normal) :
    F.RawFatherUpperBound := by
  intro u parent upper parentUpper hReal hParent hUpper hParentUpper
  exact father_upper_bound_nodes h
    ((h.rawParent_eq_P hReal).symm.trans hParent) hUpper hParentUpper

/-- Actual Q at a moved event is the new common-cut frontier of the column
named by the old raw parent. The maximum search, not numerical parent
recognition or a father-upper bound, identifies this frontier. -/
theorem eventFrontier_moving_raw_candidate {F : Frame} (hF : F.Ordered)
    {event : Nat} (hEvent : event < F.lastEvent) (column : Fin F.width)
    (hChanged : eventFrontier hF (event + 1) column ≠ eventFrontier hF event column)
    {parent : F.Node}
    (hParent : F.rawParent (eventFrontier hF event column) = some parent) :
    F.Q (eventFrontier hF (event + 1) column) =
      some (eventFrontier hF (event + 1) parent.1) := by
  obtain ⟨hUpper, hNewRow⟩ := eventFrontier_advance hF hEvent column hChanged
  obtain ⟨upper, hActualUpper, hStored⟩ := rawParent_spec hParent
  have hUpperEq : upper = eventFrontier hF (event + 1) column :=
    Option.some.inj (hActualUpper.symm.trans hUpper)
  subst upper
  obtain ⟨q, hQ⟩ := Q_exists_of_left hF ⟨ref parent, hStored⟩
  obtain ⟨left, hLeft, _, _, hQColumn, _⟩ := Q_spec hF hQ
  have hLeftEq : left = parent := Executable.ref_injective F
    (Option.some.inj (hLeft.symm.trans hStored))
  subst left
  have hFront : eventFrontier hF (event + 1) q.1 = q := by
    apply frontierAt_eq_of_upper_barrier hF (F.eventCut_one_le (event + 1))
    · exact (Q_height_le hF hQ).trans_eq hNewRow
    · intro upper hUpper
      rw [← hNewRow]
      exact Q_upper_gt hF hQ hUpper
  rw [hQColumn] at hFront
  exact hQ.trans (congrArg some hFront.symm)

/-- The raw bound excludes sparse-parent rows between the endpoint and the
current cut. It proves genuine maximum-frontier closure, not just a row bound. -/
theorem frontierAt_raw_parent_of_bound {F : Frame} (hF : F.Ordered)
    (hRaw : F.RawRowGeometry) (hBound : F.RawFatherUpperBound)
    {cut : Row} (hCut : (1 : Row) ≤ cut) (column : Fin F.width)
    {parent : F.Node} (hParent : F.rawParent (frontierAt hF cut hCut column) = some parent) :
    frontierAt hF cut hCut parent.1 = parent := by
  have hSpec := frontierAt_spec hF hCut column
  obtain ⟨upper, hUpper, _⟩ := rawParent_spec hParent
  have hRows := hRaw.at hSpec.2.1 hUpper hParent
  apply frontierAt_eq_of_upper_barrier hF hCut
  · exact hRows.1.trans hSpec.2.2.1
  · intro parentUpper hParentUpper
    exact (hSpec.2.2.2.2 upper hUpper).trans_le
      (hBound _ parent upper parentUpper hSpec.2.1 hParent hUpper hParentUpper)

theorem eventFrontier_raw_parent_of_bound {F : Frame} (hF : F.Ordered)
    (hRaw : F.RawRowGeometry) (hBound : F.RawFatherUpperBound)
    (event : Nat) (column : Fin F.width) {parent : F.Node}
    (hParent : F.rawParent (eventFrontier hF event column) = some parent) :
    eventFrontier hF event parent.1 = parent :=
  frontierAt_raw_parent_of_bound hF hRaw hBound (F.eventCut_one_le event) column hParent

/-- All frontier fields now follow from actual finite cuts, raw B, and the
separate raw father-upper bound. In particular no current numerical P occurs
in any premise or conclusion. -/
theorem eventFrontier_geometry_of_raw_bound {F : Frame} (hF : F.Ordered)
    (hRaw : F.RawRowGeometry) (hFather : F.RawFatherUpperBound) (hWidth : 0 < F.width)
    {bound : Nat} (hBound : bound < F.width) :
    FrontierGeometry F (eventFrontierNat hF hWidth) F.eventCut bound 0 F.lastEvent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro event _ _ column hColumn
    rw [eventFrontierNat_eq hF hWidth event (hColumn.trans_lt hBound)]
    exact congrArg Fin.val (eventFrontier_spec hF event ⟨column, hColumn.trans_lt hBound⟩).1
  · intro event _ _ column hColumn
    rw [eventFrontierNat_eq hF hWidth event (hColumn.trans_lt hBound)]
    exact (eventFrontier_spec hF event ⟨column, hColumn.trans_lt hBound⟩).2.1
  · intro event _ _ column hColumn
    rw [eventFrontierNat_eq hF hWidth event (hColumn.trans_lt hBound)]
    exact (eventFrontier_spec hF event ⟨column, hColumn.trans_lt hBound⟩).2.2.1
  · intro event _ _ column hColumn upper hUpper
    rw [eventFrontierNat_eq hF hWidth event (hColumn.trans_lt hBound)] at hUpper
    exact (eventFrontier_spec hF event ⟨column, hColumn.trans_lt hBound⟩).2.2.2.2 upper hUpper
  · intro event _ hEvent column hColumn hChanged
    have hc := hColumn.trans_lt hBound
    simp only [frontierMoves, eventFrontierNat_eq hF hWidth _ hc] at hChanged ⊢
    exact eventFrontier_advance hF hEvent ⟨column, hc⟩ hChanged
  · intro event _ _ column hColumn parent hParent
    have hc := hColumn.trans_lt hBound
    rw [eventFrontierNat_eq hF hWidth event hc] at hParent
    rw [eventFrontierNat_eq hF hWidth event parent.1.isLt]
    exact eventFrontier_raw_parent_of_bound hF hRaw hFather event ⟨column, hc⟩ hParent
  · intro event _ _ column hColumn upper parent hUpper hParent
    have hc := hColumn.trans_lt hBound
    rw [eventFrontierNat_eq hF hWidth event hc] at hUpper hParent ⊢
    exact hRaw.at (eventFrontier_spec hF event ⟨column, hc⟩).2.1 hUpper hParent

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- Actual positive backfill ensures an old raw parent exists whenever an
event moves. Its new Q candidate is then identified without copied Normal,
raw father bounds, or first-smaller assumptions. -/
theorem MountainSums.eventFrontier_moving_candidate {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {event : Nat} (hEvent : event < (Frame.ofMountain mountain).lastEvent)
    (column : Fin (Frame.ofMountain mountain).width)
    (hChanged : Frame.eventFrontier hValid.toOrdered (event + 1) column ≠
      Frame.eventFrontier hValid.toOrdered event column) :
    ∃ parent, (Frame.ofMountain mountain).rawParent
        (Frame.eventFrontier hValid.toOrdered event column) = some parent ∧
      (Frame.ofMountain mountain).Q (Frame.eventFrontier hValid.toOrdered (event + 1) column) =
        some (Frame.eventFrontier hValid.toOrdered (event + 1) parent.1) := by
  obtain ⟨hUpper, _⟩ := Frame.eventFrontier_advance hValid.toOrdered hEvent column hChanged
  obtain ⟨parent, hParent, _⟩ := hSums.rawParent_upper hValid
    (Frame.eventFrontier_spec hValid.toOrdered event column).2.1 hUpper
  exact ⟨parent, hParent,
    Frame.eventFrontier_moving_raw_candidate hValid.toOrdered hEvent column hChanged hParent⟩

/-- Concrete actual-event backfill. Only the raw father-upper bound is still
a new geometric premise; validity, sums, and raw B have independent executable
proofs. No NumericSuffix or numerical reconstruction is concluded. -/
theorem MountainRawGeometry.eventFrontier_synchronousBackfill {mountain : Mountain}
    (hRaw : MountainRawGeometry mountain) (hValid : MountainValid mountain)
    (hSums : MountainSums mountain)
    (hFather : (Frame.ofMountain mountain).RawFatherUpperBound)
    (hWidth : 0 < mountain.size) {bound : Nat} (hBound : bound < mountain.size)
    (initial : ZeroY.ParentMap) :
    Forests.SynchronousBackfill
      ((Frame.ofMountain mountain).frontierForests initial
        (Frame.eventFrontierNat hValid.toOrdered hWidth) bound)
      ((Frame.ofMountain mountain).frontierValue
        (Frame.eventFrontierNat hValid.toOrdered hWidth))
      (Frame.frontierMoves (Frame.eventFrontierNat hValid.toOrdered hWidth))
      bound 0 (Frame.ofMountain mountain).lastEvent :=
  synchronousBackfill_of_frontier_geometry hValid hSums
    (Frame.eventFrontier_geometry_of_raw_bound hValid.toOrdered hRaw.rawRowGeometry
      hFather hWidth hBound) initial

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.rawFatherUpperBound
#print axioms OmegaY.Geometry.Frame.eventFrontier_moving_raw_candidate
#print axioms OmegaY.Geometry.Frame.frontierAt_raw_parent_of_bound
#print axioms OmegaY.Geometry.Frame.eventFrontier_geometry_of_raw_bound
#print axioms OmegaY.Expansion.MountainSums.eventFrontier_moving_candidate
#print axioms OmegaY.Expansion.MountainRawGeometry.eventFrontier_synchronousBackfill
