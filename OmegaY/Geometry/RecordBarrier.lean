/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RecordBarrier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.Decrement
import OmegaY.Geometry.Executable

/-!
# Expanding numerical-parent records into the actual candidate search

`ParentPath` contains actual numerical-parent records, while `Hit` retains
every rejected original `Q` candidate. A threshold below the last rejected
record is below all previous records. Expanding each actual `P` step with
`P_iff` and replacing its threshold-search tail therefore recovers the full
operational trace, including candidates skipped by record compression.

Only `Ordered` and actual `P` facts along the strict-left record path are
used. No numerical-parent assertion for the current node, copied `Normal`
certificate, or expansion well-foundedness assumption is required.
-/

namespace OmegaY.Geometry.Frame

/-- Prepend a record path above a fixed threshold to a complete `Q` search.
Each record step is expanded to its actual original candidate trace. -/
theorem ParentPath.prepend_hit {F : Frame} (hF : F.Ordered)
    {threshold : Nat} {q z p : F.Node} (path : ParentPath F q z)
    (hBarrier : threshold ≤ F.value z) (tail : Hit F threshold z p) :
    Hit F threshold q p := by
  induction path with
  | refl _ => exact tail
  | @cons u next z hParent rest ih =>
    have hThreshold : threshold ≤ F.value u :=
      hBarrier.trans ((ParentPath.cons hParent rest).value_le hF)
    obtain ⟨candidate, hQ, trace⟩ := (P_iff hF).mp hParent
    exact .next (fun h => Nat.not_lt_of_ge hThreshold h.2) hQ
      (trace.replace_tail hThreshold (ih hBarrier tail))

/-- The last rejected record and its first smaller parent determine the
entire original candidate trace, not merely its compressed records. -/
theorem ParentPath.hit_of_record_barrier {F : Frame} (hF : F.Ordered)
    {threshold : Nat} {q z p : F.Node} (path : ParentPath F q z)
    (hLast : F.P z = some p) (hBarrier : threshold ≤ F.value z)
    (hSmall : F.value p < threshold) : Hit F threshold q p := by
  obtain ⟨candidate, hQ, trace⟩ := (P_iff hF).mp hLast
  have tail : Hit F threshold z p :=
    .next (fun h => Nat.not_lt_of_ge hBarrier h.2) hQ
      (trace.tighten hBarrier hSmall)
  exact path.prepend_hit hF hBarrier tail

/-- Record-barrier recognition of the actual numerical parent. All `P`
premises belong to the path starting at the strictly earlier first `Q`
candidate. In particular the conclusion `P u = some p` is not a premise. -/
theorem P_of_record_barrier {F : Frame} (hF : F.Ordered)
    {u q z p : F.Node} (hQ : F.Q u = some q) (path : ParentPath F q z)
    (hLast : F.P z = some p) (hBarrier : F.value u ≤ F.value z)
    (hSmall : F.value p < F.value u) : F.P u = some p :=
  (P_iff hF).mpr
    ⟨q, hQ, path.hit_of_record_barrier hF hLast hBarrier hSmall⟩

/-- The last record used by the barrier criterion is strictly left of the
current node, including a path with no intermediate record. -/
theorem record_barrier_column_lt {F : Frame} (hF : F.Ordered)
    {u q z : F.Node} (hQ : F.Q u = some q) (path : ParentPath F q z) :
    z.1.val < u.1.val :=
  lt_of_le_of_lt (path.column_le hF) (Q_column_lt hF hQ)

/-- Equal actual parent addends cancel. In an application, `uUpper` and
`zUpper` are the adjacent upper nodes identified by the backfill theorem.
This equivalence does not assert either comparison. -/
theorem common_parent_backfill_le_iff {F : Frame}
    {u z uUpper zUpper parent : F.Node}
    (hU : F.value u = F.value uUpper + F.value parent)
    (hZ : F.value z = F.value zUpper + F.value parent) :
    F.value u ≤ F.value z ↔ F.value uUpper ≤ F.value zUpper := by
  omega

theorem common_parent_backfill_lt_iff {F : Frame}
    {u z uUpper zUpper parent : F.Node}
    (hU : F.value u = F.value uUpper + F.value parent)
    (hZ : F.value z = F.value zUpper + F.value parent) :
    F.value u < F.value z ↔ F.value uUpper < F.value zUpper := by
  omega

theorem common_parent_backfill_eq_iff {F : Frame}
    {u z uUpper zUpper parent : F.Node}
    (hU : F.value u = F.value uUpper + F.value parent)
    (hZ : F.value z = F.value zUpper + F.value parent) :
    F.value u = F.value z ↔ F.value uUpper = F.value zUpper := by
  omega

/-- Backfill reduces the last-record barrier to an upper-value comparison.
The numerical inequality between these upper nodes remains a hypothesis;
neither same-parent backfill nor this lemma establishes it on its own. -/
theorem P_of_record_barrier_backfill {F : Frame} (hF : F.Ordered)
    {u q z p uUpper zUpper : F.Node}
    (hQ : F.Q u = some q) (path : ParentPath F q z)
    (hLast : F.P z = some p)
    (hU : F.value u = F.value uUpper + F.value p)
    (hZ : F.value z = F.value zUpper + F.value p)
    (hUpperPositive : 0 < F.value uUpper)
    (hUpperBarrier : F.value uUpper ≤ F.value zUpper) : F.P u = some p := by
  apply P_of_record_barrier hF hQ path hLast
  · exact (common_parent_backfill_le_iff hU hZ).mpr hUpperBarrier
  · omega

end OmegaY.Geometry.Frame

namespace OmegaY.Geometry.Executable

/-- The same criterion identifies the executable constructor's search,
using the existing exact bridge with sufficient column-derived fuel. -/
theorem findParent_of_record_barrier {mountain : Canonical.Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    {u q z p : (Frame.ofMountain mountain).Node}
    (hQ : (Frame.ofMountain mountain).Q u = some q)
    (path : Frame.ParentPath (Frame.ofMountain mountain) q z)
    (hLast : (Frame.ofMountain mountain).P z = some p)
    (hBarrier : (Frame.ofMountain mountain).value u ≤ (Frame.ofMountain mountain).value z)
    (hSmall : (Frame.ofMountain mountain).value p < (Frame.ofMountain mountain).value u) :
    Canonical.findParent mountain (Frame.ref u) = .ok (Frame.ref p) :=
  (findParent_ref_iff hF u p).mpr
    (Frame.P_of_record_barrier hF hQ path hLast hBarrier hSmall)

theorem findParent_of_record_barrier_backfill {mountain : Canonical.Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    {u q z p uUpper zUpper : (Frame.ofMountain mountain).Node}
    (hQ : (Frame.ofMountain mountain).Q u = some q)
    (path : Frame.ParentPath (Frame.ofMountain mountain) q z)
    (hLast : (Frame.ofMountain mountain).P z = some p)
    (hU : (Frame.ofMountain mountain).value u =
      (Frame.ofMountain mountain).value uUpper + (Frame.ofMountain mountain).value p)
    (hZ : (Frame.ofMountain mountain).value z =
      (Frame.ofMountain mountain).value zUpper + (Frame.ofMountain mountain).value p)
    (hUpperPositive : 0 < (Frame.ofMountain mountain).value uUpper)
    (hUpperBarrier : (Frame.ofMountain mountain).value uUpper ≤
      (Frame.ofMountain mountain).value zUpper) :
    Canonical.findParent mountain (Frame.ref u) = .ok (Frame.ref p) :=
  (findParent_ref_iff hF u p).mpr
    (Frame.P_of_record_barrier_backfill hF hQ path hLast hU hZ
      hUpperPositive hUpperBarrier)

end OmegaY.Geometry.Executable

#print axioms OmegaY.Geometry.Frame.ParentPath.prepend_hit
#print axioms OmegaY.Geometry.Frame.ParentPath.hit_of_record_barrier
#print axioms OmegaY.Geometry.Frame.P_of_record_barrier
#print axioms OmegaY.Geometry.Frame.record_barrier_column_lt
#print axioms OmegaY.Geometry.Frame.common_parent_backfill_le_iff
#print axioms OmegaY.Geometry.Frame.common_parent_backfill_lt_iff
#print axioms OmegaY.Geometry.Frame.common_parent_backfill_eq_iff
#print axioms OmegaY.Geometry.Frame.P_of_record_barrier_backfill
#print axioms OmegaY.Geometry.Executable.findParent_of_record_barrier
#print axioms OmegaY.Geometry.Executable.findParent_of_record_barrier_backfill
