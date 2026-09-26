/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedActiveParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreparedParentCap
import OmegaY.Expansion.CrossedParentSelection
import OmegaY.Geometry.IntervalLegTransport

/-!
# Copied parents active in a root interval

The parent is in the root interval; its child need not be. The actual
source P edge supplies both the child classification and the query-height
bounds. The actual reference target and earlier parent-column copy remain
explicit inputs. No normality of the copied column is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace ColumnCopyData

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {mountain : Mountain} {references : List Ref} {sourceColumn shift : Nat}
  (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
  (hSource : p.reduced[sourceColumn]? = some d.sources)
  {root parent : (Frame.ofMountain p.reduced).Node} {degree : Nat}
  (hRootReal : Frame.Real root)
  (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
  (hParentInside : Frame.RootInterval (Frame.ofMountain p.reduced) root
    (Row.bump ((Frame.ofMountain p.reduced).height root) degree) parent)
  (hParentColumn : parent.1.val = sourceColumn) (hRight : p.root.column < sourceColumn)
  {target : Row}
  (hTarget : referenceAt mountain references ((Frame.ofMountain p.reduced).height root) = .ok target)

include d hSource hRootReal hRootColumn hRootIndex hParentInside hParentColumn hRight hTarget

/-- An active source parent has its own real root-row marker and the
actual reference target, independently of the child's location. -/
theorem prepared_active_parent_marker_data :
    ∃ (marker : Ref) (hm : marker ∈ d.bucket),
      (d.marker_data marker hm).current.row = (Frame.ofMountain p.reduced).height root ∧
      (d.marker_data marker hm).targetCell.row = target := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  obtain ⟨badRoot, hBadRef, _⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp p.restored_root)
  have hBadColumn : badRoot.1.val = p.root.column := congrArg Ref.column hBadRef
  have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  obtain ⟨low, hLowColumn, hLowRow, hMember⟩ := rootCone_marker_witness hNormal
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    hMarkers hRootReal (Fin.ext (hRootColumn.trans hBadColumn.symm))
    (by rw [hBadIndex]; exact hRootIndex)
    (by rw [hBadColumn, hParentColumn]; exact hRight) hParentInside.1
  have hm : Frame.ref low ∈ d.bucket := by
    change BucketMem p.marked sourceColumn (Frame.ref low)
    simpa only [Frame.ref, hParentColumn] using hMember
  let md := d.marker_data (Frame.ref low) hm
  have hLowRead := d.frame_source_read hSource (show low.1.val = sourceColumn by
    rw [hLowColumn, hParentColumn])
  have hCurrentEq : md.current = F.cell low := Option.some.inj (md.current_at.symm.trans hLowRead)
  have hMarkerRow : md.current.row = F.height root := by
    rw [hCurrentEq]
    exact hLowRow
  have hTargetEq : md.targetCell.row = target := Except.ok.inj
    (md.reference.symm.trans (by simpa only [hMarkerRow] using hTarget))
  exact ⟨Frame.ref low, hm, hMarkerRow, hTargetEq⟩

section ParentInputs

variable
  (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
    Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
      (Frame.ofMountain p.reduced).height upper)
  {child childUpper : (Frame.ofMountain p.reduced).Node}
  (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
  (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  {column : Column}
  (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)

include hRootBarrier hParent hChildUpper hParentPower hParentLow hRun

/-- A parent at its source column's top remains the copied top. The
child may be above the chosen cap: strict query growth follows directly
from the source P edge and monotonicity of the same lift. -/
theorem prepared_below_active_top_parent
    (hParentTop : (Frame.ofMountain p.reduced).upper parent = none) :
    ∃ (index : Nat) (actualParent : Cell),
      below (mountain.push column) mountain.size
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨marker, hm, hMarkerRow, hTargetEq⟩ :=
    d.prepared_active_parent_marker_data hSource hRootReal hRootColumn hRootIndex
      hParentInside hParentColumn hRight hTarget
  have hLowerRead := d.frame_source_read hSource hParentColumn
  have hColumnRead : p.reduced[parent.1.val]? = some d.sources := by
    simpa only [hParentColumn] using hSource
  have hLength : F.length parent.1 = d.sources.size := by
    change p.reduced[parent.1.val].size = d.sources.size
    exact congrArg Array.size (Array.getElem?_eq_some_iff.mp hColumnRead).2
  have hNoUpper : ¬ parent.2.val + 1 < F.length parent.1 := by
    intro hBound
    change F.upper parent = none at hParentTop
    simp only [Frame.upper, hBound, ↓reduceDIte, reduceCtorEq] at hParentTop
  have hTopIndex : parent.2.val = d.sources.size - 1 := by
    have hIndex : parent.2.val < F.length parent.1 := parent.2.isLt
    omega
  have hTopRead : d.sources[d.sources.size - 1]? = some (F.cell parent) := by
    simpa only [hTopIndex] using hLowerRead
  have hNoBetween := d.prepared_no_markers_through_source_index hSource hRootColumn hRootBarrier
    hm hMarkerRow hLowerRead hParentInside.2.2
  have hHighest : ∀ other ∈ d.bucket, other.index ≤ marker.index := by
    intro other hOther
    by_contra hn
    have hIndex := (Array.getElem?_eq_some_iff.mp (d.marker_data other hOther).upper_at).1
    exact hNoBetween other.index (by omega) (by omega) (List.mem_map.mpr ⟨other, hOther, rfl⟩)
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hChildRow : F.height childUpper = Row.B (F.height child) (F.height parent) :=
    (Frame.aboveHeight_of_upper hChildUpper).symm.trans (hNormal.above_row hp)
  have hQueryLow : Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row (F.cell parent).row <
      Row.lift (F.height root) target (F.height childUpper) := by
    change Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row (F.height parent) < _
    rw [hMarkerRow, hTargetEq]
    apply Row.lift_strictMono hParentInside.2.1
    rw [hChildRow]
    exact (Frame.P_height_le hNormal.toOrdered hp).trans_lt (Row.lt_B _ _)
  obtain ⟨actualParent, hBelow, _, hActual, hRow, _⟩ :=
    d.copyColumn_below_lifted_source_top hParentPower hParentLow
      (build_source_no_premature_one p.reduced_build hSource) hRun hm hHighest hTopRead hQueryLow
  exact ⟨column.size - 1, actualParent, hBelow, hActual,
    by simpa only [hMarkerRow, hTargetEq, Frame.height] using hRow⟩

/-- Every active strict-above-root parent is selected in its actual copied
column, even if the source child has already crossed the interval cap.
Source first-parent and father-upper-bound theorems supply the entire
query interval; neither a copied barrier nor a query bound is assumed. -/
theorem prepared_below_active_parent
    (hDegree : 0 < degree)
    (hParentAbove : (Frame.ofMountain p.reduced).height root <
      (Frame.ofMountain p.reduced).height parent)
    (hTargetCap : target < Row.bump ((Frame.ofMountain p.reduced).height root) degree) :
    ∃ (index : Nat) (actualParent : Cell),
      below (mountain.push column) mountain.size
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_legal (build_success_legal p.reduced_build) p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  rcases Frame.root_interval_child_or_above_cap hNormal hp hParentInside with hChild | hChildAbove
  · exact d.prepared_below_parent_above_root hSource hRootReal hDegree hRootColumn hRootIndex
      hRootBarrier hParent hChild hChildUpper hParentColumn hRight hTarget
      hParentPower hParentLow hParentAbove hRun hTargetCap
  · cases hParentUpper : F.upper parent with
    | none =>
      exact d.prepared_below_active_top_parent hSource hRootReal hRootColumn hRootIndex
        hParentInside hParentColumn hRight hTarget hRootBarrier hParent hChildUpper
        hParentPower hParentLow hRun hParentUpper
    | some parentUpper =>
      obtain ⟨marker, hm, hMarkerRow, hTargetEq⟩ :=
        d.prepared_active_parent_marker_data hSource hRootReal hRootColumn hRootIndex
          hParentInside hParentColumn hRight hTarget
      let md := d.marker_data marker hm
      have hLowerRead := d.frame_source_read hSource hParentColumn
      have hUpperRead : d.sources[parent.2.val + 1]? = some (F.cell parentUpper) := by
        have h := d.frame_source_read hSource (show parentUpper.1.val = sourceColumn by
          rw [(Frame.upper_spec hParentUpper).1, hParentColumn])
        simpa only [(Frame.upper_spec hParentUpper).2] using h
      have hAfter : marker.index < parent.2.val := by
        by_contra hn
        have hLe : parent.2.val ≤ marker.index := by omega
        have hRow : (F.cell parent).row ≤ md.current.row := by
          rcases eq_or_lt_of_le hLe with he | hl
          · have hc : F.cell parent = md.current := Option.some.inj
              (hLowerRead.symm.trans (by simpa only [he] using md.current_at))
            exact congrArg Cell.row hc |>.le
          · exact (d.source_valid.rows_strict _ _ _ _ hLowerRead md.current_at hl).le
        rw [hMarkerRow] at hRow
        exact not_lt_of_ge hRow hParentAbove
      have hNoBetween := d.prepared_no_markers_through_source_index hSource hRootColumn
        hRootBarrier hm hMarkerRow hLowerRead hParentInside.2.2
      have hChildRow : F.height childUpper = Row.B (F.height child) (F.height parent) :=
        (Frame.aboveHeight_of_upper hChildUpper).symm.trans (hNormal.above_row hp)
      have hLow : (F.cell parent).row < F.height childUpper := by
        rw [hChildRow]
        exact (Frame.P_height_le hNormal.toOrdered hp).trans_lt (Row.lt_B _ _)
      have hHigh : F.height childUpper ≤ (F.cell parentUpper).row :=
        Frame.father_upper_bound_nodes hNormal hp hChildUpper hParentUpper
      have hUpperCap : Row.bump (F.height root) degree ≤ (F.cell parentUpper).row := by
        apply hChildAbove.trans
        apply le_trans (b := F.height childUpper)
        · rw [hChildRow]
          exact (Row.lt_B _ _).le
        · exact hHigh
      obtain ⟨index, actualParent, hBelow, _, hCell, hRow⟩ :=
        d.copyColumn_below_lifted_crossed_pair hParentPower hParentLow
          (build_source_no_premature_one p.reduced_build hSource) hRun hm
          hLowerRead hUpperRead hAfter hNoBetween
          (by simpa only [hMarkerRow, hTargetEq] using hTargetCap)
          (by simpa only [hMarkerRow] using hUpperCap) hLow hHigh
      exact ⟨index, actualParent,
        by simpa only [hMarkerRow, hTargetEq] using hBelow,
        hCell, by simpa only [hMarkerRow, hTargetEq, Frame.height] using hRow⟩

end ParentInputs

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.prepared_active_parent_marker_data
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_below_active_top_parent
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_below_active_parent
