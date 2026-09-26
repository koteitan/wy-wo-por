/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicInactiveParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InactiveParentSelection
import OmegaY.Expansion.HistoryColumnData
import OmegaY.Expansion.ActualHighParent

/-!
# Actual history selects inactive copied parents at their source rows

An earlier copied parent column and its successful execution are recovered
from the real block history. The controlling marker and reference are read
from the frozen source and the actual block-start reference list. Only the
local cap-above-marker/below-parent condition remains; no copied Normal,
parent-power/low-support packet, or separate copy success is supplied.

The final copyEdge theorem executes the unchanged source-upper row. It is
an edge-level result, not a claim of returned adjacency or that an arbitrary
child's physical copied row is unchanged. Identity-target cases whose cap
is still above the parent are not inferred from the inactive-cap case.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A locally inactive numerical source parent is selected in the actual
current copied column. Source normality also handles a parent that is a top. -/
theorem DynamicBlockState.below_inactive_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hRight : p.root.column < parent.1.val)
    {marker : Ref} (hm : marker ∈ p.marked[parent.1.val]?.getD []) {markerCell : Cell}
    (hMarkerRead : Canonical.cellAt p.reduced marker = .ok markerCell)
    (hIndex : marker.index ≤ parent.2.val)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ parent.2.val →
      middle ∉ (p.marked[parent.1.val]?.getD []).map Ref.index)
    {target : Row} (hReference : referenceAt start references markerCell.row = .ok target)
    {degree : Nat} (hTargetCap : target < Row.bump markerCell.row degree)
    (hCap : Row.bump markerCell.row degree ≤ (Frame.ofMountain p.reduced).height parent) :
    ∃ (ref : Ref) (cell : Cell),
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        ((Frame.ofMountain p.reduced).height childUpper) = .ok ref ∧
      Canonical.cellAt ambient ref = .ok cell ∧
      ref.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      cell.row = (Frame.ofMountain p.reduced).height parent := by
  have hNormal := build_normal_of_success p.reduced_build
  have hBeforeNext : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt hNormal.toOrdered hParent
  obtain ⟨before, column, d, hRun, hPreserve, hSource, hNoPremature, _, _, hQueries, _⟩ :=
    s.prior_column_data history hLast hRight hBeforeNext
  let md := d.marker_data marker hm
  have hCurrentSource : Canonical.cellAt p.reduced marker = .ok md.current :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns marker hm] using hSource, md.current_at⟩
  have hCurrentEq : md.current = markerCell := Except.ok.inj (hCurrentSource.symm.trans hMarkerRead)
  have hBeforeTarget : referenceAt before references markerCell.row = .ok target :=
    (hQueries markerCell.row).trans ((s.referenceAt_preserved markerCell.row).trans hReference)
  have hMarkerTarget : referenceAt before references markerCell.row = .ok md.targetCell.row := by
    simpa only [hCurrentEq] using md.reference
  have hTargetEq : md.targetCell.row = target := Except.ok.inj (hMarkerTarget.symm.trans hBeforeTarget)
  have hParentRead : d.sources[parent.2.val]? = some ((Frame.ofMountain p.reduced).cell parent) := by
    have hArray := (Array.getElem?_eq_some_iff.mp hSource).2
    rw [← hArray]
    exact Array.getElem?_eq_getElem parent.2.isLt
  have hOldBelow := canonical_below_of_parent p.reduced_valid hNormal hParent hUpper
  have hBeforeBelow : below before parent.1.val ((Frame.ofMountain p.reduced).height childUpper) =
      .ok (Frame.ref parent) := by
    simpa only [below, columnAt, OmegaY.Expansion.lookup, Canonical.cellAt,
      d.source_column, hSource] using hOldBelow
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hRow⟩ :=
    d.copyColumn_below_inactive_source_preserved hNoPremature hRun hPreserve hm hBeforeBelow
      hParentRead hIndex hNoBetween
      (by change md.targetCell.row < Row.bump md.current.row degree; rw [hCurrentEq, hTargetEq]; exact hTargetCap)
      (by change Row.bump md.current.row degree ≤ (Frame.ofMountain p.reduced).height parent
          rw [hCurrentEq]; exact hCap)
  rw [← d.destination] at hBelow hColumn
  exact ⟨ref, cell, hBelow, hRead, hColumn, hRow⟩

/-- Select the controlling marker from the actual prior-copy data. Its
source read, maximality, and actual block reference are outputs. The cap
test remains explicit rather than being inferred from a stationary label. -/
theorem DynamicBlockState.inactive_parent_control
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hRight : p.root.column < parent.1.val) :
    ∃ marker markerCell target,
      marker ∈ p.marked[parent.1.val]?.getD [] ∧
      Canonical.cellAt p.reduced marker = .ok markerCell ∧
      marker.index ≤ parent.2.val ∧
      (∀ middle, marker.index < middle → middle ≤ parent.2.val →
        middle ∉ (p.marked[parent.1.val]?.getD []).map Ref.index) ∧
      referenceAt start references markerCell.row = .ok target ∧ markerCell.row ≤ target ∧
      ∀ degree, target < Row.bump markerCell.row degree →
        Row.bump markerCell.row degree ≤ (Frame.ofMountain p.reduced).height parent →
        ∃ (ref : Ref) (cell : Cell),
          below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
            ((Frame.ofMountain p.reduced).height childUpper) = .ok ref ∧
          Canonical.cellAt ambient ref = .ok cell ∧
          ref.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
          cell.row = (Frame.ofMountain p.reduced).height parent := by
  have hNormal := build_normal_of_success p.reduced_build
  have hBeforeNext : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt hNormal.toOrdered hParent
  obtain ⟨before, column, d, _, _, hSource, _, _, _, hQueries, _⟩ :=
    s.prior_column_data history hLast hRight hBeforeNext
  obtain ⟨marker, hm, hIndex, hNoBetween⟩ := d.maximal_source_marker parent.2.val
  let md := d.marker_data marker hm
  have hRead : Canonical.cellAt p.reduced marker = .ok md.current :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns marker hm] using hSource, md.current_at⟩
  have hReference : referenceAt start references md.current.row = .ok md.targetCell.row :=
    ((hQueries md.current.row).trans (s.referenceAt_preserved md.current.row)).symm.trans md.reference
  refine ⟨marker, md.current, md.targetCell.row, hm, hRead, hIndex, hNoBetween,
    hReference, md.target_lower, ?_⟩
  intro degree hTargetCap hCap
  exact s.below_inactive_parent history hLast hParent hChildColumn hUpper hRight
    hm hRead hIndex hNoBetween hReference hTargetCap hCap

/-- Execute the actual source-upper copyEdge at its unchanged row. All
source stored-leg, nonzero, destination, and earlier-copy success facts are
derived. The output B formula names the original child row explicitly. -/
theorem DynamicBlockState.copyEdge_inactive_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hRight : p.root.column < parent.1.val)
    {marker : Ref} (hm : marker ∈ p.marked[parent.1.val]?.getD []) {markerCell : Cell}
    (hMarkerRead : Canonical.cellAt p.reduced marker = .ok markerCell)
    (hIndex : marker.index ≤ parent.2.val)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ parent.2.val →
      middle ∉ (p.marked[parent.1.val]?.getD []).map Ref.index)
    {target : Row} (hReference : referenceAt start references markerCell.row = .ok target)
    {degree : Nat} (hTargetCap : target < Row.bump markerCell.row degree)
    (hCap : Row.bump markerCell.row degree ≤ (Frame.ofMountain p.reduced).height parent) :
    ∃ (copied : Cell) (actualRef : Ref) (actualParent : Cell),
      copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column))
        p.root.column ((Frame.ofMountain p.reduced).height upper) = .ok copied ∧
      copied.row = (Frame.ofMountain p.reduced).height upper ∧ copied.value = 0 ∧
      copied.left = some actualRef ∧
      actualRef.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      Canonical.cellAt ambient actualRef = .ok actualParent ∧
      actualParent.row = (Frame.ofMountain p.reduced).height parent ∧
      copied.row = Row.B ((Frame.ofMountain p.reduced).height child) actualParent.row := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨actualRef, actualParent, hBelow, hRead, hRefColumn, hParentRow⟩ :=
    s.below_inactive_parent history hLast hParent hChildColumn hUpper hRight
      hm hMarkerRead hIndex hNoBetween hReference hTargetCap hCap
  change below ambient ((Frame.ref parent).column + block * (p.reduced.size - 1 - p.root.column))
    ((Frame.ofMountain p.reduced).height upper) = .ok actualRef at hBelow
  have hNormal := build_normal_of_success p.reduced_build
  have hChildReal : Frame.Real child := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, hSourceB, _, hStored⟩ := hNormal.upper_step child upper hChildReal hUpper
  have hParentEq : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  change (F.cell upper).left = some (Frame.ref parent) at hStored
  have hSourceRead : lookup ambient (Frame.ref upper) = .ok (F.cell upper) :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp
      (p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced upper)))
  have hUpperReal : Frame.Real upper := by
    have hi := (Frame.upper_spec hUpper).2
    unfold Frame.Real
    omega
  have hNonzero : (F.cell upper).row ≠ 0 := by
    intro hz
    have hPositive := Frame.one_le_height hNormal.toOrdered hUpperReal
    change (1 : Row) ≤ (F.cell upper).row at hPositive
    rw [hz] at hPositive
    exact (not_le_of_gt Row.zero_lt_one) hPositive
  have hDestination : actualRef.column <
      (Frame.ref upper).column + block * (p.reduced.size - 1 - p.root.column) := by
    rw [hRefColumn]
    apply Nat.add_lt_add_right
    change parent.1.val < upper.1.val
    rw [(Frame.upper_spec hUpper).1]
    exact Frame.P_column_lt hNormal.toOrdered hParent
  let copied : Cell := ⟨F.height upper, 0, some actualRef⟩
  refine ⟨copied, actualRef, actualParent, ?_, rfl, rfl, rfl, hRefColumn, hRead, hParentRow, ?_⟩
  · have hMoved : ¬ (Frame.ref parent).column < p.root.column := Nat.not_lt_of_ge hRight.le
    simp [copyEdge, copied, hSourceRead, hNonzero, leftOf, hStored,
      hMoved, hBelow, Nat.not_le_of_gt hDestination]
    rfl
  · change F.height upper = Row.B (F.height child) actualParent.row
    rw [hParentRow]
    exact hSourceB

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.below_inactive_parent
#print axioms OmegaY.Expansion.DynamicBlockState.inactive_parent_control
#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_inactive_parent
