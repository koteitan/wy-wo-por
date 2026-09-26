/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SecondSegments.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialEndpoints
import OmegaY.Expansion.FrozenSource

/-!
# Actual marker segments of the second source column

The frozen source upper parent is either in the root column or is a marker
of the first source column. Its shifted parent is correspondingly the old
boundary or the first completed copy. In the latter case the lifted target
is supplied by actual first-copy endpoint preservation, with a fresh index.
The new ambient mountain is valid, but is not assumed canonical.
-/

namespace OmegaY.Expansion

open Canonical

structure SecondSegmentData {front : List Nat} {last : Nat}
    (p : Preparation front last) (references : List Ref) (firstColumn : Column) (marker : Ref) where
  sources : Column
  current : Cell
  upper : Cell
  sourceParent : Ref
  sourceParentCell : Cell
  parentNodes : Column
  targetIndex : Nat
  targetCell : Cell
  marker_column : marker.column = p.root.column + 2
  base_source_column : p.reduced[p.root.column + 2]? = some sources
  source_column : (p.reduced.push firstColumn)[p.root.column + 2]? = some sources
  current_at : sources[marker.index]? = some current
  upper_at : sources[marker.index + 1]? = some upper
  upper_left : upper.left = some sourceParent
  parent_read : Canonical.cellAt p.reduced sourceParent = .ok sourceParentCell
  parent_row : sourceParentCell.row = current.row
  parent_nodes : (p.reduced.push firstColumn)[sourceParent.column +
    (p.reduced.size - 1 - p.root.column)]? = some parentNodes
  target_at : parentNodes[targetIndex]? = some targetCell
  base_reference : referenceAt p.reduced references current.row = .ok targetCell.row
  reference : referenceAt (p.reduced.push firstColumn) references current.row = .ok targetCell.row
  target_lower : current.row ≤ targetCell.row
  source_top : TopOne sources
  source_power : ColumnPowerSteps sources
  source_positive : SourceAboveBottomPositive (p.reduced.push firstColumn) sources
  destination : p.root.column + 2 + (p.reduced.size - 1 - p.root.column) ≤
    (p.reduced.push firstColumn).size
  ambient_valid : MountainValid (p.reduced.push firstColumn)

theorem SecondSegmentData.current_read {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {firstColumn : Column} {marker : Ref}
    (d : SecondSegmentData p references firstColumn marker) :
    Canonical.cellAt p.reduced marker = .ok d.current :=
  cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_column] using d.base_source_column,
    d.current_at⟩

/-- All second-source data, including the actual lifted target in its exact
shifted parent column, follows from the completed first copy. -/
theorem Preparation.second_segment_data {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {firstColumn : Column}
    (hCopy : copyColumn p.reduced p.marked references (p.root.column + 1)
      (p.initial.size - 1 - p.root.column) p.root.column = .ok firstColumn)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 2) marker) :
    Nonempty (SecondSegmentData p references firstColumn marker) := by
  have hPreserve := PreservesColumns.push p.reduced firstColumn
  obtain ⟨otherColumn, hOtherCopy, _, _, _, hAmbient⟩ := p.initial_copyColumn_valid hLast hMap
  have hOtherEq : otherColumn = firstColumn := Except.ok.inj (hOtherCopy.symm.trans hCopy)
  subst otherColumn
  obtain ⟨rootIndex, parent, current, upper, parentCell, _, hCurrent, hUpper,
    hLeft, hParentLeft, hParent, hParentRow, hParentCase⟩ :=
    markers_upper_parent
      (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
      p.root_valid p.markers_built hMarker
  have hMarkerColumn : marker.column = p.root.column + 2 := (p.marker_iff.mp hMarker).1
  obtain ⟨sources, hSources, hCurrentIndex⟩ := hCurrent
  have hSourceColumn : p.reduced[p.root.column + 2]? = some sources := by
    simpa only [hMarkerColumn] using hSources
  obtain ⟨upperSources, hUpperSources, hUpperIndex⟩ := hUpper
  have hUpperSourcesEq : upperSources = sources := Option.some.inj (hUpperSources.symm.trans hSources)
  subst upperSources
  have hCurrentRead : Canonical.cellAt p.reduced marker = .ok current :=
    cellAt_ok_iff.mpr ⟨sources, hSources, hCurrentIndex⟩
  have hParentRead : Canonical.cellAt p.reduced parent = .ok parentCell := cellAt_ok_iff.mpr hParent
  obtain ⟨rootNodes, index, lower, hRootColumn, hLower, hRootIndex, hLowerRow⟩ :=
    p.marker_root_prefix_read hMarker hCurrentRead
  obtain ⟨_, _, targetRef, boundaryTarget, _, _, hBelow, hTargetRead, hReference, hLow, _, _⟩ :=
    p.initial_referenceAt_root_interval hLast hRootColumn hLower hRootIndex hMap
  have hBaseReference : referenceAt p.reduced references current.row = .ok boundaryTarget.row := by
    simpa only [hLowerRow] using hReference
  have hTargetLower : current.row ≤ boundaryTarget.row := by
    simpa only [hLowerRow] using hLow
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRootLeft := p.root_before_last
  have hTargetWitness : ∃ (nodes : Column) (targetIndex : Nat) (targetCell : Cell),
      (p.reduced.push firstColumn)[parent.column + (p.reduced.size - 1 - p.root.column)]? = some nodes ∧
      nodes[targetIndex]? = some targetCell ∧ targetCell.row = boundaryTarget.row := by
    rcases hParentCase with hRoot | hEarlier
    · have hParentColumn : parent.column = p.root.column := by
        simpa only using congrArg Ref.column hRoot
      have hShift : parent.column + (p.reduced.size - 1 - p.root.column) =
          p.reduced.size - 1 := by omega
      have hTargetColumn : targetRef.column = p.reduced.size - 1 :=
        (below_result (Array.getElem?_eq_getElem p.reduced_last_exists) hBelow).1
      obtain ⟨nodes, hNodes, hTargetIndex⟩ := cellAt_ok_iff.mp hTargetRead
      have hNodesAmbient := hPreserve.column_read hNodes
      exact ⟨nodes, targetRef.index, boundaryTarget,
        by simpa only [hShift, hTargetColumn] using hNodesAmbient, hTargetIndex, rfl⟩
    · have hEarlierSpec := p.marker_iff.mp hEarlier
      have hParentColumn : parent.column = p.root.column + 1 := by
        have hParentRight := hEarlierSpec.2.1
        omega
      have hEarlier' : BucketMem p.marked (p.root.column + 1) parent := by
        simpa only [hParentColumn] using hEarlier
      have hParentReference : referenceAt p.reduced references parentCell.row = .ok boundaryTarget.row := by
        simpa only [hParentRow] using hBaseReference
      obtain ⟨_, targetIndex, targetCell, hTargetAt, hTargetRow⟩ :=
        p.initial_copyColumn_marker_target_reads hLast hMap hCopy hEarlier' hParentRead hParentReference
      have hShift : parent.column + (p.reduced.size - 1 - p.root.column) = p.reduced.size := by
        omega
      refine ⟨firstColumn, targetIndex, targetCell, ?_, hTargetAt, hTargetRow⟩
      simp only [hShift, Array.getElem?_push_size]
  obtain ⟨parentNodes, targetIndex, targetCell, hParentNodes, hTargetAt, hTargetRow⟩ := hTargetWitness
  obtain ⟨hSourceAmbient, hTop, hPower, hPositive⟩ :=
    frozen_source_facts p.reduced_build hPreserve hSourceColumn
  have hRefPreserved := hPreserve.referenceAt (p.initial_references_valid hMap) current.row
  exact ⟨{
    sources := sources
    current := current
    upper := upper
    sourceParent := parent
    sourceParentCell := parentCell
    parentNodes := parentNodes
    targetIndex := targetIndex
    targetCell := targetCell
    marker_column := hMarkerColumn
    base_source_column := hSourceColumn
    source_column := hSourceAmbient
    current_at := hCurrentIndex
    upper_at := hUpperIndex
    upper_left := hLeft
    parent_read := hParentRead
    parent_row := hParentRow
    parent_nodes := hParentNodes
    target_at := hTargetAt
    base_reference := by simpa only [hTargetRow] using hBaseReference
    reference := by simpa only [hTargetRow] using hRefPreserved.trans hBaseReference
    target_lower := by simpa only [hTargetRow] using hTargetLower
    source_top := hTop
    source_power := hPower
    source_positive := hPositive
    destination := by simp only [Array.size_push]; omega
    ambient_valid := hAmbient }⟩

/-- Mechanical use of the generic actual segment theorem with the derived
second-source data. It does not finish the second column. -/
theorem SecondSegmentData.total_nodup {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {firstColumn : Column} {marker : Ref}
    (d : SecondSegmentData p references firstColumn marker) :
    ∃ result, copySegment (p.reduced.push firstColumn) d.sources references (p.root.column + 2)
      ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result ∧
      (result.map Cell.row).Nodup := by
  obtain ⟨copied, upperPath, gap, _, _, _, _, _, hRun, hNodup, _⟩ :=
    copySegment_total_nodup d.ambient_valid d.source_column (by omega) d.destination d.source_top
      references ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
      d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at d.reference d.target_lower
      (rootColumn := p.root.column)
  exact ⟨[copied] ++ upperPath ++ gap, hRun, hNodup⟩

/-- All actual marker segments of an existing second source succeed in
the extended mountain. The explicit source bound excludes an empty out-of-range
second-column statement when the block width is one. -/
theorem Preparation.second_segments_total_nodup {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {firstColumn : Column}
    (hCopy : copyColumn p.reduced p.marked references (p.root.column + 1)
      (p.initial.size - 1 - p.root.column) p.root.column = .ok firstColumn)
    (hSecond : p.root.column + 2 < p.reduced.size) :
    ∃ sources, (p.reduced.push firstColumn)[p.root.column + 2]? = some sources ∧
      ∀ marker, BucketMem p.marked (p.root.column + 2) marker →
        ∃ result, copySegment (p.reduced.push firstColumn) sources references (p.root.column + 2)
          ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
          (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result ∧
          (result.map Cell.row).Nodup := by
  let sources := p.reduced[p.root.column + 2]
  have hSources : p.reduced[p.root.column + 2]? = some sources := Array.getElem?_eq_getElem hSecond
  refine ⟨sources, (PreservesColumns.push p.reduced firstColumn).column_read hSources, ?_⟩
  intro marker hMarker
  obtain ⟨d⟩ := p.second_segment_data hLast hMap hCopy hMarker
  have hSourcesEq : d.sources = sources := Option.some.inj (d.base_source_column.symm.trans hSources)
  simpa only [hSourcesEq] using d.total_nodup

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.second_segment_data
#print axioms OmegaY.Expansion.SecondSegmentData.total_nodup
#print axioms OmegaY.Expansion.Preparation.second_segments_total_nodup
