/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualContourRootParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveRootParent
import OmegaY.Expansion.ActualEffectiveContourParent
import OmegaY.Expansion.ActualRootParentEdge

/-!
# Raised source contours whose parent lies in the root column

The original source parent is identified with the root of the actual
controlling interval. Actual execution then supplies an edge to this
block's concrete boundary reference. This module does not identify a
root-column node above the bad-root prefix with a reference below lastTop.
-/

namespace OmegaY.Expansion

open Canonical Geometry

def EffectiveRootReference.extend
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start : Mountain} {references : List Ref} {source : (Frame.ofMountain p.reduced).Node}
    {before after : Mountain} (copy : EffectiveRootReference p start references source before)
    (hPreserved : PreservesColumns before after) :
    EffectiveRootReference p start references source after := by
  have hResult : Canonical.cellAt after copy.reference = .ok copy.target := by
    obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp copy.result_read
    exact cellAt_ok_iff.mpr ⟨nodes, hPreserved.column_read hNodes, hRead⟩
  exact { copy with result_read := hResult }

private theorem root_reference_eq {mountain : Mountain}
    (hValid : MountainValid mountain) {left right : Ref} {a b : Cell}
    (hA : Canonical.cellAt mountain left = .ok a)
    (hB : Canonical.cellAt mountain right = .ok b)
    (hColumn : left.column = right.column) (hRow : a.row = b.row) : left = right := by
  obtain ⟨nodes, hNodes, hLeft⟩ := cellAt_ok_iff.mp hA
  obtain ⟨others, hOthers, hRight⟩ := cellAt_ok_iff.mp hB
  have he : others = nodes := Option.some.inj (hOthers.symm.trans (hColumn ▸ hNodes))
  subst others
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hCV : ColumnValid mountain left.column nodes := hNodesEq ▸ hValid _ hc
  have hIndex := column_read_index_eq_of_row hCV hLeft hRight hRow
  cases left
  cases right
  simp only [Ref.mk.injEq]
  exact ⟨hColumn, hIndex⟩

/-- Reference query equality and actual row uniqueness determine both the
concrete reference and its cell, independently of how an exact cap was
retained in the certificate. -/
theorem EffectiveRootReference.unique
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start : Mountain} {references : List Ref} {source : (Frame.ofMountain p.reduced).Node}
    {leftResult rightResult : Mountain}
    (left : EffectiveRootReference p start references source leftResult)
    (right : EffectiveRootReference p start references source rightResult)
    (hValid : MountainValid start) :
    left.reference = right.reference ∧ left.target = right.target := by
  have hRow := Except.ok.inj (left.start_query.symm.trans right.start_query)
  have hRef := root_reference_eq hValid left.start_read right.start_read
    (left.reference_column.trans right.reference_column.symm) hRow
  exact ⟨hRef, Except.ok.inj
    (left.start_read.symm.trans (by simpa only [hRef] using right.start_read))⟩

private theorem selected_boundary_member {mountain : Mountain} {column : Nat}
    {boundaries : List Row} {references : List Ref}
    (hMap : boundaries.mapM (below mountain column) = .ok references)
    {cap : Row} (hCap : cap ∈ boundaries) {ref : Ref}
    (hBelow : below mountain column cap = .ok ref) : ref ∈ references := by
  have hPairs := below_mapM_pairing hMap
  clear hMap
  induction hPairs with
  | nil => simp only [List.not_mem_nil] at hCap
  | @cons first selected rest refs hFirst hPairs ih =>
      rcases List.mem_cons.mp hCap with rfl | hTail
      · have he : selected = ref := Except.ok.inj (hFirst.symm.trans hBelow)
        simp only [List.mem_cons, he, true_or]
      · exact List.mem_cons.mpr (.inr (ih hTail))

/-- A sufficient actual interval is refined using the real boundary list.
Its target ref stays exactly the same. Literal cap membership is supplied
by the actual map, rather than added to an arbitrary interval by fiat. -/
theorem DynamicBlockState.exact_effective_root_reference
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next rootIndex : Nat}
    {rootRow : Row} (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {parent : (Frame.ofMountain p.reduced).Node} (hParent : parent = a.root) :
    ∃ copy : EffectiveRootReference p start references parent ambient,
      copy.reference = a.reference ∧ copy.target = a.target := by
  obtain ⟨b, hRoot, hTargetRow, hCap⟩ := s.with_exact_root_cap hLast a
  have hParentRow : (Frame.ofMountain p.reduced).height parent = rootRow := hParent ▸ a.root_row
  have hRef : b.reference = a.reference := root_reference_eq s.start_valid
    b.target_start_read a.target_start_read (b.reference_column.trans a.reference_column.symm) hTargetRow
  have hTarget : b.target = a.target := Except.ok.inj
    (b.target_start_read.symm.trans (by simpa only [hRef] using a.target_start_read))
  refine ⟨{
    reference := b.reference
    target := b.target
    degree := b.degree
    source_column := (congrArg (fun node => node.1.val) hParent).trans (congrArg Ref.column a.root_ref)
    reference_column := b.reference_column
    reference_member := selected_boundary_member s.reference_map hCap b.start_below
    start_read := b.target_start_read
    result_read := b.target_ambient_read
    start_query := by simpa only [hParentRow] using b.start_query
    start_below := by simpa only [hParentRow] using b.start_below
    cap_member := by simpa only [hParentRow] using hCap
    target_lower := by simpa only [hParentRow] using b.target_lower
    target_below := by simpa only [hParentRow] using b.target_below
    cap_top := by simpa only [hParentRow] using b.cap_top }, hRef, hTarget⟩

/-- The complete raised, uninterrupted contour branch for a source
root-column parent. The branch inspects only the original marker list and
the actual reference query. Root identity, reference occurrence, output
adjacency, and the raw edge are conclusions. -/
theorem DynamicBlockState.actual_raised_contour_effective_root_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRootColumn : parent.1.val = p.root.column)
    (branch : RaisedSourceContour p start references child) {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (rootCopy : EffectiveRootReference p start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef rootCopy.reference := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead := d.frame_source_read hSource (rfl : child.1.val = child.1.val)
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSource (congrArg Fin.val (Frame.upper_spec hUpper).1)
    simpa only [(Frame.upper_spec hUpper).2] using hRead
  have hUpperRef : Frame.ref sourceUpper = ⟨child.1.val, child.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  have hm : branch.marker ∈ d.bucket := branch.member
  let md := d.marker_data branch.marker hm
  have hMarkerRead : Canonical.cellAt p.reduced branch.marker = .ok md.current :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns branch.marker hm] using hSource,
      md.current_at⟩
  have hCurrent : md.current = branch.current := Except.ok.inj (hMarkerRead.symm.trans branch.source_read)
  have hTarget : md.targetCell.row = branch.target := by
    have hReference : referenceAt ambient references branch.current.row = .ok branch.target :=
      (s.referenceAt_preserved branch.current.row).trans branch.query
    exact Except.ok.inj (md.reference.symm.trans (by simpa only [hCurrent] using hReference))
  have hLiftRaised : F.height child < Row.lift md.current.row md.targetCell.row (F.height child) := by
    simpa only [hCurrent, hTarget] using branch.raised
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  have hReadRow := read.output_row_of_marker hm branch.after.le
    (fun middle hlo hhi => branch.no_between middle hlo (by omega))
  obtain ⟨position, lower, upper, candidate, hLowerOut, hUpperOut,
      hLowerRow, _, hCopy, hShape⟩ := d.copyColumn_source_adjacent_execution
    hParentPower hParentLow hNoPremature hRun hm hChildRead hSourceUpper branch.after branch.no_between
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  have hPosition : position = read.outputIndex := column_read_index_eq_of_row
    hValid hLowerOut read.output_at (hLowerRow.trans hReadRow.symm)
  rcases s.marker_source_transport hLast d hm rfl branch.after.le with
    ⟨_, hFixed⟩ | ⟨rootIndex, a, hActualTarget, hRaised, hChildInside | ⟨_, hFixed⟩⟩
  · exact False.elim ((ne_of_lt hLiftRaised) hFixed.symm)
  · have hRootCol : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
    have hRootRow : F.height a.root = md.current.row := a.root_row
    have hInside' : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) child := by
      simpa only [hRootRow] using hChildInside
    have hBarrier : ∀ rootUpper, F.upper a.root = some rootUpper →
        Row.bump (F.height a.root) a.degree ≤ F.height rootUpper := by
      simpa only [hRootRow] using a.root_upper_barrier
    have hParentInside : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) parent := by
      rcases Frame.root_interval_parent_bump hNormal a.root_real (a.raised_degree hRaised)
          hBarrier hParent hInside' with hi | ⟨hb, _⟩
      · exact hi
      · have hBefore := hb.1
        rw [hRootCol, hRootColumn] at hBefore
        exact False.elim (Nat.lt_irrefl _ hBefore)
    have hParentCol : parent.1 = a.root.1 := Fin.ext (hRootColumn.trans hRootCol.symm)
    have hParentHeight : F.height parent = F.height a.root := le_antisymm
      (Frame.height_le_of_upper_barrier hNormal.toOrdered hBarrier hParentCol hParentInside.2.2)
      hParentInside.2.1
    have hParentEq : parent = a.root := Frame.node_eq_of_column_height hNormal.toOrdered hParentCol hParentHeight
    obtain ⟨rootRead, hReferenceEq, _⟩ := s.exact_effective_root_reference hLast a hParentEq
    obtain ⟨hActualCopy, _, _, _, _, _⟩ :=
      s.copyEdge_root_parent_below_cap a hParent hParentEq rfl hUpper hChildInside.2.2
    have hCopy' : copyEdge ambient (Frame.ref sourceUpper)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift md.current.row a.target.row (F.height sourceUpper)) = .ok candidate := by
      simpa only [hUpperRef, hActualTarget, Frame.height] using hCopy
    have hCandidate : candidate =
        (⟨Row.lift md.current.row a.target.row (F.height sourceUpper), 0, some a.reference⟩ : Cell) :=
      Except.ok.inj (hCopy'.symm.trans hActualCopy)
    let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
      ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
    let rootCopy := rootRead.extend (PreservesColumns.push ambient column)
    refine ⟨childCopy, rootCopy, rfl, rfl, read.outputCell, upper,
      rootRead.target, read.output_read, ?_, ?_, rootCopy.result_read⟩
    · exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
        EffectiveCopyRead.outputRef], by
        change column[read.outputIndex + 1]? = some upper
        simpa only [hPosition] using hUpperOut⟩
    · have hLeft : upper.left = some a.reference := hShape.2.symm.trans (congrArg Cell.left hCandidate)
      simpa only [rootCopy, EffectiveRootReference.extend, hReferenceEq] using hLeft
  · exact False.elim ((ne_of_lt hLiftRaised) hFixed.symm)

set_option maxHeartbeats 800000 in
/-- Every source root parent strictly below the bad root has its actual
next root row as reference cap. The source father-upper bound puts its
child inside that cap. Thus stationary and raised copies share the same
parent-row query; neither a raised condition nor a supplied interval is
needed here. The source successor is unmarked in this interface. -/
theorem DynamicBlockState.actual_lower_root_contour_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRootColumn : parent.1.val = p.root.column)
    (hParentBefore : parent.2.val < p.root.index)
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    (hUpperUnmarked : child.2.val + 1 ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (rootCopy : EffectiveRootReference p start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef rootCopy.reference := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hParentReal := Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hParent).1
  have hParentRef : Frame.ref parent = ⟨p.root.column, parent.2.val⟩ := by simp only [Frame.ref, hRootColumn]
  have hInitialRead : Canonical.cellAt p.initial ⟨p.root.column, parent.2.val⟩ = .ok (F.cell parent) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, parent.2.val⟩)
      p.initial_build p.reduced_build p.root_before_last).trans
      (by simpa only [hParentRef] using cellAt_of_frame_node p.reduced parent)
  obtain ⟨parentNodes, hParentNodes, hParentRead⟩ := cellAt_ok_iff.mp hInitialRead
  have hPositive : 0 < (F.cell parent).row :=
    Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hParentReal)
  obtain ⟨a0⟩ := s.actual_root_interval hLast hParentNodes hParentRead hParentBefore.le hPositive
  have hParentEq0 : parent = a0.root := Executable.ref_injective F (hParentRef.trans a0.root_ref.symm)
  obtain ⟨a, hARoot, _, hCapMember⟩ := s.with_exact_root_cap hLast a0
  have hParentEq : parent = a.root := hParentEq0.trans hARoot.symm
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hBadColumn : badRoot.1 = parent.1 := Fin.ext
    ((congrArg Ref.column hBadRef).trans hRootColumn.symm)
  have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
  have hBound : parent.2.val + 1 < F.length parent.1 := by
    have hb : p.root.index < F.length parent.1 := calc
      p.root.index = badRoot.2.val := hBadIndex.symm
      _ < F.length badRoot.1 := badRoot.2.isLt
      _ = F.length parent.1 := congrArg F.length hBadColumn
    omega
  let parentUpper : F.Node := ⟨parent.1, ⟨parent.2.val + 1, hBound⟩⟩
  have hParentUpper : F.upper parent = some parentUpper := by
    simp only [Frame.upper, hBound, ↓reduceDIte, parentUpper]
  have hParentUpper' : F.upper a.root = some parentUpper := by simpa only [hParentEq] using hParentUpper
  have hCap : Row.bump (F.height parent) a.degree = F.height parentUpper :=
    a.cap_eq_upper_of_boundary hLast hCapMember hParentBefore hParentUpper'
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  have hUpperBound := Frame.father_upper_bound_nodes hNormal hParent hUpper hParentUpper
  have hChildBelow : F.height child < Row.bump (F.height parent) a.degree := by
    rw [hCap]
    have hRow : F.height sourceUpper = Row.B (F.height child) (F.height parent) :=
      (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
    exact (show F.height child < F.height sourceUpper by rw [hRow]; exact Row.lt_B _ _).trans_le hUpperBound
  have hRootCone : Frame.RootCone F a.root parent := by
    rw [← hParentEq]
    exact ⟨parent, hParentReal, rfl, rfl, .refl parent⟩
  obtain ⟨hCone, hRootLower⟩ := Frame.root_cone_child_of_parent hNormal hParent hRootCone
    (by rw [← hParentEq])
  have hInside : Frame.RootInterval F a.root (Row.bump (F.height parent) a.degree) child :=
    ⟨hCone, hRootLower, hChildBelow⟩
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead := d.frame_source_read hSource (rfl : child.1.val = child.1.val)
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSource (congrArg Fin.val (Frame.upper_spec hUpper).1)
    simpa only [(Frame.upper_spec hUpper).2] using hRead
  have hRootRow : F.height a.root = F.height parent := congrArg F.height hParentEq.symm
  have hInside' : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) child := by
    simpa only [hRootRow] using hInside
  have hRootCol : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hRootIndex : a.root.2.val ≤ p.root.index :=
    (congrArg Ref.index a.root_ref).trans_le a.root_prefix
  have hQuery : referenceAt ambient references (F.height a.root) = .ok a.target.row := by
    rw [hRootRow]
    exact a.ambient_query
  obtain ⟨marker, hm, hMarkerRow, hTargetRow⟩ := d.prepared_active_parent_marker_data
    hSource a.root_real hRootCol hRootIndex hInside' rfl s.next_lower hQuery
  let md := d.marker_data marker hm
  have hBefore : marker.index ≤ child.2.val := by
    by_contra hn
    have hLt := d.source_valid.rows_strict _ _ _ _ hChildRead md.current_at (Nat.lt_of_not_ge hn)
    change F.height child < md.current.row at hLt
    rw [show md.current.row = F.height a.root from hMarkerRow] at hLt
    exact (not_lt_of_ge hRootLower) hLt
  have hAfter : marker.index < child.2.val := by
    have hMember : marker.index ∈ d.bucket.map Ref.index := List.mem_map.mpr ⟨marker, hm, rfl⟩
    have hNe : marker.index ≠ child.2.val := fun he => hUnmarked (he ▸ hMember)
    omega
  have hBarrier : ∀ upper, F.upper a.root = some upper →
      Row.bump (F.height a.root) a.degree ≤ F.height upper := by
    rw [hRootRow]
    exact a.root_upper_barrier
  have hNoBetweenLow := d.prepared_no_markers_through_source_index hSource hRootCol hBarrier
    hm hMarkerRow hChildRead hInside'.2.2
  have hNoBetween : ∀ middle, marker.index < middle → middle ≤ child.2.val + 1 →
      middle ∉ d.bucket.map Ref.index := by
    intro middle hLo hHi
    by_cases hLe : middle ≤ child.2.val
    · exact hNoBetweenLow middle hLo hLe
    · have he : middle = child.2.val + 1 := by omega
      exact he ▸ hUpperUnmarked
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  have hReadRow := read.output_row_of_marker hm hBefore hNoBetweenLow
  obtain ⟨position, lower, upper, candidate, hLowerOut, hUpperOut,
      hLowerRow, _, hCopy, hShape⟩ := d.copyColumn_source_adjacent_execution
    hParentPower hParentLow hNoPremature hRun hm hChildRead hSourceUpper hAfter hNoBetween
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  have hPosition : position = read.outputIndex := column_read_index_eq_of_row
    hValid hLowerOut read.output_at (hLowerRow.trans hReadRow.symm)
  obtain ⟨rootRead, hReferenceEq, _⟩ := s.exact_effective_root_reference hLast a hParentEq
  obtain ⟨hActualCopy, _, _, _, _, _⟩ :=
    s.copyEdge_root_parent_below_cap a hParent hParentEq rfl hUpper hChildBelow
  have hUpperRef : Frame.ref sourceUpper = ⟨child.1.val, child.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  have hCopy' : copyEdge ambient (Frame.ref sourceUpper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift (F.height parent) a.target.row (F.height sourceUpper)) = .ok candidate := by
    change copyEdge ambient ⟨child.1.val, child.2.val + 1⟩
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift md.current.row md.targetCell.row (F.height sourceUpper)) = .ok candidate at hCopy
    have hLow : md.current.row = F.height parent := hMarkerRow.trans hRootRow
    have hTarget : md.targetCell.row = a.target.row := hTargetRow
    rw [hUpperRef, ← hLow, ← hTarget]
    exact hCopy
  have hCandidate : candidate =
      (⟨Row.lift (F.height parent) a.target.row (F.height sourceUpper), 0, some a.reference⟩ : Cell) :=
    Except.ok.inj (hCopy'.symm.trans hActualCopy)
  let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  let rootCopy := rootRead.extend (PreservesColumns.push ambient column)
  refine ⟨childCopy, rootCopy, rfl, rfl, read.outputCell, upper,
    rootRead.target, read.output_read, ?_, ?_, rootCopy.result_read⟩
  · exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
      EffectiveCopyRead.outputRef], by
      change column[read.outputIndex + 1]? = some upper
      simpa only [hPosition] using hUpperOut⟩
  · have hLeft : upper.left = some a.reference := hShape.2.symm.trans (congrArg Cell.left hCandidate)
    simpa only [rootCopy, EffectiveRootReference.extend, hReferenceEq] using hLeft

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveRootReference.unique
#print axioms OmegaY.Expansion.DynamicBlockState.exact_effective_root_reference
#print axioms OmegaY.Expansion.DynamicBlockState.actual_raised_contour_effective_root_parent
#print axioms OmegaY.Expansion.DynamicBlockState.actual_lower_root_contour_effective_parent
