/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveContourParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveParent
import OmegaY.Expansion.ActualMarkerTransport
import OmegaY.Expansion.ActualIntervalEdge
import OmegaY.Expansion.PreparedActiveParent

/-!
# Effective parent edges for actually raised source contours

The branch conditions inspect the old marker list and the block's actual
reference query. The source interval and both effective occurrences are
derived. No copied numerical-parent or normality certificate is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Maximality fixes the effective lift even when a different constructive
proof selected the marker and the output occurrence. -/
theorem EffectiveCopyRead.output_row_of_marker
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {sourceIndex : Nat} {sourceCell : Cell} {column : Column}
    (read : EffectiveCopyRead d sourceIndex sourceCell column)
    {marker : Ref} (hm : marker ∈ d.bucket) (hBefore : marker.index ≤ sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index) :
    read.outputCell.row = Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row sourceCell.row := by
  have hIndex : read.marker.index = marker.index := by
    apply Nat.le_antisymm
    · by_contra hn
      exact hNoBetween read.marker.index (by omega) read.marker_before
        (List.mem_map.mpr ⟨read.marker, read.marker_mem, rfl⟩)
    · by_contra hn
      exact read.no_between marker.index (by omega) hBefore
        (List.mem_map.mpr ⟨marker, hm, rfl⟩)
  have hCurrent : (d.marker_data read.marker read.marker_mem).current =
      (d.marker_data marker hm).current := Option.some.inj
    ((d.marker_data read.marker read.marker_mem).current_at.symm.trans
      ((congrArg (fun i : Nat => d.sources[i]?) hIndex).trans
        (d.marker_data marker hm).current_at))
  have hCurrentRow := congrArg Cell.row hCurrent
  have hReference := (d.marker_data read.marker read.marker_mem).reference
  rw [hCurrentRow] at hReference
  have hTargetRow := Except.ok.inj (hReference.symm.trans (d.marker_data marker hm).reference)
  rw [read.output_row, hCurrentRow, hTargetRow]

/-- A source in an actual root interval has that interval's effective
row in every recorded copy. The real source marker enumeration excludes
an intervening controlling marker. This includes a source at the root row. -/
theorem EffectiveCopyOccurrence.interval_row
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node} {result ambient : Mountain}
    (copy : EffectiveCopyOccurrence p block start references source result)
    {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump rootRow a.degree) source)
    (hRight : p.root.column < source.1.val) :
    copy.read.outputCell.row = Row.lift rootRow a.target.row
      ((Frame.ofMountain p.reduced).height source) := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  have hRootRow : F.height a.root = rootRow := a.root_row
  have hSource : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hRootIndex : a.root.2.val ≤ p.root.index :=
    (congrArg Ref.index a.root_ref).trans_le a.root_prefix
  have hInside' : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) source := by
    simpa only [hRootRow] using hInside
  have hTarget : referenceAt copy.before references (F.height a.root) = .ok a.target.row := by
    rw [copy.state.referenceAt_preserved, hRootRow]
    exact a.start_query
  obtain ⟨marker, hm, hMarkerRow, hTargetRow⟩ :=
    d.prepared_active_parent_marker_data hSource a.root_real hRootColumn hRootIndex
      hInside' rfl hRight hTarget
  have hBefore : marker.index ≤ source.2.val := by
    by_contra hn
    have hLt := d.source_valid.rows_strict _ _ _ _ copy.read.source_at
      (d.marker_data marker hm).current_at (Nat.lt_of_not_ge hn)
    change F.height source < (d.marker_data marker hm).current.row at hLt
    rw [hMarkerRow] at hLt
    exact (not_lt_of_ge hInside'.2.1) hLt
  have hBarrier : ∀ upper, F.upper a.root = some upper →
      Row.bump (F.height a.root) a.degree ≤ F.height upper := by
    simpa only [hRootRow] using a.root_upper_barrier
  have hNoBetween := d.prepared_no_markers_through_source_index hSource hRootColumn
    hBarrier hm hMarkerRow copy.read.source_at hInside'.2.2
  have hRow := copy.read.output_row_of_marker hm hBefore hNoBetween
  change copy.read.outputCell.row = Row.lift (d.marker_data marker hm).current.row
    (d.marker_data marker hm).targetCell.row (F.height source) at hRow
  rw [hMarkerRow, hTargetRow, hRootRow] at hRow
  exact hRow

/-- A case predicate stated entirely on the original marker enumeration,
the block's actual reference query, and the source row transform. The
inclusive upper bound excludes a marker seam at the source successor. -/
structure RaisedSourceContour {front : List Nat} {last : Nat} (p : Preparation front last)
    (start : Mountain) (references : List Ref) (child : (Frame.ofMountain p.reduced).Node) where
  marker : Ref
  current : Cell
  target : Row
  member : BucketMem p.marked child.1.val marker
  source_read : Canonical.cellAt p.reduced marker = .ok current
  query : referenceAt start references current.row = .ok target
  after : marker.index < child.2.val
  no_between : ∀ middle, marker.index < middle → middle ≤ child.2.val + 1 →
    middle ∉ (p.marked[child.1.val]?.getD []).map Ref.index
  raised : (Frame.ofMountain p.reduced).height child <
    Row.lift current.row target ((Frame.ofMountain p.reduced).height child)

/-- The branch record is recovered from a constructed effective read by
the three direct case tests: child unmarked, successor unmarked, and the
actual child's row raised. No interval or effective parent is supplied. -/
theorem DynamicBlockState.raised_source_contour_of_effective_read
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    {d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column}
    {child : (Frame.ofMountain p.reduced).Node} (hChildColumn : child.1.val = next)
    {column : Column}
    (read : EffectiveCopyRead d child.2.val ((Frame.ofMountain p.reduced).cell child) column)
    (hUnmarked : child.2.val ∉ d.bucket.map Ref.index)
    (hUpperUnmarked : child.2.val + 1 ∉ d.bucket.map Ref.index)
    (hRaised : (Frame.ofMountain p.reduced).height child < read.outputCell.row) :
    Nonempty (RaisedSourceContour p start references child) := by
  subst next
  let md := d.marker_data read.marker read.marker_mem
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hAfter : read.marker.index < child.2.val := by
    have hBefore := read.marker_before
    have hNe : read.marker.index ≠ child.2.val := by
      intro he
      exact hUnmarked (he ▸ List.mem_map.mpr ⟨read.marker, read.marker_mem, rfl⟩)
    omega
  refine ⟨{
    marker := read.marker
    current := md.current
    target := md.targetCell.row
    member := read.marker_mem
    source_read := cellAt_ok_iff.mpr ⟨d.sources,
      by simpa only [d.marker_columns read.marker read.marker_mem] using hSource, md.current_at⟩
    query := (s.referenceAt_preserved md.current.row).symm.trans md.reference
    after := hAfter
    no_between := ?_
    raised := ?_ }⟩
  · intro middle hLow hHigh
    by_cases hLe : middle ≤ child.2.val
    · exact read.no_between middle hLow hLe
    · have he : middle = child.2.val + 1 := by omega
      exact he ▸ hUpperUnmarked
  · rw [read.output_row] at hRaised
    exact hRaised

private theorem ref_eq_of_same_column_row {mountain : Mountain}
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

/-- A raised, uninterrupted source contour transports the actual source
P edge to its effective parent occurrence. The parent may itself be a
marker; only its column must be strictly right of the bad-root column. -/
theorem DynamicBlockState.actual_raised_contour_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (branch : RaisedSourceContour p start references child)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (parentCopy : EffectiveCopyOccurrence p block start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef parentCopy.outputRef := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead := d.frame_source_read hSource (rfl : child.1.val = child.1.val)
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSource
      (congrArg Fin.val (Frame.upper_spec hUpper).1)
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
  · have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
    have hRootRow : F.height a.root = md.current.row := a.root_row
    have hInside' : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) child := by
      simpa only [hRootRow] using hChildInside
    have hBarrier : ∀ rootUpper, F.upper a.root = some rootUpper →
        Row.bump (F.height a.root) a.degree ≤ F.height rootUpper := by
      simpa only [hRootRow] using a.root_upper_barrier
    have hParentInside : Frame.RootInterval F a.root (Row.bump md.current.row a.degree) parent := by
      rcases Frame.root_interval_parent_bump hNormal a.root_real (a.raised_degree hRaised)
          hBarrier hParent hInside' with hi | ⟨hb, _⟩
      · change Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) parent at hi
        simpa only [hRootRow] using hi
      · have hBefore := hb.1
        rw [hRootColumn] at hBefore
        omega
    obtain ⟨oldParentCopy⟩ := s.prior_effective_occurrence history hLast hRight
      (Frame.P_column_lt hNormal.toOrdered hParent)
    obtain ⟨copied, ref, parentCell, hActualCopy, _, _, hLeft, hColumn, hParentRead, hParentRow, _⟩ :=
      s.copyEdge_interval_parent history hLast a hRaised hChildInside hParent rfl hUpper
    have hCopy' : copyEdge ambient (Frame.ref sourceUpper)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift md.current.row a.target.row (F.height sourceUpper)) = .ok candidate := by
      simpa only [hUpperRef, hActualTarget, Frame.height] using hCopy
    have hCopied : copied = candidate := Except.ok.inj (hActualCopy.symm.trans hCopy')
    subst copied
    have hNotFixed : ¬ parent.1.val < p.root.column := by omega
    have hActualColumn : ref.column = parent.1.val +
        block * (p.reduced.size - 1 - p.root.column) := by
      simpa only [if_neg hNotFixed] using hColumn
    have hActualRow : parentCell.row = oldParentCopy.read.outputCell.row := by
      rw [hParentRow, oldParentCopy.interval_row a hParentInside hRight]
      simp only [Frame.intervalParentRow, hRootColumn, if_neg hNotFixed, a.root_row]
    have hSelected : ref = oldParentCopy.outputRef := ref_eq_of_same_column_row s.ambient_valid
      hParentRead oldParentCopy.output_read (hActualColumn.trans oldParentCopy.source_column.symm) hActualRow
    let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
      ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
    let parentCopy := oldParentCopy.extend (PreservesColumns.push ambient column)
    refine ⟨childCopy, parentCopy, rfl, rfl, read.outputCell, upper,
      oldParentCopy.read.outputCell, read.output_read, ?_, ?_, parentCopy.output_read⟩
    · exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
        EffectiveCopyRead.outputRef], by
        change column[read.outputIndex + 1]? = some upper
        simpa only [hPosition] using hUpperOut⟩
    · exact hShape.2.symm.trans (hSelected ▸ hLeft)
  · exact False.elim ((ne_of_lt hLiftRaised) hFixed.symm)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyRead.output_row_of_marker
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.interval_row
#print axioms OmegaY.Expansion.DynamicBlockState.raised_source_contour_of_effective_read
#print axioms OmegaY.Expansion.DynamicBlockState.actual_raised_contour_effective_parent
