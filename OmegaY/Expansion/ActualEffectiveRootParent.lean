/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveRootParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveMarkerParent
import OmegaY.Expansion.ExactRootCap

/-!
# Actual effective marker edges into the current block boundary

A source root-column parent is represented by the concrete reference
selected in this block's start mountain. The certificate retains its
literal boundary-cap membership and its actual reads. It does not claim
that the boundary reference's outgoing path has already been reconstructed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- An actual selected root reference, retained into a later mountain.
The source node and every query concern the original root row; no copied
parent edge or numerical search assertion occurs in this record. -/
structure EffectiveRootReference {front : List Nat} {last : Nat}
    (p : Preparation front last) (start : Mountain) (references : List Ref)
    (source : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  reference : Ref
  target : Cell
  degree : Nat
  source_column : source.1.val = p.root.column
  reference_column : reference.column = start.size - 1
  reference_member : reference ∈ references
  start_read : Canonical.cellAt start reference = .ok target
  result_read : Canonical.cellAt result reference = .ok target
  start_query : referenceAt start references ((Frame.ofMountain p.reduced).height source) = .ok target.row
  start_below : below start (start.size - 1)
    (Row.bump ((Frame.ofMountain p.reduced).height source) degree) = .ok reference
  cap_member : Row.bump ((Frame.ofMountain p.reduced).height source) degree ∈ p.boundaries
  target_lower : (Frame.ofMountain p.reduced).height source ≤ target.row
  target_below : target.row < Row.bump ((Frame.ofMountain p.reduced).height source) degree
  cap_top : Row.bump ((Frame.ofMountain p.reduced).height source) degree ≤ p.lastTop.row

private theorem boundary_selected_mem {mountain : Mountain} {column : Nat}
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

private theorem marker_parent_row {input : List Nat} {mountain : Mountain}
    (hBuild : build input = .ok mountain)
    {root child parent : (Frame.ofMountain mountain).Node} {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked)
    (hParent : (Frame.ofMountain mountain).P child = some parent)
    (hMarked : BucketMem marked (Frame.ref child).column (Frame.ref child)) :
    (Frame.ofMountain mountain).height child = (Frame.ofMountain mountain).height parent := by
  have hNormal := build_normal_of_success hBuild
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨hRight, low, _, hColumn, _, hPath, hRow⟩ :=
    (build_markers_real_member_iff_parentPath hBuild hMarkers hReal).mp hMarked
  cases hPath with
  | refl =>
      have he := congrArg Fin.val hColumn
      omega
  | @cons child next low hNext tail =>
      have he : next = parent := Option.some.inj (hNext.symm.trans hParent)
      subst next
      exact le_antisymm (by rw [hRow]; exact tail.height_le hNormal.toOrdered)
        (Frame.P_height_le hNormal.toOrdered hParent)

private theorem root_refs_equal {mountain : Mountain}
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

/-- The current block's actual map supplies the root-parent occurrence.
The supplied source child is genuinely marked, so its source row equals
its root-column parent's row. Neither a cap nor a selected ref is an input. -/
theorem DynamicBlockState.actual_marker_root_reference
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hRootColumn : parent.1.val = p.root.column)
    (hMarked : BucketMem p.marked (Frame.ref child).column (Frame.ref child)) :
    ∃ _rootCopy : EffectiveRootReference p start references parent ambient,
      (Frame.ofMountain p.reduced).height child = (Frame.ofMountain p.reduced).height parent := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  have hRow := marker_parent_row p.reduced_build hMarkers hParent hMarked
  obtain ⟨nodes, index, lower, hNodes, hLower, hIndex, hLowerRow⟩ :=
    p.marker_root_prefix_read hMarked (cellAt_of_frame_node p.reduced child)
  have hSourceRow : lower.row = F.height parent := hLowerRow.trans hRow
  obtain ⟨cap, degree, ref, target, hCap, hPower, hTop, hBelow, hRead, hColumn,
      hQuery, hLow, hHigh, _⟩ := RootRowsInColumn.root_interval_with_boundary
    s.boundary_rows s.start_valid hLast hNodes hLower hIndex s.reference_map
  obtain ⟨targetNodes, hTargetNodes, hTargetRead⟩ := cellAt_ok_iff.mp hRead
  have hAmbient : Canonical.cellAt ambient ref = .ok target :=
    cellAt_ok_iff.mpr ⟨targetNodes, s.start_preserved.column_read hTargetNodes, hTargetRead⟩
  refine ⟨{
    reference := ref
    target := target
    degree := degree
    source_column := hRootColumn
    reference_column := hColumn
    reference_member := boundary_selected_mem s.reference_map hCap hBelow
    start_read := hRead
    result_read := hAmbient
    start_query := by simpa only [hSourceRow] using hQuery
    start_below := by simpa only [hPower, hSourceRow] using hBelow
    cap_member := by simpa only [hPower, hSourceRow] using hCap
    target_lower := by simpa only [hSourceRow] using hLow
    target_below := by simpa only [hPower, hSourceRow] using hHigh
    cap_top := by simpa only [hPower, hSourceRow] using hTop }, hRow⟩

/-- An actual marked child copies to an effective node whose raw parent
is exactly the concrete root reference selected at this block's start.
This includes zero gaps and raised gaps. It makes no claim about the
outgoing path or numerical parent search of the boundary node itself. -/
theorem DynamicBlockState.actual_marker_effective_root_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRootColumn : parent.1.val = p.root.column)
    (hMarked : BucketMem p.marked (Frame.ref child).column (Frame.ref child))
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (rootCopy : EffectiveRootReference p start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      childCopy.read.outputCell.row = rootCopy.target.row ∧
      RawRefEdge (ambient.push column) childCopy.outputRef rootCopy.reference := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨rootRead, hSourceRow⟩ := s.actual_marker_root_reference hLast hParent hRootColumn hMarked
  change F.height child = F.height parent at hSourceRow
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead : d.sources[child.2.val]? = some (F.cell child) := by
    have hArray := (Array.getElem?_eq_some_iff.mp hSource).2
    rw [← hArray]
    exact Array.getElem?_eq_getElem child.2.isLt
  have hm : (Frame.ref child) ∈ d.bucket := hMarked
  let md := d.marker_data (Frame.ref child) hm
  have hCurrent : md.current = F.cell child := Option.some.inj
    (md.current_at.symm.trans hChildRead)
  obtain ⟨hc, hSourceEq⟩ := Array.getElem?_eq_some_iff.mp hSource
  have hSteps : ColumnSteps p.reduced child.1.val d.sources :=
    hSourceEq ▸ build_steps p.reduced_build child.1.val hc
  obtain ⟨_, sourceRef, _, _, hFound, _, _, _, hStored⟩ :=
    hSteps child.2.val md.current md.upper md.current_at md.upper_at hReal
  have hFoundActual : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent) :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mpr hParent
  have hFoundRef : sourceRef = Frame.ref parent := Except.ok.inj (hFound.symm.trans hFoundActual)
  have hSourceParent : md.sourceParent = Frame.ref parent :=
    (Option.some.inj (md.upper_left.symm.trans hStored)).trans hFoundRef
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  have hReadQuery := read.marked_reference hMarked
  have hReadRow : read.outputCell.row = md.targetCell.row := Except.ok.inj
    (hReadQuery.symm.trans (by simpa only [hCurrent] using md.reference))
  obtain ⟨hUpper, hRoot⟩ := d.prepared_real_marker_successor hSource hm hReal
  obtain ⟨upper, hUpperRead, _, hLeft⟩ := d.effective_marker_upper hParentPower hParentLow
    hNoPremature hRun hm hUpper hRoot read.output_at hReadRow
  have hReference : referenceAt ambient references (F.height child) = .ok rootRead.target.row := by
    have hRef := (s.referenceAt_preserved (F.height parent)).trans rootRead.start_query
    simpa only [hSourceRow] using hRef
  have hOutputRow : read.outputCell.row = rootRead.target.row :=
    Except.ok.inj (hReadQuery.symm.trans hReference)
  have hTargetRead : Canonical.cellAt ambient ⟨md.sourceParent.column +
      block * (p.reduced.size - 1 - p.root.column), md.targetIndex⟩ = .ok md.targetCell :=
    cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, md.target_at⟩
  have hColumn : md.sourceParent.column + block * (p.reduced.size - 1 - p.root.column) =
      rootRead.reference.column := by
    rw [hSourceParent, rootRead.reference_column]
    change parent.1.val + block * (p.reduced.size - 1 - p.root.column) = start.size - 1
    rw [hRootColumn]
    exact s.boundary_copy_index
  have hSelected : (⟨md.sourceParent.column + block * (p.reduced.size - 1 - p.root.column),
      md.targetIndex⟩ : Ref) = rootRead.reference := root_refs_equal s.ambient_valid
    hTargetRead rootRead.result_read hColumn (hReadRow.symm.trans hOutputRow)
  have hLeft' : upper.left = some rootRead.reference := by
    change upper.left = some (⟨md.sourceParent.column +
      block * (p.reduced.size - 1 - p.root.column), md.targetIndex⟩ : Ref) at hLeft
    exact hLeft.trans (congrArg some hSelected)
  let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  have hRootFinal : Canonical.cellAt (ambient.push column) rootRead.reference = .ok rootRead.target := by
    obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp rootRead.result_read
    exact cellAt_ok_iff.mpr ⟨nodes, (PreservesColumns.push ambient column).column_read hNodes, hRead⟩
  let rootCopy : EffectiveRootReference p start references parent (ambient.push column) :=
    { rootRead with result_read := hRootFinal }
  refine ⟨childCopy, rootCopy, rfl, rfl, hOutputRow, read.outputCell, upper,
    rootRead.target, read.output_read, ?_, hLeft', hRootFinal⟩
  exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
    EffectiveCopyRead.outputRef], hUpperRead⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_marker_root_reference
#print axioms OmegaY.Expansion.DynamicBlockState.actual_marker_effective_root_parent
