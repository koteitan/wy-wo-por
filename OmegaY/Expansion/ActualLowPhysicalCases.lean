/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowPhysicalCases.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowOriginReduction
import OmegaY.Expansion.ActualNonmarkerDirectRecognition

/-!
# Parent existence and direct recognition for every physical marker

Real marked source nodes have a nonempty same-row path to the root
column. Thus they have a parent, which cannot lie in the fixed good part.
For direct source hits, the actual copied upper and actual Q have the
same translated parent column, including the root-boundary column.
Raw frontier geometry and positive backfill then prove numerical
recognition, without any low depth-word comparison or search induction.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem Preparation.real_marker_parent
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {source : (Frame.ofMountain p.reduced).Node} (hReal : Real source)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source)) :
    ∃ parent, (Frame.ofMountain p.reduced).P source = some parent ∧
      p.root.column ≤ parent.1.val ∧
      (Frame.ofMountain p.reduced).height source = (Frame.ofMountain p.reduced).height parent := by
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hRight, low, _, hColumn, _, path, _⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mp hMarked
  cases path with
  | refl =>
      have he := congrArg Fin.val hColumn
      omega
  | @cons source parent low hParent tail =>
      obtain ⟨hBound, hRow⟩ := build_marked_parent_bounds p.reduced_build hMarkers hParent hMarked
      exact ⟨parent, hParent, (congrArg Ref.column hRootRef).symm.trans_le hBound, hRow⟩

namespace PhysicalMarkerRead

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  {copy : EffectiveCopyOccurrence p block start references source result}
  (physical : PhysicalMarkerRead copy)

/-- The physical upper's stored parent is read from the actual translated
source-parent column, with no strict-right restriction on that parent. -/
theorem raw_parent_column_all (hLast : 1 < last)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent) :
    ∃ reference, RawRefEdge result physical.outputRef reference ∧
      reference.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  let md := d.marker_data (Frame.ref source) hMarked
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hCurrent : md.current = F.cell source := Option.some.inj
    (md.current_at.symm.trans copy.read.source_at)
  obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hParent
  have hUpperAt : d.sources[source.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSources (congrArg Fin.val (Frame.upper_spec hSourceUpper).1)
    simpa only [(Frame.upper_spec hSourceUpper).2] using hRead
  have hUpperCell : md.upper = F.cell sourceUpper := Option.some.inj (md.upper_at.symm.trans hUpperAt)
  obtain ⟨actualParent, hActualParent, hB, _, hStored⟩ := hNormal.upper_step source sourceUpper hReal hSourceUpper
  have he : actualParent = parent := Option.some.inj (hActualParent.symm.trans hParent)
  subst actualParent
  have hSourceParent : md.sourceParent = Frame.ref parent := Option.some.inj
    (md.upper_left.symm.trans (by simpa only [hUpperCell] using hStored))
  obtain ⟨actual, hActual, hParentBound, hSameRows⟩ := p.real_marker_parent hReal hMarked
  have he : actual = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actual
  change F.height source = F.height parent at hSameRows
  have hSourceUpperRow : md.upper.row = Row.bump md.current.row 0 := by
    rw [hUpperCell, hCurrent]
    change F.height sourceUpper = Row.bump (F.height source) 0
    change F.height sourceUpper = Row.B (F.height source) (F.height parent) at hB
    simpa only [← hSameRows, Row.B_self] using hB
  have hRoot : p.root.column ≤ md.sourceParent.column := by
    rw [hSourceParent]
    exact hParentBound
  obtain ⟨hNoPremature, hPP, hPL⟩ := copy.state.column_data_parent_inputs hLast source.1.isLt d
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hPL (Frame.ref source) hMarked
  have hPhysicalRow : physical.cell.row = md.current.row :=
    physical.source_row.trans (congrArg Cell.row hCurrent).symm
  obtain ⟨upper, hUpperRead, _, hUpperLeft⟩ := d.physical_marker_upper
    hPP hPL hNoPremature copy.read.copy_run hMarked hSourceUpperRow hRoot hLow hLowRow
    physical.output_at hPhysicalRow
  let lowRef : Ref := ⟨md.sourceParent.column + block * (p.reduced.size - 1 - p.root.column), lowIndex⟩
  have hLowRead : Canonical.cellAt copy.before lowRef = .ok lowCell :=
    cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, hLow⟩
  have hLowBound : lowRef.column < copy.before.size := (Array.getElem?_eq_some_iff.mp md.parent_nodes).1
  have hPreserve : PreservesColumns copy.before result :=
    (PreservesColumns.push copy.before copy.column).trans copy.preserved
  have hLowResult : Canonical.cellAt result lowRef = .ok lowCell := (hPreserve.cellAt hLowBound).trans hLowRead
  have hActualUpper : Canonical.cellAt result
      ⟨physical.outputRef.column, physical.outputRef.index + 1⟩ = .ok upper := by
    exact (copy.preserved.cellAt
      (ref := ⟨physical.outputRef.column, physical.outputRef.index + 1⟩)
      (by simp [outputRef])).trans
      (cellAt_ok_iff.mpr ⟨copy.column, by simp [outputRef], hUpperRead⟩)
  refine ⟨lowRef, ⟨physical.cell, upper, lowCell, physical.output_read,
    hActualUpper, hUpperLeft, hLowResult⟩, ?_⟩
  change md.sourceParent.column + _ = _
  rw [hSourceParent]
  rfl

/-- Source Q=P is recognized at every physical marker height and for all
source-parent columns. The root-column case uses actual endpoint geometry,
not an assumed boundary-value equality. -/
theorem recognize_direct_all (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hDirect : (Frame.ofMountain p.reduced).Q source = some parent)
    {node : (Frame.ofMountain result).Node} (hRef : Frame.ref node = physical.outputRef) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  have hLegal := build_success_legal p.initial_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨actual, hActual, hBound, _⟩ := p.real_marker_parent hReal hMarked
  have he : actual = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actual
  obtain ⟨current, candidate, hCurrentRef, _, hQ, _, hCandidateColumn, _⟩ :=
    physical.candidate_frontier hValid hMarked hReal hDirect hBound
  have hCurrent : current = node := Executable.ref_injective _ (hCurrentRef.trans hRef.symm)
  subst current
  obtain ⟨reference, hEdge, hColumn⟩ := physical.raw_parent_column_all hLast hMarked hParent
  have hEdgeCopy := hEdge
  obtain ⟨_, _, parentCell, _, _, _, hRead⟩ := hEdgeCopy
  obtain ⟨father, hFatherRef, _⟩ := Canonical.frame_node_of_cellAt hRead
  have hRaw := hEdge.rawParent hRef hFatherRef
  have hNodeReal := physical.frame_real hReal hRef
  have hSame := Frame.Q_eq_rawParent_of_column hValid.toOrdered
    (OmegaY.Expansion.expandDiagram_raw_geometry hLegal hRun).rawRowGeometry
    (OmegaY.Expansion.expandDiagram_raw_father_upper_bound hLegal hRun)
    hNodeReal hQ hRaw (Fin.ext (hCandidateColumn.trans
      ((congrArg Ref.column hFatherRef).trans hColumn).symm))
  subst candidate
  have hP := (OmegaY.Expansion.expandDiagram_equations hLegal hRun).1.P_of_Q_rawParent
    hValid hNodeReal hQ hRaw
  exact hRaw.trans hP.symm

end PhysicalMarkerRead
end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.real_marker_parent
#print axioms OmegaY.Expansion.PhysicalMarkerRead.raw_parent_column_all
#print axioms OmegaY.Expansion.PhysicalMarkerRead.recognize_direct_all
