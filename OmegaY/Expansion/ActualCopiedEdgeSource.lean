/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedEdgeSource.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ColumnEdgeSourceClassification
import OmegaY.Expansion.ActualCopiedNodeOrigin
import OmegaY.Expansion.ActualEffectiveEdgeKeys

/-! Every surviving actual copied edge has either a genuine effective
source edge with the same lower reference, or a genuine fill execution.
All input-side copy data and source-realness are derived internally. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem EffectiveAdjacentSource.source_index_pos
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {column : Column} {index : Nat} {lower : Cell}
    (source : EffectiveAdjacentSource d column index lower) (hNonzero : lower.row ≠ 0) :
    0 < source.sourceIndex := by
  by_contra hn
  have hZero : source.sourceIndex = 0 := by omega
  have hMarkerZero : source.read.marker.index = 0 := by have := source.read.marker_before; omega
  let md := d.marker_data source.read.marker source.read.marker_mem
  have hSourceAt : d.sources[0]? = some source.sourceLower := by
    simpa only [hZero] using source.read.source_at
  have hCurrentAt : d.sources[0]? = some md.current := by
    simpa only [hMarkerZero] using md.current_at
  have hSource : source.sourceLower = phantom := Option.some.inj
    (hSourceAt.symm.trans d.source_valid.phantom)
  have hCurrent : md.current = phantom := Option.some.inj
    (hCurrentAt.symm.trans d.source_valid.phantom)
  have hCurrentRow : md.current.row = 0 := by rw [hCurrent]; rfl
  have hSourceRow : source.sourceLower.row = 0 := by rw [hSource]; rfl
  have hTarget := d.target_zero source.read.marker_mem hCurrentRow
  have hRow := source.read.output_row
  rw [source.output_cell] at hRow
  change lower.row = Row.lift md.current.row md.targetCell.row source.sourceLower.row at hRow
  rw [hCurrentRow, hTarget, hSourceRow, Row.lift_at_root] at hRow
  exact hNonzero hRow

theorem CopiedNodeOrigin.effective_adjacent_source
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    (edge : RealStoredEdge (Frame.ofMountain result))
    (packet : CopiedNodeOrigin p result edge.upper)
    (hOrdered : (Frame.ofMountain result).Ordered)
    (certificate : EffectiveAdjacentSource packet.data packet.column edge.lower.2.val
      ((Frame.ofMountain result).cell edge.lower)) :
    ∃ (source : RealStoredEdge (Frame.ofMountain p.reduced))
      (copy : EffectiveCopyOccurrence p packet.block packet.start packet.references source.lower
        (packet.before.push packet.column)),
      source.lower.1.val = packet.sourceColumn ∧
      Frame.ref edge.lower = (copy.extend packet.preserved).outputRef := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNonzero : (G.cell edge.lower).row ≠ 0 := by
    intro hz
    have h := one_le_height hOrdered edge.lower_real
    change (1 : Row) ≤ (G.cell edge.lower).row at h
    rw [hz] at h
    exact (not_le_of_gt (by decide : (0 : Row) < 1)) h
  have hRealIndex := certificate.source_index_pos hNonzero
  let column : Fin F.width := ⟨packet.sourceColumn, packet.source_bound⟩
  have hLength : F.length column = packet.data.sources.size :=
    congrArg Array.size (Array.getElem?_eq_some_iff.mp packet.source_read).2
  let sourceLower : F.Node := ⟨column, ⟨certificate.sourceIndex, by
    rw [hLength]
    exact (Array.getElem?_eq_some_iff.mp certificate.read.source_at).1⟩⟩
  let sourceUpper : F.Node := ⟨column, ⟨certificate.sourceIndex + 1, by
    rw [hLength]
    exact (Array.getElem?_eq_some_iff.mp certificate.upper_at).1⟩⟩
  have hLowerRead : Canonical.cellAt p.reduced (Frame.ref sourceLower) = .ok certificate.sourceLower :=
    cellAt_ok_iff.mpr ⟨packet.data.sources, packet.source_read, certificate.read.source_at⟩
  have hLowerCell : F.cell sourceLower = certificate.sourceLower := Except.ok.inj
    ((Canonical.cellAt_of_frame_node p.reduced sourceLower).symm.trans hLowerRead)
  have hUpper : F.upper sourceLower = some sourceUpper := Frame.upper_of_refs (by rfl) (by rfl)
  have hReal : Real sourceLower := hRealIndex
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨parent, hParent, _, _, _⟩ := hNormal.upper_step sourceLower sourceUpper hReal hUpper
  let source : RealStoredEdge F := {
    lower := sourceLower, upper := sourceUpper, parent := parent,
    lower_real := hReal, upper_eq := hUpper,
    parent_eq := (hNormal.rawParent_eq_P hReal).trans hParent }
  let copy : EffectiveCopyOccurrence p packet.block packet.start packet.references sourceLower
      (packet.before.push packet.column) := {
    before := packet.before, column := packet.column, state := packet.state,
    data := packet.data,
    read := {
      source_at := by
        change packet.data.sources[certificate.sourceIndex]? = some (F.cell sourceLower)
        rw [hLowerCell]
        exact certificate.read.source_at
      copy_run := certificate.read.copy_run
      marker := certificate.read.marker
      marker_mem := certificate.read.marker_mem
      marker_before := certificate.read.marker_before
      no_between := certificate.read.no_between
      source_lower := by
        change _ ≤ (F.cell sourceLower).row
        rw [hLowerCell]
        exact certificate.read.source_lower
      outputIndex := certificate.read.outputIndex
      outputCell := certificate.read.outputCell
      output_at := certificate.read.output_at
      output_row := by
        change _ = Row.lift _ _ (F.cell sourceLower).row
        rw [hLowerCell]
        exact certificate.read.output_row }
    preserved := fun _ _ => rfl }
  refine ⟨source, copy, rfl, ?_⟩
  have hColumn : packet.before.size = edge.lower.1.val :=
    packet.target_column.trans (congrArg Fin.val (upper_spec edge.upper_eq).1)
  change (⟨edge.lower.1.val, edge.lower.2.val⟩ : Ref) = ⟨packet.before.size, copy.read.outputIndex⟩
  exact congrArg₂ Ref.mk hColumn.symm certificate.output_index.symm

/-- This is the complete algorithm-to-key source classification. A fill
case retains its actual run and member, and an ordinary case retains the
actual source edge and its effective occurrence in a recorded block. -/
theorem Preparation.copied_edge_source_or_fill
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hColumn : p.reduced.size ≤ edge.lower.1.val) :
    (∃ (packet : CopiedNodeOrigin p result edge.upper)
      (source : RealStoredEdge (Frame.ofMountain p.reduced))
      (copy : EffectiveCopyOccurrence p packet.block packet.start packet.references source.lower
        (packet.before.push packet.column)),
      source.lower.1.val = packet.sourceColumn ∧
      Frame.ref edge.lower = (copy.extend packet.preserved).outputRef) ∨
    (∃ packet : CopiedNodeOrigin p result edge.upper,
      FillUpperOrigin packet.data ((Frame.ofMountain result).cell edge.upper)) := by
  have hUpperColumn := congrArg Fin.val (upper_spec edge.upper_eq).1
  obtain ⟨original⟩ := p.copied_node_origin hLast hCopies hRun (hColumn.trans_eq hUpperColumn.symm)
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := original.state.column_data hLast original.source_bound
  have hSource : p.reduced[original.sourceColumn]? = some d.sources :=
    (original.state.base_ambient original.sourceColumn original.source_bound).symm.trans d.source_column
  let packet : CopiedNodeOrigin p result edge.upper := { original with
    data := d
    source_read := hSource
    origin := Classical.choice (d.copyColumn_cell_origin original.copy_run original.node_read) }
  have hLowerAt : packet.column[edge.lower.2.val]? = some ((Frame.ofMountain result).cell edge.lower) := by
    obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp (Canonical.cellAt_of_frame_node result edge.lower)
    have hSame : nodes = packet.column := Option.some.inj (hNodes.symm.trans
      (by
        change result[edge.lower.1.val]? = some packet.column
        rw [← hUpperColumn]
        exact packet.column_read))
    exact hSame ▸ hRead
  have hUpperAt : packet.column[edge.lower.2.val + 1]? = some ((Frame.ofMountain result).cell edge.upper) := by
    rw [← (upper_spec edge.upper_eq).2]
    exact packet.node_read
  rcases d.adjacent_effective_or_fill hParentPower hParentLow hNoPremature
      packet.copy_run hLowerAt hUpperAt with hEffective | hFill
  · obtain ⟨certificate⟩ := hEffective
    obtain ⟨source, copy, hSourceColumn, hRef⟩ := packet.effective_adjacent_source edge
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered certificate
    exact Or.inl ⟨packet, source, copy, hSourceColumn, hRef⟩
  · exact Or.inr ⟨packet, hFill⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveAdjacentSource.source_index_pos
#print axioms OmegaY.Expansion.CopiedNodeOrigin.effective_adjacent_source
#print axioms OmegaY.Expansion.Preparation.copied_edge_source_or_fill
