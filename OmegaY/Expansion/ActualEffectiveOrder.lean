/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveOrder.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveCopy

/-!
# Strict order of actual effective copies within one source column

Equal controlling markers use strict monotonicity of one lift. Distinct
controlling markers put the lower source strictly before the higher marker;
the actual reference cap makes the lower lift fix that marker's row. Thus
effective output rows are strictly ordered across segments as well as
inside them. Markers, their effective targets, and phantom index zero are
all included. No cross-column event sampling is asserted.
-/

namespace OmegaY.Expansion

open Canonical

namespace EffectiveCopyRead

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
  {column : Column} {i j : Nat} {lowerSource upperSource : Cell}
  (lower : EffectiveCopyRead d i lowerSource column)
  (upper : EffectiveCopyRead d j upperSource column)

/-- Maximal preceding marker indices are monotone in actual source index. -/
theorem marker_index_le (hOrder : i ≤ j) : lower.marker.index ≤ upper.marker.index := by
  by_contra hn
  exact upper.no_between lower.marker.index (Nat.lt_of_not_ge hn)
    (lower.marker_before.trans hOrder) (List.mem_map.mpr ⟨lower.marker, lower.marker_mem, rfl⟩)

/-- Arbitrary strict source-index order gives strict effective-row order.
No extra parent-support or output-order assumption is supplied by the caller. -/
theorem output_row_lt (hOrder : i < j) : lower.outputCell.row < upper.outputCell.row := by
  have hMarker := lower.marker_index_le upper hOrder.le
  let lm := d.marker_data lower.marker lower.marker_mem
  let um := d.marker_data upper.marker upper.marker_mem
  rcases eq_or_lt_of_le hMarker with hSame | hBefore
  · have hCurrent : lm.current = um.current := Option.some.inj
      (lm.current_at.symm.trans (by simpa only [hSame] using um.current_at))
    have hTarget : lm.targetCell.row = um.targetCell.row := by
      have hReference := lm.reference
      rw [hCurrent] at hReference
      exact Except.ok.inj (hReference.symm.trans um.reference)
    have hSourceOrder : lowerSource.row < upperSource.row :=
      d.source_valid.rows_strict i j lowerSource upperSource lower.source_at upper.source_at hOrder
    rw [lower.output_row, upper.output_row]
    change Row.lift lm.current.row lm.targetCell.row lowerSource.row <
      Row.lift um.current.row um.targetCell.row upperSource.row
    rw [← hCurrent, ← hTarget]
    exact Row.lift_strictMono lower.source_lower hSourceOrder
  · have hBeforeMarker : i < upper.marker.index := by
      by_contra hn
      exact lower.no_between upper.marker.index hBefore (Nat.le_of_not_gt hn)
        (List.mem_map.mpr ⟨upper.marker, upper.marker_mem, rfl⟩)
    have hSourceBelow : lowerSource.row < um.current.row :=
      d.source_valid.rows_strict i upper.marker.index lowerSource um.current
        lower.source_at um.current_at hBeforeMarker
    obtain ⟨degree, hTarget, hCap⟩ :=
      d.reference_caps lower.marker lower.marker_mem upper.marker upper.marker_mem hBefore
    have hFixed : Row.lift lm.current.row lm.targetCell.row um.current.row = um.current.row :=
      Row.lift_eq_of_ge_cap lm.target_lower hTarget hCap
    have hLowerBelow : lower.outputCell.row < um.current.row := by
      rw [lower.output_row, ← hFixed]
      exact Row.lift_strictMono lower.source_lower hSourceBelow
    exact hLowerBelow.trans_le (upper.source_lower.trans upper.source_row_le_output)

/-- The actual finisher's strict rows turn the row inequality into strict
fresh output-array index order; no desired output adjacency is assumed. -/
theorem output_index_lt (hOrder : i < j) : lower.outputIndex < upper.outputIndex := by
  have hRows := lower.output_row_lt upper hOrder
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans lower.copy_run)
  subst actual
  by_contra hn
  rcases eq_or_lt_of_le (Nat.le_of_not_gt hn) with hEq | hLt
  · have hCells : upper.outputCell = lower.outputCell := Option.some.inj
      (upper.output_at.symm.trans (by simpa only [hEq] using lower.output_at))
    rw [hCells] at hRows
    exact (lt_irrefl _) hRows
  · exact (not_lt_of_gt hRows) (hValid.rows_strict _ _ _ _ upper.output_at lower.output_at hLt)

/-- The requested neighbouring-source case, including a marker or phantom
lower and a possibly marked upper, is a specialization of the full result. -/
theorem adjacent_output_order
    (lower : EffectiveCopyRead d i lowerSource column)
    (upper : EffectiveCopyRead d (i + 1) upperSource column) :
    lower.outputCell.row < upper.outputCell.row ∧ lower.outputIndex < upper.outputIndex :=
  ⟨lower.output_row_lt upper (Nat.lt_succ_self i), lower.output_index_lt upper (Nat.lt_succ_self i)⟩

/-- Phantom source index zero has precisely the output phantom index zero,
even though effective occurrences of real markers can finish above their
physical copies. This is derived from the actual zero reference query. -/
theorem output_index_zero (read : EffectiveCopyRead d 0 lowerSource column) : read.outputIndex = 0 := by
  have hMarker : read.marker.index = 0 := Nat.le_zero.mp read.marker_before
  have hSource : lowerSource = phantom := Option.some.inj (read.source_at.symm.trans d.source_valid.phantom)
  let md := d.marker_data read.marker read.marker_mem
  have hCurrent : md.current = phantom := Option.some.inj
    (md.current_at.symm.trans (by simpa only [hMarker] using d.source_valid.phantom))
  have hCurrentRow : md.current.row = 0 := congrArg Cell.row hCurrent
  have hTarget : md.targetCell.row = 0 := d.target_zero read.marker_mem hCurrentRow
  have hRow : read.outputCell.row = 0 := by
    rw [read.output_row]
    change Row.lift md.current.row md.targetCell.row lowerSource.row = 0
    rw [hCurrentRow, hTarget, hSource]
    exact Row.lift_at_root 0 0
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans read.copy_run)
  subst actual
  by_contra hn
  have hPositive := hValid.rows_strict 0 read.outputIndex phantom read.outputCell
    hValid.phantom read.output_at (by omega)
  change (0 : Row) < read.outputCell.row at hPositive
  rw [hRow] at hPositive
  exact (lt_irrefl (0 : Row)) hPositive

end EffectiveCopyRead

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- One actual source column embeds, in strict order, into its real copied
column via effective occurrences. The finite embedding is constructed from
executed reads and therefore includes every source node, including phantom.
This does not choose or align event indices between different columns. -/
theorem exists_effectiveIndexEmbedding
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    ∃ embedding : Fin d.sources.size ↪o Fin column.size,
      ∀ i : Fin d.sources.size, ∃ read : EffectiveCopyRead d i.val d.sources[i] column,
        (embedding i).val = read.outputIndex := by
  classical
  let reads : (i : Fin d.sources.size) → EffectiveCopyRead d i.val d.sources[i] column :=
    fun i => Classical.choice (d.effective_copy_read hParentPower hParentLow hNoPremature hRun
      (Array.getElem?_eq_getElem i.isLt))
  let indexMap : Fin d.sources.size → Fin column.size := fun i =>
    ⟨(reads i).outputIndex, (Array.getElem?_eq_some_iff.mp (reads i).output_at).1⟩
  have hStrict : StrictMono indexMap := by
    intro i j hij
    exact (reads i).output_index_lt (reads j) hij
  exact ⟨OrderEmbedding.ofStrictMono indexMap hStrict, fun i => ⟨reads i, rfl⟩⟩

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyRead.marker_index_le
#print axioms OmegaY.Expansion.EffectiveCopyRead.output_row_lt
#print axioms OmegaY.Expansion.EffectiveCopyRead.output_index_lt
#print axioms OmegaY.Expansion.EffectiveCopyRead.adjacent_output_order
#print axioms OmegaY.Expansion.EffectiveCopyRead.output_index_zero
#print axioms OmegaY.Expansion.ColumnCopyData.exists_effectiveIndexEmbedding
