/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighNodeOrigin.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighSourceRecognition
import OmegaY.Expansion.ExecutedBlockPrefix
import OmegaY.Expansion.FinalCopyIndices
import OmegaY.Expansion.FinalSourceRecognition

/-!
# Inverting actual surviving high nodes

A final column coordinate determines an executed block and source column.
Only the prefix ending at this particular copied column is transported
through the final pop. High-row support and strict row uniqueness then
identify the given target node with a genuine effective source occurrence.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem copied_column_coordinates {root size column : Nat}
    (hWidth : root + 1 < size) (hColumn : size ≤ column) :
    ∃ block source, 0 < block ∧ root < source ∧ source < size ∧
      source + block * (size - 1 - root) = column := by
  let width := size - 1 - root
  let distance := column - (root + 1)
  have hw : 0 < width := by dsimp [width]; omega
  have hd : width ≤ distance := by dsimp [width, distance]; omega
  have hmod := Nat.mod_lt distance hw
  have hdiv := Nat.div_pos hd hw
  have he := Nat.mod_add_div distance width
  have hSize : size = root + 1 + width := by dsimp [width]; omega
  have hDistance : column = root + 1 + distance := by dsimp [distance]; omega
  refine ⟨distance / width, root + 1 + distance % width, hdiv, by omega, ?_, ?_⟩
  · omega
  · change root + 1 + distance % width + distance / width * width = column
    rw [Nat.mul_comm (distance / width) width]
    omega

/-- A true execution prefix that contains the selected copied node,
including its own earlier history and the actual outer run at its start. -/
structure HighCopiedNodeOrigin {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (node : (Frame.ofMountain result).Node) where
  block : Nat
  block_pos : 0 < block
  start : Mountain
  references : List Ref
  before : Mountain
  next : Nat
  state : DynamicBlockState p block start references next before
  history : CopyRunHistory p block start references next before
  preserved : PreservesColumns before result
  start_run : (forIn (List.range (block - 1)) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start
  source : (Frame.ofMountain p.reduced).Node
  copy : EffectiveCopyOccurrence p block start references source result
  source_before : source.1.val < next
  source_high : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source
  target_ref : Frame.ref node = copy.outputRef

/-- No source node, block number, intermediate run, or occurrence is an
input. All are recovered from the final successful output and its node. -/
theorem Preparation.high_copied_node_origin
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {node : (Frame.ofMountain result).Node}
    (hColumn : p.reduced.size ≤ node.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain result).height node) :
    Nonempty (HighCopiedNodeOrigin p result node) := by
  have hLegal := build_success_legal p.initial_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hSourceSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSourceSize
  have hWidth : p.root.column + 1 < p.reduced.size := by
    have := p.root_before_last
    omega
  obtain ⟨block, sourceColumn, hBlockPos, hRight, hSourceBound, hCoordinate⟩ :=
    copied_column_coordinates hWidth hColumn
  have hBlock := p.block_le_of_final_column hLast hCopies hRun hRight
    (hCoordinate ▸ node.1.isLt)
  obtain ⟨full, hFull, _⟩ := p.blocks_total hLast copies
  have hPop : full.pop = result := Except.ok.inj
    ((p.expandDiagram_of_blocks hLast hCopies hFull).symm.trans hRun)
  obtain ⟨packet⟩ := p.blocks_executed_prefix hLast hFull hBlockPos hBlock
  obtain ⟨before, column, state, history, hCopy, hCompleted, _⟩ :=
    packet.history.column_with_history hRight hSourceBound
  have hBeforeSize : before.size = node.1.val := state.size_eq.trans hCoordinate
  have hPreservedFull : PreservesColumns (before.push column) full :=
    hCompleted.trans packet.preserved
  have hSurvives : (before.push column).size ≤ full.size - 1 := by
    have hn := node.1.isLt
    change node.1.val < result.size at hn
    have hSizePop := congrArg Array.size hPop
    simp only [Array.size_pop] at hSizePop
    simp only [Array.size_push, hBeforeSize]
    omega
  have hPreserved : PreservesColumns (before.push column) result :=
    hPop ▸ hPreservedFull.pop_of_size hSurvives
  obtain ⟨actual, hActual, _, _, _, _, afterState, _⟩ := state.copy_next hLast hSourceBound
  have heColumn : actual = column := Except.ok.inj (hActual.symm.trans hCopy)
  subst actual
  have afterHistory := history.push state hCopy
  have hColumnRead : result[node.1.val]? = some column := by
    rw [← hBeforeSize]
    exact hPreserved.column_read (by simp)
  obtain ⟨nodes, hNodes, hTargetRead⟩ := cellAt_ok_iff.mp (cellAt_of_frame_node result node)
  have heNodes : nodes = column := Option.some.inj (hNodes.symm.trans hColumnRead)
  subst nodes
  obtain ⟨d, _, _, _⟩ := state.column_data hLast hSourceBound
  obtain ⟨sourceIndex, sourceCell, hSourceRead, hSourceRow⟩ :=
    d.copyColumn_high_read_to_source (state.marker_caps_below_lastTop hLast d hSourceBound)
      hCopy hTargetRead hHigh
  have hFrozen : p.reduced[sourceColumn]? = some d.sources :=
    (state.base_ambient sourceColumn hSourceBound).symm.trans d.source_column
  have hSourceAt : cellAt p.reduced ⟨sourceColumn, sourceIndex⟩ = .ok sourceCell :=
    cellAt_ok_iff.mpr ⟨d.sources, hFrozen, hSourceRead⟩
  obtain ⟨source, hSourceRef, hSourceCell⟩ := Canonical.frame_node_of_cellAt hSourceAt
  have hSourceColumn : source.1.val = sourceColumn := congrArg Ref.column hSourceRef
  have hSourceHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source := by
    change p.lastTop.row ≤ ((Frame.ofMountain p.reduced).cell source).row
    rw [hSourceCell, hSourceRow]
    exact hHigh
  have hSourceBefore : source.1.val < sourceColumn + 1 := by omega
  obtain ⟨oldCopy⟩ := afterState.prior_effective_occurrence afterHistory hLast
    (by omega : p.root.column < source.1.val) hSourceBefore
  let copy := oldCopy.extend hPreserved
  obtain ⟨actualNode, hActualRef, hActualCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
  have hSameColumn : actualNode.1 = node.1 := by
    apply Fin.ext
    have hc := (congrArg Ref.column hActualRef).trans copy.source_column
    change actualNode.1.val = source.1.val + block * (p.reduced.size - 1 - p.root.column) at hc
    rw [hc, hSourceColumn, hCoordinate]
  have hSameHeight : (Frame.ofMountain result).height actualNode =
      (Frame.ofMountain result).height node := by
    change ((Frame.ofMountain result).cell actualNode).row = _
    rw [hActualCell, copy.high_row hLast hSourceHigh]
    change ((Frame.ofMountain p.reduced).cell source).row = _
    rw [hSourceCell]
    exact hSourceRow
  have hSameNode := Frame.node_eq_of_column_height hValid.toOrdered hSameColumn hSameHeight
  exact ⟨{
    block := block
    block_pos := hBlockPos
    start := packet.start
    references := packet.references
    before := before.push column
    next := sourceColumn + 1
    state := afterState
    history := afterHistory
    preserved := hPreserved
    start_run := packet.start_run
    source := source
    copy := copy
    source_before := hSourceBefore
    source_high := hSourceHigh
    target_ref := hSameNode ▸ hActualRef }⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.high_copied_node_origin
