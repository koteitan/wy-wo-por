/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedNodeOrigin.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CopyCellOrigin
import OmegaY.Expansion.ExecutedBlockPrefix
import OmegaY.Expansion.FinalCopyIndices

/-!
# Complete provenance of surviving copied nodes

Every actual final node outside the complete reduced prefix is located in
one real earlier block and one real column execution. The original source
column, current reference map, input data, history, all output indices and
preservation through the final pop are derived from that execution.
There is no row threshold or numerical-parent hypothesis in this result.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem column_coordinates {root size column : Nat}
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
  refine ⟨distance / width, root + 1 + distance % width, hdiv, by omega, by omega, ?_⟩
  change root + 1 + distance % width + distance / width * width = column
  rw [Nat.mul_comm (distance / width) width]
  omega

/-- A derived certificate of the real column execution containing this
particular final node. The node origin is an output field, not an input
assumed about the executable copying process. -/
structure CopiedNodeOrigin {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (node : (Frame.ofMountain result).Node) where
  block : Nat
  block_pos : 0 < block
  start : Mountain
  references : List Ref
  before : Mountain
  column : Column
  sourceColumn : Nat
  source_right : p.root.column < sourceColumn
  source_bound : sourceColumn < p.reduced.size
  state : DynamicBlockState p block start references sourceColumn before
  history : CopyRunHistory p block start references sourceColumn before
  after_state : DynamicBlockState p block start references (sourceColumn + 1) (before.push column)
  after_history : CopyRunHistory p block start references (sourceColumn + 1) (before.push column)
  preserved : PreservesColumns (before.push column) result
  start_run : (forIn (List.range (block - 1)) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start
  data : ColumnCopyData before p.marked references sourceColumn
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column
  source_read : p.reduced[sourceColumn]? = some data.sources
  copy_run : copyColumn before p.marked references sourceColumn
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column
  target_column : before.size = node.1.val
  column_read : result[node.1.val]? = some column
  node_read : column[node.2.val]? = some ((Frame.ofMountain result).cell node)
  origin : CopiedCellOrigin data column node.2.val ((Frame.ofMountain result).cell node)

/-- The complete origin of any surviving new copied cell, including all
low nodes and actual fill cells. Neither an intermediate execution nor a
node classification is given as a premise. -/
theorem Preparation.copied_node_origin
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {node : (Frame.ofMountain result).Node}
    (hColumn : p.reduced.size ≤ node.1.val) :
    Nonempty (CopiedNodeOrigin p result node) := by
  have hSourceSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSourceSize
  have hWidth : p.root.column + 1 < p.reduced.size := by
    have := p.root_before_last
    omega
  obtain ⟨block, sourceColumn, hBlockPos, hRight, hSourceBound, hCoordinate⟩ :=
    column_coordinates hWidth hColumn
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
  obtain ⟨nodes, hNodes, hTargetRead⟩ := cellAt_ok_iff.mp (Canonical.cellAt_of_frame_node result node)
  have heNodes : nodes = column := Option.some.inj (hNodes.symm.trans hColumnRead)
  subst nodes
  obtain ⟨d, _, _, _⟩ := state.column_data hLast hSourceBound
  have hFrozen : p.reduced[sourceColumn]? = some d.sources :=
    (state.base_ambient sourceColumn hSourceBound).symm.trans d.source_column
  obtain ⟨origin⟩ := d.copyColumn_cell_origin hCopy hTargetRead
  exact ⟨{
    block := block
    block_pos := hBlockPos
    start := packet.start
    references := packet.references
    before := before
    column := column
    sourceColumn := sourceColumn
    source_right := hRight
    source_bound := hSourceBound
    state := state
    history := history
    after_state := afterState
    after_history := afterHistory
    preserved := hPreserved
    start_run := packet.start_run
    data := d
    source_read := hFrozen
    copy_run := hCopy
    target_column := hBeforeSize
    column_read := hColumnRead
    node_read := hTargetRead
    origin := origin }⟩

/-- Exhaustive original-prefix / actual-copy provenance, with no row or
realness restriction. Real low nodes use exactly the same actual indices. -/
theorem Preparation.node_origin
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (node : (Frame.ofMountain result).Node) :
    node.1.val < p.reduced.size ∨ Nonempty (CopiedNodeOrigin p result node) := by
  by_cases hOld : node.1.val < p.reduced.size
  · exact Or.inl hOld
  · exact Or.inr (p.copied_node_origin hLast hCopies hRun (by omega))

/-- The effective constructor's concrete source-array read supplies a
typed source and a genuine final occurrence. Its output reference is the
caller's original target reference, with no same-row matching premise. -/
theorem CopiedNodeOrigin.effective_occurrence
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    {sourceIndex : Nat} {sourceCell : Cell}
    (read : EffectiveCopyRead packet.data sourceIndex sourceCell packet.column)
    (hIndex : read.outputIndex = node.2.val)
    (hCell : read.outputCell = (Frame.ofMountain result).cell node) :
    ∃ (source : (Frame.ofMountain p.reduced).Node)
      (copy : EffectiveCopyOccurrence p packet.block packet.start packet.references source result),
      source.1.val = packet.sourceColumn ∧ source.2.val = sourceIndex ∧
      (Frame.ofMountain p.reduced).cell source = sourceCell ∧
      Frame.ref node = copy.outputRef ∧ copy.read.outputCell = (Frame.ofMountain result).cell node := by
  let sourceColumn : Fin (Frame.ofMountain p.reduced).width :=
    ⟨packet.sourceColumn, packet.source_bound⟩
  have hLength : (Frame.ofMountain p.reduced).length sourceColumn = packet.data.sources.size :=
    congrArg Array.size (Array.getElem?_eq_some_iff.mp packet.source_read).2
  have hi : sourceIndex < (Frame.ofMountain p.reduced).length sourceColumn := by
    rw [hLength]
    exact (Array.getElem?_eq_some_iff.mp read.source_at).1
  let source : (Frame.ofMountain p.reduced).Node := ⟨sourceColumn, ⟨sourceIndex, hi⟩⟩
  have hSourceRead : Canonical.cellAt p.reduced (Frame.ref source) = .ok sourceCell :=
    cellAt_ok_iff.mpr ⟨packet.data.sources, packet.source_read, read.source_at⟩
  have hSourceCell : (Frame.ofMountain p.reduced).cell source = sourceCell :=
    Except.ok.inj ((Canonical.cellAt_of_frame_node p.reduced source).symm.trans hSourceRead)
  subst sourceCell
  let copy : EffectiveCopyOccurrence p packet.block packet.start packet.references source result := {
    before := packet.before
    column := packet.column
    state := packet.state
    data := packet.data
    read := read
    preserved := packet.preserved }
  refine ⟨source, copy, rfl, rfl, rfl, ?_, hCell⟩
  change (⟨node.1.val, node.2.val⟩ : Ref) = ⟨packet.before.size, read.outputIndex⟩
  exact congrArg₂ Ref.mk packet.target_column.symm hIndex.symm

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.copied_node_origin
#print axioms OmegaY.Expansion.Preparation.node_origin
#print axioms OmegaY.Expansion.CopiedNodeOrigin.effective_occurrence
