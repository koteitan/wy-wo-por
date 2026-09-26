/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualIteratedHighestBoundary.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualParentlessHighestBoundary
import OmegaY.Expansion.BlocksTotal
import OmegaY.Expansion.LoopPrefix

/-!
# The actual highest selector after any finite number of blocks

The final real block and its column history are recovered from the unchanged
outer loop. No boundary-edge invariant is assumed of any intermediate block.
With zero blocks the selector is the actual decrement graft. If the original
bad root has a parent, the selector has one raw edge to that fixed original
parent. Otherwise the selector is a real value-one terminal.

The cut is the old terminal-top row Z. It need not itself occur as a row in
the reduced or copied mountain. These are actual stored-edge statements;
they do not identify the new numerical candidate chain or its blockers.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The actual outer run either has no block, or supplies a full real
history for its last block. The prefix and block are independently
constructed by the actual totality theorem and identified by determinism. -/
theorem Preparation.blocks_final_history_of_run
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    (copies = 0 ∧ result = p.reduced) ∨
      ∃ previous start references,
        copies = previous + 1 ∧
        (forIn (List.range previous) p.reduced (fun block mountain => do
          let next ← copyBlock mountain p.marked p.boundaries p.root.column
            (p.initial.size - 1 - p.root.column) (block + 1)
          pure (.yield next)) : Result Mountain) = .ok start ∧
        DynamicBlockState p (previous + 1) start references p.reduced.size result ∧
        CopyRunHistory p (previous + 1) start references p.reduced.size result := by
  cases copies with
  | zero =>
      have he : p.reduced = result := Except.ok.inj hRun
      exact Or.inl ⟨rfl, he.symm⟩
  | succ previous =>
      obtain ⟨start, hPrefix, ready⟩ := p.blocks_total hLast previous
      obtain ⟨actual, references, hCopy, _, _, state, history⟩ :=
        ready.copyBlock_with_history hLast
      have hSizes : p.initial.size = p.reduced.size := by
        have hInitial := build_size p.initial_build
        have hReduced := build_size p.reduced_build
        simp only [List.length_append, List.length_singleton] at hInitial hReduced
        exact hInitial.trans hReduced.symm
      have hStep : copyBlock start p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (previous + 1) = .ok actual := by
        simpa only [hSizes] using hCopy
      have hActual := forIn_yield_range_succ p.reduced
        (fun block mountain => copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)) hPrefix hStep
      have he : actual = result := Except.ok.inj (hActual.symm.trans hRun)
      subst actual
      exact Or.inr ⟨previous, start, references, rfl, hPrefix, state, history⟩

/-- The parent-present classification at the highest cut holds for
every actual finite outer run, including the initial zero-block graft. -/
theorem Preparation.blocks_highest_edge_of_run
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    (g : RootGeometry p) {parent : (Frame.ofMountain p.initial).Node}
    (hParent : (Frame.ofMountain p.initial).P g.rootNode = some parent) :
    parent.1.val < p.root.column ∧
    ∃ reference cell,
      below result (result.size - 1) p.lastTop.row = .ok reference ∧
      Canonical.cellAt result reference = .ok cell ∧ cell.row < p.lastTop.row ∧
      RawRefEdge result reference (Frame.ref parent) ∧
      Canonical.cellAt result (Frame.ref parent) = .ok ((Frame.ofMountain p.initial).cell parent) := by
  refine ⟨?_, ?_⟩
  · have hc := Frame.P_column_lt (build_normal_of_success p.initial_build).toOrdered hParent
    simpa only [show g.rootNode.1.val = p.root.column from congrArg Ref.column g.root_ref] using hc
  · rcases p.blocks_final_history_of_run hLast hRun with ⟨_, he⟩ |
      ⟨_, _, _, _, _, state, history⟩
    · subst result
      obtain ⟨source, hBelow, _, hEdge, hRead, _, hLow⟩ :=
        p.initial_badRoot_reference_edge hLast g hParent
      exact ⟨Frame.ref source, (Frame.ofMountain p.reduced).cell source,
        hBelow, cellAt_of_frame_node p.reduced source, hLow, hEdge, hRead⟩
    · obtain ⟨_, copy, _, _, hBelow, hEdge, hRead, hLow⟩ :=
        state.next_highest_boundary_edge history hLast g hParent
      exact ⟨copy.outputRef, copy.read.outputCell, hBelow, copy.output_read, hLow, hEdge, hRead⟩

/-- The parentless classification is a genuine terminal, not merely a
failed lookup. In particular its value is one and it has no upper node. -/
theorem Preparation.blocks_parentless_highest_of_run
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    (g : RootGeometry p) (hNone : (Frame.ofMountain p.initial).P g.rootNode = none) :
    ∃ terminal : (Frame.ofMountain result).Node,
      below result (result.size - 1) p.lastTop.row = .ok (Frame.ref terminal) ∧
      terminal.1.val = result.size - 1 ∧ Frame.Real terminal ∧
      (Frame.ofMountain result).value terminal = 1 ∧
      (Frame.ofMountain result).upper terminal = none ∧
      (Frame.ofMountain result).rawParent terminal = none ∧
      (Frame.ofMountain result).height terminal < p.lastTop.row := by
  rcases p.blocks_final_history_of_run hLast hRun with ⟨_, he⟩ |
    ⟨_, _, _, _, _, state, history⟩
  · subst result
    obtain ⟨source, _, hColumn, hBelow, hReal, hUpper, hOne, hLow⟩ :=
      p.initial_parentless_highest_source hLast g hNone
    exact ⟨source, hBelow, hColumn, hReal, hOne, hUpper,
      Frame.rawParent_none_of_upper_none hUpper, hLow⟩
  · obtain ⟨_, _, terminal, _, _, _, _, hBelow, hColumn, hReal, hOne, hUpper, hRaw, hLow⟩ :=
      state.next_parentless_highest_terminal history hLast g hNone
    exact ⟨terminal, hBelow, hColumn, hReal, hOne, hUpper, hRaw, hLow⟩

/-- An exhaustive classification using the actual original bad-root
search. The terminal case uses `toOption = none` because executable
`findParent` returns `Except BuildError Ref`, not `Option Ref`.
The source is genuinely canonical, so its typed-search equivalence
prevents a malformed-input error from being used as a terminal oracle. -/
theorem Preparation.blocks_highest_classification_of_run
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    ∃ reference cell,
      below result (result.size - 1) p.lastTop.row = .ok reference ∧
      Canonical.cellAt result reference = .ok cell ∧ cell.row < p.lastTop.row ∧
      ((∃ parent : (Frame.ofMountain p.initial).Node,
        Canonical.findParent p.initial p.root = .ok (Frame.ref parent) ∧
        parent.1.val < p.root.column ∧
        RawRefEdge result reference (Frame.ref parent) ∧
        Canonical.cellAt result (Frame.ref parent) = .ok ((Frame.ofMountain p.initial).cell parent)) ∨
       ((Canonical.findParent p.initial p.root).toOption = none ∧
        ∃ terminal : (Frame.ofMountain result).Node,
          Frame.ref terminal = reference ∧ terminal.1.val = result.size - 1 ∧
          Frame.Real terminal ∧ (Frame.ofMountain result).value terminal = 1 ∧
          (Frame.ofMountain result).upper terminal = none ∧
          (Frame.ofMountain result).rawParent terminal = none)) := by
  obtain ⟨g⟩ := p.root_geometry hLast
  have hOrdered := (build_normal_of_success p.initial_build).toOrdered
  cases hParent : (Frame.ofMountain p.initial).P g.rootNode with
  | none =>
      have hNone : (Canonical.findParent p.initial p.root).toOption = none := by
        simpa only [g.root_ref, hParent, Option.map_none] using
          Executable.findParent_toOption hOrdered g.rootNode
      obtain ⟨terminal, hBelow, hColumn, hReal, hOne, hUpper, hRaw, hLow⟩ :=
        p.blocks_parentless_highest_of_run hLast hRun g hParent
      exact ⟨Frame.ref terminal, (Frame.ofMountain result).cell terminal, hBelow,
        cellAt_of_frame_node result terminal, hLow,
        Or.inr ⟨hNone, terminal, rfl, hColumn, hReal, hOne, hUpper, hRaw⟩⟩
  | some parent =>
      have hSearch : Canonical.findParent p.initial p.root = .ok (Frame.ref parent) := by
        simpa only [g.root_ref] using
          (Executable.findParent_ref_iff hOrdered g.rootNode parent).mpr hParent
      obtain ⟨hFixed, reference, cell, hBelow, hRead, hLow, hEdge, hParentRead⟩ :=
        p.blocks_highest_edge_of_run hLast hRun g hParent
      exact ⟨reference, cell, hBelow, hRead, hLow,
        Or.inl ⟨parent, hSearch, hFixed, hEdge, hParentRead⟩⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_final_history_of_run
#print axioms OmegaY.Expansion.Preparation.blocks_highest_edge_of_run
#print axioms OmegaY.Expansion.Preparation.blocks_parentless_highest_of_run
#print axioms OmegaY.Expansion.Preparation.blocks_highest_classification_of_run
