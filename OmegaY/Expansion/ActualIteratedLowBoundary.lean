/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualIteratedLowBoundary.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNextBoundaryAll
import OmegaY.Expansion.LoopPrefix

/-!
# Actual low-root boundary paths through every finite number of blocks

Each block's complete execution constructs its finished dynamic state and
column history. Its newly selected boundary has a real stored-parent path
to the preceding block's actual selector at the same original root-upper
cut. Complete-column preservation and path composition carry this to the
original low root. No per-block path, output normality, or numerical parent
recognition is supplied as an input.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- One real copying block constructs a path between its actual old and
new selectors at a fixed original lower-root cap. The full execution
history used by the single-block theorem is recovered here. -/
theorem BlockReady.copyBlock_low_boundary_path
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start : Mountain} (ready : BlockReady p block start)
    (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← OmegaY.Expansion.copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper) :
    ∃ result,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧ PreservesColumns start result ∧
      ∃ oldReference newReference cell,
        below start (start.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
          .ok oldReference ∧
        below result (result.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
          .ok newReference ∧
        Canonical.cellAt result newReference = .ok cell ∧
        RawRefPath result newReference oldReference := by
  obtain ⟨baseReference, baseCell, hBaseBelow, hBaseRead, _, _, _⟩ :=
    p.initial_low_root_reference_path hLast hRootReal hRootColumn hBefore hRootUpper
  obtain ⟨source, hSourceRef, _⟩ := Canonical.frame_node_of_cellAt hBaseRead
  have hSourceBelow : below p.reduced (p.reduced.size - 1)
      ((Frame.ofMountain p.initial).height rootUpper) = .ok (Frame.ref source) := by
    simpa only [hSourceRef] using hBaseBelow
  obtain ⟨result, references, hRun, hReady, _, state, history⟩ :=
    ready.copyBlock_with_history hLast
  obtain ⟨_, sourceCopy, rootCopy, _, _, hNextBelow, hStartBelow, hPath⟩ :=
    state.next_low_boundary_path history hLast hStartRun
      hRootReal hRootColumn hBefore hRootUpper hSourceBelow
  exact ⟨result, hRun, hReady, state.start_preserved,
    rootCopy.reference, sourceCopy.outputRef, sourceCopy.read.outputCell,
    hStartBelow, hNextBelow, sourceCopy.output_read, hPath⟩

/-- Any finite number of the actual outer-loop blocks produces a selector
with a real raw-parent path to the original low root. The cut is the same
original root-upper height at every stage. -/
theorem Preparation.blocks_low_boundary_path
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper) (copies : Nat) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧
      ∃ reference cell,
        below result (result.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
          .ok reference ∧
        Canonical.cellAt result reference = .ok cell ∧
        RawRefPath result reference (Frame.ref root) := by
  have hSizes : p.initial.size = p.reduced.size := by
    have hInitial := build_size p.initial_build
    have hReduced := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hInitial hReduced
    exact hInitial.trans hReduced.symm
  induction copies with
  | zero =>
      obtain ⟨reference, cell, hBelow, hRead, _, _, hPath⟩ :=
        p.initial_low_root_reference_path hLast hRootReal hRootColumn hBefore hRootUpper
      exact ⟨p.reduced, rfl, p.initial_block_ready hLast, reference, cell, hBelow, hRead, hPath⟩
  | succ copies ih =>
      obtain ⟨start, hPrefix, hReady, oldReference, _, hOldBelow, _, hOldPath⟩ := ih
      obtain ⟨result, hCopy, hNext, hPreserved, actualOld, newReference, cell,
          hActualOld, hNewBelow, hNewRead, hBlockPath⟩ :=
        hReady.copyBlock_low_boundary_path hLast hPrefix hRootReal hRootColumn hBefore hRootUpper
      have hOldEq : actualOld = oldReference := Except.ok.inj (hActualOld.symm.trans hOldBelow)
      have hFullPath : RawRefPath result newReference (Frame.ref root) := by
        rw [hOldEq] at hBlockPath
        exact hBlockPath.trans (hOldPath.preserve hPreserved)
      have hStep : copyBlock start p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (copies + 1) = .ok result := by
        simpa only [hSizes] using hCopy
      exact ⟨result, forIn_yield_range_succ p.reduced
        (fun block mountain => copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)) hPrefix hStep,
        hNext, newReference, cell, hNewBelow, hNewRead, hFullPath⟩

/-- Determinism transfers the constructed path to any actual complete
outer-loop output, without assuming a successful path for any block. -/
theorem Preparation.blocks_low_boundary_path_of_run
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper) :
    ∃ reference cell,
      below result (result.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
        .ok reference ∧
      Canonical.cellAt result reference = .ok cell ∧
      RawRefPath result reference (Frame.ref root) := by
  obtain ⟨actual, hActual, _, hPath⟩ :=
    p.blocks_low_boundary_path hLast hRootReal hRootColumn hBefore hRootUpper copies
  have he : actual = result := Except.ok.inj (hActual.symm.trans hRun)
  exact he ▸ hPath

/-- Any caller-observed successful selector is the constructed endpoint,
so it too has a path to the original low root. -/
theorem Preparation.blocks_low_selected_path
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper)
    {reference : Ref}
    (hBelow : below result (result.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
      .ok reference) : RawRefPath result reference (Frame.ref root) := by
  obtain ⟨actual, _, hActual, _, hPath⟩ :=
    p.blocks_low_boundary_path_of_run hLast hRun hRootReal hRootColumn hBefore hRootUpper
  have he : actual = reference := Except.ok.inj (hActual.symm.trans hBelow)
  exact he ▸ hPath

end OmegaY.Expansion

#print axioms OmegaY.Expansion.BlockReady.copyBlock_low_boundary_path
#print axioms OmegaY.Expansion.Preparation.blocks_low_boundary_path
#print axioms OmegaY.Expansion.Preparation.blocks_low_boundary_path_of_run
#print axioms OmegaY.Expansion.Preparation.blocks_low_selected_path
