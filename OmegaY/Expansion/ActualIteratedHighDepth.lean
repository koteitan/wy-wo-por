/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualIteratedHighDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighCopiedDepth

/-!
# High-event depths in every actual finite copying block

The newest block uses the three proved parent-chain exits. Earlier blocks
are complete preserved columns; their event indices are resampled by the
actual common high cut before applying the induction hypothesis. Block zero
denotes the original reduced source and is included. No depth invariant is
supplied for an intermediate run.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- Every stated block/source position is an actual column of the outer
result. Block zero is the unchanged reduced-source position. -/
theorem Preparation.blocks_shifted_column_lt
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {block column : Nat} (hBlock : block ≤ copies) (hColumn : column < p.reduced.size) :
    column + block * (p.reduced.size - 1 - p.root.column) < result.size := by
  obtain ⟨ready, _⟩ := p.blocks_high_root_boundary_of_success hLast hRun
  have hInitial := (p.initial_block_ready hLast).size_eq
  have hFinal := ready.size_eq
  simp only [Nat.one_mul] at hInitial
  rw [Nat.add_mul, Nat.one_mul] at hFinal
  have hMul := Nat.mul_le_mul_right (p.reduced.size - 1 - p.root.column) hBlock
  omega

/-- Every existing copied column, in any block up to the executed copy
count, has exactly the source column's depth at equal high cuts. Actual
prefix runs and their fresh event samplings are recovered internally. -/
theorem Preparation.blocks_high_depth_at_equal_cut
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    (hValid : MountainValid result) (hSourceWidth : 0 < p.reduced.size)
    (hTargetWidth : 0 < result.size)
    {block : Nat} (hBlock : block ≤ copies)
    {sourceColumn : Fin (Frame.ofMountain p.reduced).width}
    (hRight : p.root.column < sourceColumn.val)
    {sourceEvent targetEvent : Nat}
    (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hCut : (Frame.ofMountain result).eventCut targetEvent =
      (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    parentDepth (eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent)
        (sourceColumn.val + block * (p.reduced.size - 1 - p.root.column)) =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) sourceColumn.val := by
  induction copies generalizing result targetEvent with
  | zero =>
      have he : p.reduced = result := Except.ok.inj hRun
      subst result
      have hZero : block = 0 := Nat.eq_zero_of_le_zero hBlock
      have hPreserved : PreservesColumns p.reduced p.reduced := fun _ _ => rfl
      simpa only [hZero, Nat.zero_mul, Nat.add_zero] using hPreserved.event_parentDepth
        (build_normal_of_success p.reduced_build).toOrdered hValid.toOrdered
        hSourceWidth hTargetWidth hCut sourceColumn.isLt
  | succ previous ih =>
      rcases p.blocks_final_history_of_run hLast hRun with ⟨hn, _⟩ |
        ⟨actualPrevious, start, references, hCount, hPrefix, state, history⟩
      · omega
      · have hPrevious : actualPrevious = previous := by omega
        subst actualPrevious
        by_cases hNewest : block = previous + 1
        · subst block
          exact state.actual_high_column_depth history hLast hPrefix hRun hSourceWidth hTargetWidth
            hRight hSourceEvent hHigh hCut
        · have hOldBlock : block ≤ previous := by omega
          obtain ⟨startEvent, _, _, _, hStartCut⟩ :=
            p.blocks_high_event_correspondence hLast hPrefix hSourceEvent hHigh
          have hStartWidth : 0 < start.size := hSourceWidth.trans_le state.base_preserved.size_le
          have hOldDepth := ih hPrefix state.start_valid hStartWidth hOldBlock hStartCut
          have hOldColumn : sourceColumn.val + block * (p.reduced.size - 1 - p.root.column) < start.size :=
            p.blocks_shifted_column_lt hLast hPrefix hOldBlock sourceColumn.isLt
          have hDepth := state.start_preserved.event_parentDepth state.start_valid.toOrdered
            hValid.toOrdered hStartWidth hTargetWidth (hCut.trans hStartCut.symm) hOldColumn
          exact hDepth.trans hOldDepth

/-- A single target event is chosen from the real high-tail sampling.
At that event all copied blocks, including the original block zero, have
the source depths at their actual shifted columns. -/
theorem Preparation.blocks_all_high_depth
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    ∃ (hValid : MountainValid result) (hSourceWidth : 0 < p.reduced.size)
      (hTargetWidth : 0 < result.size) (targetEvent : Nat),
      (Frame.ofMountain result).highEventStart p.lastTop.row ≤ targetEvent ∧
      targetEvent ≤ (Frame.ofMountain result).lastEvent ∧
      (p.blocks_high_event_sampling hLast hRun).sample targetEvent = sourceEvent ∧
      (Frame.ofMountain result).eventCut targetEvent =
        (Frame.ofMountain p.reduced).eventCut sourceEvent ∧
      ∀ block, block ≤ copies → ∀ sourceColumn : Fin (Frame.ofMountain p.reduced).width,
        p.root.column < sourceColumn.val →
        sourceColumn.val + block * (p.reduced.size - 1 - p.root.column) < result.size ∧
        parentDepth (eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent)
            (sourceColumn.val + block * (p.reduced.size - 1 - p.root.column)) =
          parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
            (p.reduced.size - 1) sourceEvent) sourceColumn.val := by
  obtain ⟨ready, _⟩ := p.blocks_high_root_boundary_of_success hLast hRun
  obtain ⟨nodes, hNodes, _⟩ := cellAt_ok_iff.mp p.restored_root
  have hRootBound := (Array.getElem?_eq_some_iff.mp hNodes).1
  have hSourceWidth : 0 < p.reduced.size := (Nat.zero_le p.root.column).trans_lt hRootBound
  have hTargetWidth : 0 < result.size := hSourceWidth.trans_le ready.base_preserved.size_le
  obtain ⟨targetEvent, hStart, hEnd, hSample, hCut⟩ :=
    p.blocks_high_event_correspondence hLast hRun hSourceEvent hHigh
  refine ⟨ready.valid, hSourceWidth, hTargetWidth, targetEvent, hStart, hEnd, hSample, hCut, ?_⟩
  intro block hBlock sourceColumn hRight
  exact ⟨p.blocks_shifted_column_lt hLast hRun hBlock sourceColumn.isLt,
    p.blocks_high_depth_at_equal_cut hLast hRun ready.valid hSourceWidth hTargetWidth hBlock
      hRight hSourceEvent hHigh hCut⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_shifted_column_lt
#print axioms OmegaY.Expansion.Preparation.blocks_high_depth_at_equal_cut
#print axioms OmegaY.Expansion.Preparation.blocks_all_high_depth
