/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ExecutedBlockPrefix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualIteratedHighestBoundary

/-!
# Recover any chosen actual copying block from an outer execution

The prefix retains the real successful outer runs before and after that
block, its complete inner execution history, and preservation of its
completed columns in the later result. The requested block is positive and
no larger than the executed count. Neither a successful prefix nor an
intermediate history is supplied by the caller.
-/

namespace OmegaY.Expansion

open Canonical

structure ExecutedBlockPrefix {front : List Nat} {last : Nat}
    (p : Preparation front last) (block : Nat) (result : Mountain) where
  block_pos : 0 < block
  start : Mountain
  completed : Mountain
  references : List Ref
  start_run : (forIn (List.range (block - 1)) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start
  completed_run : (forIn (List.range block) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok completed
  state : DynamicBlockState p block start references p.reduced.size completed
  history : CopyRunHistory p block start references p.reduced.size completed
  preserved : PreservesColumns completed result

def ExecutedBlockPrefix.preserve
    {front : List Nat} {last : Nat} {p : Preparation front last} {block : Nat}
    {before after : Mountain} (packet : ExecutedBlockPrefix p block before)
    (hPreserve : PreservesColumns before after) : ExecutedBlockPrefix p block after where
  block_pos := packet.block_pos
  start := packet.start
  completed := packet.completed
  references := packet.references
  start_run := packet.start_run
  completed_run := packet.completed_run
  state := packet.state
  history := packet.history
  preserved := packet.preserved.trans hPreserve

/-- Arbitrary earlier blocks are obtained by peeling the actual outer
run, rather than postulating an independent compatible history. -/
theorem Preparation.blocks_executed_prefix
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {block : Nat} (hPositive : 0 < block) (hBlock : block ≤ copies) :
    Nonempty (ExecutedBlockPrefix p block result) := by
  induction copies generalizing result with
  | zero => omega
  | succ previous ih =>
      rcases p.blocks_final_history_of_run hLast hRun with ⟨hn, _⟩ |
        ⟨actualPrevious, start, references, hCount, hPrefix, state, history⟩
      · omega
      · have hPrevious : actualPrevious = previous := by omega
        subst actualPrevious
        by_cases hNewest : block = previous + 1
        · subst block
          exact ⟨{
            block_pos := Nat.zero_lt_succ _
            start := start
            completed := result
            references := references
            start_run := by simpa only [Nat.add_sub_cancel_right] using hPrefix
            completed_run := hRun
            state := state
            history := history
            preserved := fun _ _ => rfl }⟩
        · have hOld : block ≤ previous := by omega
          obtain ⟨packet⟩ := ih hPrefix hOld
          exact ⟨packet.preserve state.start_preserved⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_executed_prefix
