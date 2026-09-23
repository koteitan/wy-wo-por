/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SupportedDimension.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DynamicsRowBound
import OmegaY.Expansion.ActualBlockSplice

/-! A chosen key dimension is preserved by the actual program, including
the temporary last columns used inside the outer copying loop. The bound
is inherited from the input, without increasing the dimension between
successive expansions. No termination assumption is used. -/

namespace OmegaY.Expansion

open Canonical Geometry Frame

def MountainKeyDimension (mountain : Mountain) (D : Nat) : Prop :=
  ∀ node : (Frame.ofMountain mountain).Node,
    ∀ i, D < i → Row.coeff ((Frame.ofMountain mountain).height node) i = 0

private theorem jump_foldr_max_le (rows : List Row) (D : Nat)
    (hRows : ∀ row ∈ rows, Row.jump 0 row ≤ D + 1) :
    Row.jump 0 (rows.foldr max 0) ≤ D + 1 := by
  induction rows with
  | nil => simp only [List.foldr_nil, Row.jump_self]; omega
  | cons head tail ih =>
    have hHead := hRows head List.mem_cons_self
    have hTail := ih (fun row h => hRows row (List.mem_cons_of_mem _ h))
    simp only [List.foldr_cons]
    rcases le_total head (tail.foldr max 0) with h | h
    · rw [max_eq_right h]
      exact hTail
    · rw [max_eq_left h]
      exact hHead

theorem MountainKeyDimension.rowCeiling_jump_le {mountain : Mountain} {D : Nat}
    (hDimension : MountainKeyDimension mountain D) :
    Row.jump 0 (rowCeiling mountain) ≤ D + 1 := by
  apply jump_foldr_max_le
  intro row hRow
  obtain ⟨column, hColumn, hCell⟩ := List.mem_flatMap.mp hRow
  obtain ⟨cell, hMem, rfl⟩ := List.mem_map.mp hCell
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hColumn
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hMem
  have hRead : Canonical.cellAt mountain ⟨c, i⟩ = .ok cell := by
    apply Canonical.cellAt_ok_iff.mpr
    exact ⟨column, by simpa only [Array.getElem?_toList] using hc,
      by simpa only [Array.getElem?_toList] using hi⟩
  obtain ⟨node, _, hNode⟩ := Canonical.frame_node_of_cellAt hRead
  apply Row.jump_le_iff.mpr
  intro j hj
  have hZero := hDimension node j (by omega)
  change Row.coeff ((Frame.ofMountain mountain).cell node).row j = 0 at hZero
  rw [hNode] at hZero
  simpa only [Row.coeff_zero] using hZero.symm

theorem MountainKeyDimension.of_rows_bound {before after : Mountain} {D : Nat}
    (hDimension : MountainKeyDimension before D)
    (hBound : MountainRowsBound after (rowCeiling before)) :
    MountainKeyDimension after D := by
  intro node i hi
  exact Row.coeff_zero_above_bound
    (hBound _ _ (Canonical.cellAt_of_frame_node after node))
    (hDimension.rowCeiling_jump_le.trans (by omega))

theorem expandDiagram_key_dimension {values : List Nat} {initial : Mountain}
    (hBuild : Canonical.build values = .ok initial) {D : Nat}
    (hDimension : MountainKeyDimension initial D) {copies : Nat} {result : Mountain}
    (hRun : expandDiagram values copies = .ok result) :
    MountainKeyDimension result D :=
  hDimension.of_rows_bound (expandDiagram_rows_bound hBuild (rowCeiling_bound initial) hRun)

namespace Preparation

variable {front : List Nat} {last : Nat} (p : Preparation front last)

theorem reduced_key_dimension (hLast : 1 < last) {D : Nat}
    (hDimension : MountainKeyDimension p.initial D) :
    MountainKeyDimension p.reduced D :=
  hDimension.of_rows_bound (p.reduced_rows_bound hLast (rowCeiling_bound p.initial))

theorem physicalBlock_rows_bound (hLast : 1 < last) (block : Nat) {height : Row}
    (hBound : MountainRowsBound p.initial height) :
    MountainRowsBound (p.physicalBlock hLast block) height := by
  obtain ⟨result, hRun, _, hResult⟩ := p.blocks_bounded hLast block hBound
  rw [p.physicalBlock_eq_of_run hLast hRun]
  exact hResult

theorem physicalBlock_key_dimension (hLast : 1 < last) {D : Nat}
    (hDimension : MountainKeyDimension p.initial D) (block : Nat) :
    MountainKeyDimension (p.physicalBlock hLast block) D :=
  hDimension.of_rows_bound (p.physicalBlock_rows_bound hLast block (rowCeiling_bound p.initial))

theorem spliceMountain_key_dimension (hLast : 1 < last) {D : Nat}
    (hDimension : MountainKeyDimension p.initial D) (block : Nat) :
    MountainKeyDimension (p.spliceMountain hLast block) D :=
  hDimension.of_rows_bound
    (p.physicalBlock_rows_bound hLast block (rowCeiling_bound p.initial)).pop

end Preparation

namespace Dynamics

def KeyDimension (s : Expr) (D : Nat) : Prop := MountainKeyDimension (diagram s) D

theorem next_key_dimension {s : Expr} {D : Nat} (hDimension : KeyDimension s D)
    (copies : Nat) : KeyDimension (next s copies) D :=
  expandDiagram_key_dimension (diagram_build s) hDimension (next_diagram_run s copies)

theorem Step.key_dimension {child parent : Expr} (step : Step child parent)
    {D : Nat} (hDimension : KeyDimension parent D) : KeyDimension child D := by
  obtain ⟨_, copies, rfl⟩ := step
  exact next_key_dimension hDimension copies

theorem Path.key_dimension {root output : Expr} (path : Path root output)
    {D : Nat} (hDimension : KeyDimension root D) : KeyDimension output D := by
  induction path with
  | refl => exact hDimension
  | tail prior copies _ ih => exact next_key_dimension ih copies

end Dynamics
end OmegaY.Expansion

#print axioms OmegaY.Expansion.MountainKeyDimension.rowCeiling_jump_le
#print axioms OmegaY.Expansion.expandDiagram_key_dimension
#print axioms OmegaY.Expansion.Preparation.physicalBlock_key_dimension
#print axioms OmegaY.Expansion.Preparation.spliceMountain_key_dimension
#print axioms OmegaY.Expansion.Dynamics.Path.key_dimension
