/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TotalRowBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.Totality
import OmegaY.Expansion.BlocksRowBound

/-! The row bound applies to every legal input, including all deletion
branches. It bounds the graph returned by this expansion, before any new
canonical reconstruction for a subsequent expansion. -/

namespace OmegaY.Expansion

open Canonical

theorem expandDiagram_rows_bound {values : List Nat} {initial result : Mountain}
    (hBuild : Canonical.build values = .ok initial) {height : Row}
    (hBound : MountainRowsBound initial height) {copies : Nat}
    (hRun : expandDiagram values copies = .ok result) : MountainRowsBound result height := by
  by_cases hTrivial : values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0
  · have hActual : expandDiagram values copies = .ok initial.pop := by
      simp only [List.isEmpty_iff] at hTrivial
      simp [expandDiagram, hBuild, Except.mapError, hTrivial]
    have he : initial.pop = result := Except.ok.inj (hActual.symm.trans hRun)
    exact he ▸ hBound.pop
  · rcases build_success_legal hBuild with rfl | ⟨rest, rfl, hPositive⟩
    · simp at hTrivial
    · rcases List.eq_nil_or_concat' rest with rfl | ⟨middle, last, rfl⟩
      · simp at hTrivial
      · have hLastPositive : 0 < last := hPositive last (by simp)
        have hLastNe : last ≠ 1 := by
          intro hLast
          apply hTrivial
          right; left
          change ((1 :: middle) ++ [last]).getLast? = some 1
          rw [List.getLast?_append]
          simp [hLast]
        have hLast : 1 < last := by omega
        obtain ⟨p⟩ := preparation_total middle last
          (fun value hv => hPositive value (by simp [hv])) hLast
        have hInitial : p.initial = initial := Except.ok.inj (p.initial_build.symm.trans hBuild)
        have hPreparedBound : MountainRowsBound p.initial height := hInitial ▸ hBound
        exact p.expandDiagram_rows_bound hLast hPreparedBound hRun

theorem expandDiagram_total_bounded {values : List Nat} {initial : Mountain}
    (hBuild : Canonical.build values = .ok initial) {height : Row}
    (hBound : MountainRowsBound initial height) (copies : Nat) :
    ∃ result, expandDiagram values copies = .ok result ∧ MountainValid result ∧
      MountainRowsBound result height := by
  obtain ⟨result, hRun, hValid⟩ := expandDiagram_total (build_success_legal hBuild) copies
  exact ⟨result, hRun, hValid, expandDiagram_rows_bound hBuild hBound hRun⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_rows_bound
#print axioms OmegaY.Expansion.expandDiagram_total_bounded
