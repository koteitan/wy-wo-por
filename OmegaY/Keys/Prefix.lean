/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Keys/Prefix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Keys

/-! Exact restriction of finite key templates to a prefix containing all
of their named columns. The infinity marker remains infinity. -/

namespace OmegaY.Keys

def restrictPrefix {m n : Nat} (t : Template m n) (k : Nat)
    (hBound : ∀ i column, t i = some column → column.val < k) : Template m k :=
  fun i => match h : t i with
    | none => none
    | some column => some ⟨column.val, hBound i column h⟩

theorem relabel_restrictPrefix {m n k : Nat} (t : Template m n)
    (hBound : ∀ i column, t i = some column → column.val < k)
    (hk : k ≤ n) : relabel (restrictPrefix t k hBound) (Fin.castLE hk) = t := by
  funext i
  unfold relabel restrictPrefix
  split <;> simp_all

theorem templateKey_relabel_lt_iff {m n k : Nat} (t s : Template m n)
    (mu : Fin n → Fin k) (hMono : StrictMono mu) :
    templateKey (relabel t mu) < templateKey (relabel s mu) ↔ templateKey t < templateKey s := by
  have hT : templateKey (relabel t mu) = eval t mu := by
    exact eval_relabel_of_labels t mu mu id (fun _ => rfl)
  have hS : templateKey (relabel s mu) = eval s mu := by
    exact eval_relabel_of_labels s mu mu id (fun _ => rfl)
  rw [hT, hS]
  constructor
  · intro h
    by_contra hn
    exact not_lt_of_ge (eval_le_of_template_le s t mu hMono (le_of_not_gt hn)) h
  · exact eval_lt_of_template_lt t s mu hMono

theorem restrictPrefix_lt_iff {m n k : Nat} (t s : Template m n)
    (hT : ∀ i column, t i = some column → column.val < k)
    (hS : ∀ i column, s i = some column → column.val < k)
    (hk : k ≤ n) :
    templateKey (restrictPrefix t k hT) < templateKey (restrictPrefix s k hS) ↔
      templateKey t < templateKey s := by
  have h := templateKey_relabel_lt_iff (restrictPrefix t k hT) (restrictPrefix s k hS)
    (Fin.castLE hk) (fun _ _ hi => hi)
  rw [relabel_restrictPrefix t hT hk, relabel_restrictPrefix s hS hk] at h
  exact h.symm

end OmegaY.Keys

#print axioms OmegaY.Keys.relabel_restrictPrefix
#print axioms OmegaY.Keys.templateKey_relabel_lt_iff
#print axioms OmegaY.Keys.restrictPrefix_lt_iff
