/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedKeyLabels.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedKeyBound

/-! Finite-label consequences of actual copied-edge certificates. The
block and source column are uniquely recovered from the target child.
Finite label matching is needed only on the key support and the two
endpoints, or on the finite source prefix through that child. -/

namespace OmegaY.Keys

/-- A source key retained through a finite embedding can be copied
directly from the smaller source graph. Only actual support coordinates
must agree; there is no total map of the larger intermediate width. -/
theorem mapSupported_relabel_eq {m n n' n'' : Nat}
    (original : Template m n) (current : Template m n')
    (embed : Fin n → Fin n') (mu : Fin n' → Nat)
    (hSupport : ∀ i column, current i = some column → mu column < n'')
    (hCurrent : current = relabel original embed)
    (nu : Fin n → Fin n'')
    (hAgree : ∀ i column, original i = some column → (nu column).val = mu (embed column)) :
    mapSupported current mu hSupport = relabel original nu := by
  subst current
  funext i
  cases h : original i with
  | none =>
    have hm : relabel original embed i = none := by simp only [relabel, h, Option.map_none]
    rw [mapSupported_none _ _ _ hm]
    simp only [relabel, h, Option.map_none]
  | some column =>
    have hm : relabel original embed i = some (embed column) := by
      simp only [relabel, h, Option.map_some]
    rw [mapSupported_some _ _ _ hm]
    simp only [relabel, h, Option.map_some]
    congr 1
    exact Fin.ext (hAgree i column h).symm

end OmegaY.Keys

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ActualCopiedKeyBound

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {result : Mountain} {hOrdered : (Frame.ofMountain result).Ordered}
  {edge : RealStoredEdge (Frame.ofMountain result)} {D : Nat}

/-- Quotient and remainder determine the actual positive block and the
source column; they cannot be arbitrarily selected by a key witness. -/
theorem column_coordinates (bound : ActualCopiedKeyBound p result hOrdered edge D) :
    (edge.lower.1.val - (p.root.column + 1)) / (p.reduced.size - 1 - p.root.column) = bound.block ∧
    p.root.column + 1 + (edge.lower.1.val - (p.root.column + 1)) %
      (p.reduced.size - 1 - p.root.column) = bound.source.lower.1.val := by
  let width := p.reduced.size - 1 - p.root.column
  let offset := bound.source.lower.1.val - (p.root.column + 1)
  have hRight := bound.source_right
  have hBound := bound.source_bound
  have hWidth : 0 < width := by dsimp [width]; omega
  have hOffset : offset < width := by dsimp [offset, width]; omega
  have hChild := bound.child_column
  rw [copiedKeyColumn, if_neg (not_lt_of_ge hRight.le)] at hChild
  have hDistance : edge.lower.1.val - (p.root.column + 1) = offset + bound.block * width := by
    dsimp [offset, width]
    omega
  change (edge.lower.1.val - (p.root.column + 1)) / width = bound.block ∧
    p.root.column + 1 + (edge.lower.1.val - (p.root.column + 1)) % width = _
  rw [hDistance, Nat.add_mul_div_right _ _ hWidth, Nat.div_eq_of_lt hOffset,
    Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hOffset]
  exact ⟨rfl, by dsimp [offset]; omega⟩

theorem block_unique (left right : ActualCopiedKeyBound p result hOrdered edge D) :
    left.block = right.block := left.column_coordinates.1.symm.trans right.column_coordinates.1

theorem source_column_unique (left right : ActualCopiedKeyBound p result hOrdered edge D) :
    left.source.lower.1.val = right.source.lower.1.val :=
  left.column_coordinates.2.symm.trans right.column_coordinates.2

/-- The whole source prefix through this particular lower is defined in
the output. This does not assert a map of the unused rest of the source. -/
theorem prefix_column_bound (bound : ActualCopiedKeyBound p result hOrdered edge D)
    (column : Fin (Frame.ofMountain p.reduced).width)
    (hColumn : column.val ≤ bound.source.lower.1.val) :
    copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column)) column.val <
      (Frame.ofMountain result).width :=
  ((copiedKeyColumn_strictMono p.root.column _).monotone hColumn).trans_lt
    (bound.child_column ▸ edge.lower.1.isLt)

theorem source_labels_le (bound : ActualCopiedKeyBound p result hOrdered edge D)
    {Label : Type*} [LinearOrder Label]
    (old : Fin (Frame.ofMountain p.reduced).width → Label)
    (fresh : Fin (Frame.ofMountain result).width → Label) (hFresh : StrictMono fresh)
    (hLabels : ∀ i column (h : bound.source.keyTemplate p.reduced_valid.toOrdered D i = some column),
      fresh ⟨copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column)) column.val,
        bound.support_bound i column h⟩ = old column) :
    Keys.eval (edge.keyTemplate hOrdered D) fresh ≤
      Keys.eval (bound.source.keyTemplate p.reduced_valid.toOrdered D) old :=
  (bound.finite_key_le fresh hFresh).trans_eq
    (Keys.eval_mapSupported_of_labels _ _ _ old fresh hLabels)

/-- The semantic weakening step required by splicing. The geometry and
the entire key comparison have already been supplied by actual execution;
only the reflected labels and old edge relation remain inputs. -/
theorem represented (bound : ActualCopiedKeyBound p result hOrdered edge D)
    (old : Fin (Frame.ofMountain p.reduced).width → Model.Label)
    (fresh : Fin (Frame.ofMountain result).width → Model.Label) (hFresh : StrictMono fresh)
    (hLabels : ∀ i column (h : bound.source.keyTemplate p.reduced_valid.toOrdered D i = some column),
      fresh ⟨copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column)) column.val,
        bound.support_bound i column h⟩ = old column)
    (hParent : fresh edge.parent.1 = old bound.source.parent.1)
    (hChild : fresh edge.lower.1 = old bound.source.lower.1)
    (hSource : Model.R (D + 1) (Keys.eval (bound.source.keyTemplate p.reduced_valid.toOrdered D) old)
      (old bound.source.parent.1) (old bound.source.lower.1)) :
    Model.R (D + 1) (Keys.eval (edge.keyTemplate hOrdered D) fresh)
      (fresh edge.parent.1) (fresh edge.lower.1) := by
  rw [hParent, hChild]
  exact Model.key_weaken (bound.source_labels_le old fresh hFresh hLabels) hSource

theorem represented_of_prefix_labels (bound : ActualCopiedKeyBound p result hOrdered edge D)
    (old : Fin (Frame.ofMountain p.reduced).width → Model.Label)
    (fresh : Fin (Frame.ofMountain result).width → Model.Label) (hFresh : StrictMono fresh)
    (hLabels : ∀ column (h : column.val ≤ bound.source.lower.1.val),
      fresh ⟨copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column)) column.val,
        bound.prefix_column_bound column h⟩ = old column)
    (hSource : Model.R (D + 1) (Keys.eval (bound.source.keyTemplate p.reduced_valid.toOrdered D) old)
      (old bound.source.parent.1) (old bound.source.lower.1)) :
    Model.R (D + 1) (Keys.eval (edge.keyTemplate hOrdered D) fresh)
      (fresh edge.parent.1) (fresh edge.lower.1) := by
  have hParentBefore := rawParent_column_lt p.reduced_valid.toOrdered bound.source.parent_eq
  apply bound.represented old fresh hFresh _ _ _ hSource
  · intro i column h
    exact hLabels column (bound.source.keyTemplate_column_bound p.reduced_valid.toOrdered h).2.le
  · have hParentFin : edge.parent.1 =
        ⟨copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column))
          bound.source.parent.1.val, bound.prefix_column_bound bound.source.parent.1 hParentBefore.le⟩ :=
      Fin.ext bound.parent_column
    rw [hParentFin]
    exact hLabels bound.source.parent.1 hParentBefore.le
  · have hChildFin : edge.lower.1 =
        ⟨copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column))
          bound.source.lower.1.val, bound.prefix_column_bound bound.source.lower.1 le_rfl⟩ :=
      Fin.ext bound.child_column
    rw [hChildFin]
    exact hLabels bound.source.lower.1 le_rfl

end ActualCopiedKeyBound
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualCopiedKeyBound.column_coordinates
#print axioms OmegaY.Keys.mapSupported_relabel_eq
#print axioms OmegaY.Expansion.ActualCopiedKeyBound.source_labels_le
#print axioms OmegaY.Expansion.ActualCopiedKeyBound.represented
#print axioms OmegaY.Expansion.ActualCopiedKeyBound.represented_of_prefix_labels
