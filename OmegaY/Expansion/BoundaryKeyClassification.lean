/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BoundaryKeyClassification.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BoundaryKeySources
import OmegaY.Expansion.DecrementKeyClassification
import OmegaY.Keys.ModelExtensionality

/-! Every actual boundary edge uses either a transported old last-column
lower edge, or a transported internal root edge. The latter has all key
parameters in the fixed good part, so its next-block transport agrees. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

inductive BoundaryOriginalKeyOrigin {front : List Nat} {last : Nat}
    (p : Preparation front last) (g : RootGeometry p) (hLast : 1 < last) (block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1))))
    (D : Nat) : Prop
  | lower (old : g.LowerEdge)
      (hParent : edge.parent.1.val = copiedKeyColumn p.root.column
        (block * (front.length - p.root.column)) old.val.parent.1.val)
      (hKey : Keys.eval (edge.keyTemplate (p.spliceMountain_valid hLast (block + 1)).toOrdered D)
          (fun c => c.val) ≤
        Keys.eval (old.val.keyTemplate p.initial_valid.toOrdered D)
          (fun c => copiedKeyColumn p.root.column (block * (front.length - p.root.column)) c.val))
  | grafted (old : RealStoredEdge (Frame.ofMountain p.initial.pop))
      (hColumn : old.lower.1.val = p.root.column)
      (hParent : edge.parent.1.val = old.parent.1.val)
      (hKey : Keys.eval (edge.keyTemplate (p.spliceMountain_valid hLast (block + 1)).toOrdered D)
          (fun c => c.val) ≤
        Keys.eval (old.keyTemplate p.initial_valid.pop.toOrdered D)
          (fun c => copiedKeyColumn p.root.column ((block + 1) * (front.length - p.root.column)) c.val))

theorem Preparation.boundary_original_key_origin
    {front : List Nat} {last : Nat} (p : Preparation front last) (g : RootGeometry p)
    (hLast : 1 < last) (block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1))))
    (hColumn : edge.lower.1.val = (p.spliceMountain hLast block).size)
    (D : Nat) (hDimension : MountainKeyDimension p.initial D) :
    BoundaryOriginalKeyOrigin p g hLast block edge D := by
  obtain ⟨bound⟩ := p.splice_boundary_key_bound hLast block edge hColumn D hDimension
  cases p.reduced_edge_key_origin g hLast bound.source with
  | retained old hEdge =>
    have hSource := bound.source_last
    have hMap := congrArg (fun e => e.lower.1.val) hEdge
    have hSame : (p.initial_pop_preserved_reduced.storedEdge old).lower.1.val = old.lower.1.val :=
      p.initial_pop_preserved_reduced.mapNode_column old.lower
    rw [hSame, hSource] at hMap
    have hBound : old.lower.1.val < p.initial.pop.size := old.lower.1.isLt
    rw [p.initial_pop_size] at hBound
    omega
  | lower old _hLastColumn hParent _hDegree hKey =>
    have hParentColumn : old.val.parent.1.val = bound.source.parent.1.val :=
      congrArg Ref.column hParent
    have hEval := Keys.eval_eq_of_model_eval_eq
      (bound.source.keyTemplate p.reduced_valid.toOrdered D)
      (old.val.keyTemplate p.initial_valid.toOrdered D) (hKey D)
      (copiedKeyColumn p.root.column (block * (front.length - p.root.column)))
    exact .lower old (by rw [bound.parent_column, ← hParentColumn])
      (bound.key_le.trans_eq hEval)
  | grafted old _hLastColumn hOldColumn hParent _hDegree hKey =>
    have hParentGood : old.parent.1.val < p.root.column :=
      (rawParent_column_lt p.initial_valid.toOrdered old.parent_eq).trans_eq hOldColumn
    have hParentColumn : old.parent.1.val = bound.source.parent.1.val := congrArg Ref.column hParent
    have hTargetParent : edge.parent.1.val = old.parent.1.val := by
      rw [bound.parent_column, ← hParentColumn, copiedKeyColumn, if_pos hParentGood]
    have hEval := Keys.eval_eq_of_model_eval_eq
      (bound.source.keyTemplate p.reduced_valid.toOrdered D)
      (old.keyTemplate p.initial_valid.toOrdered D) (hKey D)
      (copiedKeyColumn p.root.column (block * (front.length - p.root.column)))
    have hFixed : Keys.eval (old.keyTemplate p.initial_valid.toOrdered D)
        (fun c => copiedKeyColumn p.root.column (block * (front.length - p.root.column)) c.val) =
        Keys.eval (old.keyTemplate p.initial_valid.toOrdered D)
        (fun c => copiedKeyColumn p.root.column ((block + 1) * (front.length - p.root.column)) c.val) := by
      funext i
      simp only [Keys.eval, Pi.toLex_apply]
      cases ht : old.keyTemplate p.initial_valid.toOrdered D i with
      | none => rfl
      | some column =>
        have hGood := (old.keyTemplate_column_bound p.initial_valid.toOrdered ht).1.trans_lt hParentGood
        simp only [copiedKeyColumn, if_pos hGood]
    let preserved := PreservesColumns.pop_prefix p.initial
    have hOldBefore : old.lower.1.val < p.initial.pop.size := by
      rw [hOldColumn, p.initial_pop_size]
      exact p.root_before_last
    obtain ⟨prefixEdge, hPrefix⟩ := preserved.storedEdge_preimage p.initial_valid.toOrdered old hOldBefore
    have hPrefixChild : prefixEdge.lower.1.val = p.root.column :=
      (preserved.mapNode_column prefixEdge.lower).symm.trans
        ((congrArg (fun e => e.lower.1.val) hPrefix).trans hOldColumn)
    have hPrefixParent : old.parent.1.val = prefixEdge.parent.1.val := by
      rw [← hPrefix]
      exact preserved.mapNode_column prefixEdge.parent
    have hPrefixKey := preserved.storedEdge_key_eval (Label := Nat)
      p.initial_valid.pop.toOrdered p.initial_valid.toOrdered prefixEdge D
      (fun c => copiedKeyColumn p.root.column ((block + 1) * (front.length - p.root.column)) c.val)
    rw [hPrefix] at hPrefixKey
    change Keys.eval (old.keyTemplate p.initial_valid.toOrdered D)
        (fun c => copiedKeyColumn p.root.column ((block + 1) * (front.length - p.root.column)) c.val) =
      Keys.eval (prefixEdge.keyTemplate p.initial_valid.pop.toOrdered D)
        (fun c => copiedKeyColumn p.root.column ((block + 1) * (front.length - p.root.column)) c.val)
      at hPrefixKey
    exact .grafted prefixEdge hPrefixChild (hTargetParent.trans hPrefixParent)
      (bound.key_le.trans_eq (hEval.trans (hFixed.trans hPrefixKey)))

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.boundary_original_key_origin
