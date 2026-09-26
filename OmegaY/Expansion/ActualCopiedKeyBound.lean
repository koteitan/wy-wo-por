/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedKeyBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedEdgeSource
import OmegaY.Expansion.ActualEffectiveEdgeColumns

/-!
# A common actual copied-edge certificate

The source edge, positive executed block, endpoint column map and complete
key bound are bundled for downstream finite splicing. The ordinary case
is constructed from the exhaustive executable adjacent-source theorem.
Fill edges can reuse an actual control's certificate by key weakening.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

structure ActualCopiedKeyBound {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (hOrdered : (Frame.ofMountain result).Ordered)
    (edge : RealStoredEdge (Frame.ofMountain result)) (D : Nat) where
  block : Nat
  block_pos : 0 < block
  source : RealStoredEdge (Frame.ofMountain p.reduced)
  source_right : p.root.column < source.lower.1.val
  parent_column : edge.parent.1.val = copiedKeyColumn p.root.column
    (block * (p.reduced.size - 1 - p.root.column)) source.parent.1.val
  child_column : edge.lower.1.val = copiedKeyColumn p.root.column
    (block * (p.reduced.size - 1 - p.root.column)) source.lower.1.val
  key_le : Keys.eval (edge.keyTemplate hOrdered D) (fun c => c.val) ≤
    Keys.eval (source.keyTemplate p.reduced_valid.toOrdered D)
      (fun c => copiedKeyColumn p.root.column
        (block * (p.reduced.size - 1 - p.root.column)) c.val)

namespace ActualCopiedKeyBound

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {result : Mountain} {hOrdered : (Frame.ofMountain result).Ordered}
  {edge : RealStoredEdge (Frame.ofMountain result)} {D : Nat}

theorem source_bound (bound : ActualCopiedKeyBound p result hOrdered edge D) :
    bound.source.lower.1.val < p.reduced.size := bound.source.lower.1.isLt

/-- This operation only transfers a certificate between actual edges
with the same endpoint columns and a proved weaker key. -/
def weaken (bound : ActualCopiedKeyBound p result hOrdered edge D)
    {fresh : RealStoredEdge (Frame.ofMountain result)}
    (hParent : fresh.parent.1.val = edge.parent.1.val)
    (hChild : fresh.lower.1.val = edge.lower.1.val)
    (hKey : Keys.eval (fresh.keyTemplate hOrdered D) (fun c => c.val) ≤
      Keys.eval (edge.keyTemplate hOrdered D) (fun c => c.val)) :
    ActualCopiedKeyBound p result hOrdered fresh D where
  block := bound.block
  block_pos := bound.block_pos
  source := bound.source
  source_right := bound.source_right
  parent_column := hParent.trans bound.parent_column
  child_column := hChild.trans bound.child_column
  key_le := hKey.trans bound.key_le

/-- Every finite mapped source root is a genuine target column. This
depends only on the actual endpoint map, so it also covers weakened fill
certificates, whose degree may differ from the control's degree. -/
theorem support_bound (bound : ActualCopiedKeyBound p result hOrdered edge D)
    (i : Fin (D + 1)) (column : Fin (Frame.ofMountain p.reduced).width)
    (h : bound.source.keyTemplate p.reduced_valid.toOrdered D i = some column) :
    copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column)) column.val <
      (Frame.ofMountain result).width := by
  have hBefore := (bound.source.keyTemplate_column_bound p.reduced_valid.toOrdered h).2
  exact ((copiedKeyColumn_strictMono p.root.column _ hBefore).trans_eq bound.child_column.symm).trans
    edge.lower.1.isLt

def mappedKey (bound : ActualCopiedKeyBound p result hOrdered edge D) :
    Keys.Template (D + 1) (Frame.ofMountain result).width :=
  Keys.mapSupported (bound.source.keyTemplate p.reduced_valid.toOrdered D)
    (fun c => copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column)) c.val)
    bound.support_bound

theorem mappedKey_nat_eval (bound : ActualCopiedKeyBound p result hOrdered edge D) :
    Keys.eval bound.mappedKey (fun c => c.val) =
      Keys.eval (bound.source.keyTemplate p.reduced_valid.toOrdered D)
        (fun c => copiedKeyColumn p.root.column (bound.block * (p.reduced.size - 1 - p.root.column)) c.val) :=
  Keys.eval_mapSupported_of_labels _ _ _ _ _ (fun _ _ _ => rfl)

/-- The natural-key bound reflects back to the finite template order;
there are no labels assigned outside the actual output. -/
theorem template_le (bound : ActualCopiedKeyBound p result hOrdered edge D) :
    Keys.templateKey (edge.keyTemplate hOrdered D) ≤ Keys.templateKey bound.mappedKey := by
  by_contra hn
  have hStrict := Keys.eval_lt_of_template_lt bound.mappedKey (edge.keyTemplate hOrdered D)
    (fun c => c.val) (fun _ _ h => h) (lt_of_not_ge hn)
  rw [bound.mappedKey_nat_eval] at hStrict
  exact (not_lt_of_ge bound.key_le) hStrict

theorem finite_key_le (bound : ActualCopiedKeyBound p result hOrdered edge D)
    {Label : Type*} [LinearOrder Label]
    (labels : Fin (Frame.ofMountain result).width → Label) (hLabels : StrictMono labels) :
    Keys.eval (edge.keyTemplate hOrdered D) labels ≤ Keys.eval bound.mappedKey labels :=
  Keys.eval_le_of_template_le _ _ labels hLabels bound.template_le

end ActualCopiedKeyBound

/-- The complete ordinary certificate is built with the packet's actual
completed-column history. No key or endpoint fact is supplied by callers. -/
theorem CopiedNodeOrigin.effective_key_bound
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    (edge : RealStoredEdge (Frame.ofMountain result))
    (packet : CopiedNodeOrigin p result edge.upper)
    (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (copy : EffectiveCopyOccurrence p packet.block packet.start packet.references source.lower
      (packet.before.push packet.column))
    (hSourceColumn : source.lower.1.val = packet.sourceColumn)
    (hLower : Frame.ref edge.lower = (copy.extend packet.preserved).outputRef) (D : Nat) :
    Nonempty (ActualCopiedKeyBound p result
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered edge D) := by
  have hBefore : source.lower.1.val < packet.sourceColumn + 1 := by omega
  obtain ⟨hParentColumn, hChildColumn⟩ := packet.after_state.preserved_effective_edge_columns
    packet.after_history hLast packet.start_run source hBefore copy packet.preserved edge hLower
  exact ⟨{
    block := packet.block
    block_pos := packet.block_pos
    source := source
    source_right := by rw [hSourceColumn]; exact packet.source_right
    parent_column := hParentColumn
    child_column := hChildColumn
    key_le := packet.after_state.preserved_effective_edge_nat_key_le
      packet.after_history hLast packet.start_run source hBefore copy packet.preserved hRun edge hLower D }⟩

/-- Ordinary output edges are fully ready for semantic splicing. The
remaining alternative keeps the real fill execution for its independent
control-edge argument; it is not replaced by a key-bound premise. -/
theorem Preparation.copied_edge_key_bound_or_fill
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hColumn : p.reduced.size ≤ edge.lower.1.val) (D : Nat) :
    Nonempty (ActualCopiedKeyBound p result
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered edge D) ∨
    (∃ packet : CopiedNodeOrigin p result edge.upper,
      FillUpperOrigin packet.data ((Frame.ofMountain result).cell edge.upper)) := by
  rcases p.copied_edge_source_or_fill hLast hCopies hRun edge hColumn with
    ⟨packet, source, copy, hSourceColumn, hLower⟩ | ⟨packet, hFill⟩
  · exact Or.inl (packet.effective_key_bound edge hLast hRun source copy hSourceColumn hLower D)
  · exact Or.inr ⟨packet, hFill⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualCopiedKeyBound.support_bound
#print axioms OmegaY.Expansion.ActualCopiedKeyBound.template_le
#print axioms OmegaY.Expansion.CopiedNodeOrigin.effective_key_bound
#print axioms OmegaY.Expansion.Preparation.copied_edge_key_bound_or_fill
