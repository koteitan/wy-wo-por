/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSpliceFacts.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSpliceIndices
import OmegaY.Splice.IteratedReservoirs

/-! The finite graph and reserves contain exactly the indicated actual
source edges. Their dimensions are those proved from the executed block
loop. This module also classifies retained graph edges geometrically. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem spliceAtom_eq_of_fields {m n : Nat} {left right : Model.InternalAtom m n}
    (hKey : left.key = right.key) (hParent : left.parent = right.parent)
    (hChild : left.child = right.child) : left = right := by
  cases left
  cases right
  cases hKey
  cases hParent
  cases hChild
  rfl

theorem mapAtom_eq_of_pointwise {m n k : Nat} (left right : Fin n → Fin k)
    (hLeft : StrictMono left) (hRight : StrictMono right)
    (hMaps : ∀ column, left column = right column) (atom : Model.InternalAtom m n) :
    Splice.mapAtom left hLeft atom = Splice.mapAtom right hRight atom := by
  have he : left = right := funext hMaps
  subst right
  rfl

theorem PreservesColumns.storedEdge_atom {before after : Mountain}
    (preserved : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    (edge : RealStoredEdge (Frame.ofMountain before)) (D : Nat) :
    (preserved.storedEdge edge).atom hAfter D =
      Splice.mapAtom preserved.keyColumn preserved.keyColumn_strictMono (edge.atom hBefore D) := by
  apply spliceAtom_eq_of_fields
  · exact preserved.storedEdge_keyTemplate hBefore hAfter edge D
  · exact Fin.ext (preserved.mapNode_column edge.parent)
  · exact Fin.ext (preserved.mapNode_column edge.lower)

noncomputable def actualStoredEdges (F : Frame) : List (RealStoredEdge F) :=
  (Finset.univ : Finset (RealStoredEdge F)).toList

@[simp] theorem mem_actualStoredEdges (F : Frame) (edge : RealStoredEdge F) :
    edge ∈ actualStoredEdges F := by classical simp [actualStoredEdges]

namespace Preparation
variable {front : List Nat} {last : Nat} (p : Preparation front last)

noncomputable def spliceEdgeAtom (hLast : 1 < last) (D block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast block))) :
    Model.InternalAtom (D + 1) (Splice.blockWidth front.length p.root.column block) :=
  Splice.mapAtom (Fin.cast (p.spliceMountain_size hLast block)) (Splice.fin_cast_strictMono _)
    (edge.atom (p.spliceMountain_valid hLast block).toOrdered D)

noncomputable def spliceGraph (hLast : 1 < last) (D block : Nat) :
    List (Model.InternalAtom (D + 1) (Splice.blockWidth front.length p.root.column block)) :=
  (actualStoredEdges (Frame.ofMountain (p.spliceMountain hLast block))).map
    (p.spliceEdgeAtom hLast D block)

@[simp] theorem spliceEdgeAtom_mem (hLast : 1 < last) (D block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast block))) :
    p.spliceEdgeAtom hLast D block edge ∈ p.spliceGraph hLast D block :=
  List.mem_map.mpr ⟨edge, mem_actualStoredEdges _ _, rfl⟩

noncomputable def initialSpliceEdgeAtom (D : Nat)
    (edge : RealStoredEdge (Frame.ofMountain p.initial.pop)) : Model.InternalAtom (D + 1) front.length :=
  Splice.mapAtom (Fin.cast p.initial_pop_size) (Splice.fin_cast_strictMono _)
    (edge.atom p.initial_valid.pop.toOrdered D)

noncomputable def initialSpliceFacts (D : Nat) : List (Model.InternalAtom (D + 1) front.length) :=
  (actualStoredEdges (Frame.ofMountain p.initial.pop)).map (p.initialSpliceEdgeAtom D)

@[simp] theorem initialSpliceEdgeAtom_mem (D : Nat)
    (edge : RealStoredEdge (Frame.ofMountain p.initial.pop)) :
    p.initialSpliceEdgeAtom D edge ∈ p.initialSpliceFacts D :=
  List.mem_map.mpr ⟨edge, mem_actualStoredEdges _ _, rfl⟩

noncomputable def spliceFacts (D block : Nat) :
    List (Model.InternalAtom (D + 1) (Splice.blockWidth front.length p.root.column block)) :=
  (p.initialSpliceFacts D).map
    (Splice.mapAtom (Splice.blockSource p.root_before_last block)
      (Splice.blockSource_strictMono p.root_before_last block))

noncomputable def spliceLocalEdgeAtom (hLast : 1 < last) (D block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1)))) :
    Model.InternalAtom (D + 1) (Splice.width (Splice.blockCut p.root_before_last block)) :=
  Splice.mapAtom (Fin.cast (Splice.width_blockCut p.root_before_last block).symm)
    (Splice.fin_cast_strictMono _) (p.spliceEdgeAtom hLast D (block + 1) edge)

theorem retained_splice_atom (hLast : 1 < last) (D block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast block))) :
    p.spliceLocalEdgeAtom hLast D block
        ((p.spliceMountain_preserved_next hLast block).storedEdge edge) =
      Splice.mapAtom (Splice.old (Splice.blockCut p.root_before_last block))
        (Splice.old_strictMono _) (p.spliceEdgeAtom hLast D block edge) := by
  apply spliceAtom_eq_of_fields
  · change Keys.relabel (Keys.relabel
        (((p.spliceMountain_preserved_next hLast block).storedEdge edge).keyTemplate
          (p.spliceMountain_valid hLast (block + 1)).toOrdered D)
        (Fin.cast (p.spliceMountain_size hLast (block + 1))))
        (Fin.cast (Splice.width_blockCut p.root_before_last block).symm) =
      Keys.relabel (Keys.relabel (edge.keyTemplate (p.spliceMountain_valid hLast block).toOrdered D)
        (Fin.cast (p.spliceMountain_size hLast block)))
        (Splice.old (Splice.blockCut p.root_before_last block))
    rw [(p.spliceMountain_preserved_next hLast block).storedEdge_keyTemplate
      (p.spliceMountain_valid hLast block).toOrdered (p.spliceMountain_valid hLast (block + 1)).toOrdered]
    funext i
    simp only [Keys.relabel]
    cases (edge.keyTemplate (p.spliceMountain_valid hLast block).toOrdered D) i with
    | none => rfl
    | some column => exact congrArg some (Fin.ext rfl)
  · exact Fin.ext ((p.spliceMountain_preserved_next hLast block).mapNode_column edge.parent)
  · exact Fin.ext ((p.spliceMountain_preserved_next hLast block).mapNode_column edge.lower)

theorem retained_splice_classified (hLast : 1 < last) (D block : Nat)
    (N : List (Model.TopAtom (D + 1) (Splice.blockWidth front.length p.root.column block)))
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1))))
    (hColumn : edge.lower.1.val < (p.spliceMountain hLast block).size) :
    Splice.ReservoirClassified (Splice.blockCut p.root_before_last block)
      (p.spliceGraph hLast D block) (p.spliceFacts D block) N
      (p.spliceLocalEdgeAtom hLast D block edge) := by
  obtain ⟨oldEdge, hEdge⟩ := (p.spliceMountain_preserved_next hLast block).storedEdge_preimage
    (p.spliceMountain_valid hLast (block + 1)).toOrdered edge hColumn
  exact Or.inl ⟨p.spliceEdgeAtom hLast D block oldEdge, p.spliceEdgeAtom_mem hLast D block oldEdge,
    hEdge ▸ p.retained_splice_atom hLast D block oldEdge⟩

end Preparation

namespace RootGeometry
variable {front : List Nat} {last : Nat} {p : Preparation front last}

noncomputable def initialSpliceVirtualAtom (g : RootGeometry p) (D : Nat) (edge : g.LowerEdge) :
    Model.TopAtom (D + 1) front.length :=
  Splice.mapTop (Fin.cast p.initial_pop_size) (g.lowerAtom D edge)

noncomputable def initialSpliceVirtualFacts (g : RootGeometry p) (D : Nat) :
    List (Model.TopAtom (D + 1) front.length) := by
  classical
  letI : Fintype g.LowerEdge := by unfold LowerEdge; infer_instance
  exact (Finset.univ : Finset g.LowerEdge).toList.map (g.initialSpliceVirtualAtom D)

@[simp] theorem initialSpliceVirtualAtom_mem (g : RootGeometry p) (D : Nat) (edge : g.LowerEdge) :
    g.initialSpliceVirtualAtom D edge ∈ g.initialSpliceVirtualFacts D := by
  classical
  exact List.mem_map.mpr ⟨edge, by simp, rfl⟩

theorem mem_initialSpliceVirtualFacts_iff (g : RootGeometry p) (D : Nat)
    (atom : Model.TopAtom (D + 1) front.length) :
    atom ∈ g.initialSpliceVirtualFacts D ↔ ∃ edge : g.LowerEdge,
      g.initialSpliceVirtualAtom D edge = atom := by
  classical
  simp only [initialSpliceVirtualFacts, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]

noncomputable def initialSpliceControl (g : RootGeometry p) (D : Nat) :
    Model.TopAtom (D + 1) front.length :=
  Splice.mapTop (Fin.cast p.initial_pop_size) (g.controlAtom D)

noncomputable def spliceVirtualFacts (g : RootGeometry p) (D block : Nat) :
    List (Model.TopAtom (D + 1) (Splice.blockWidth front.length p.root.column block)) :=
  (g.initialSpliceVirtualFacts D).map (Splice.mapTop (Splice.blockSource p.root_before_last block))

noncomputable def spliceControl (g : RootGeometry p) (D block : Nat) :
    Model.TopAtom (D + 1) (Splice.blockWidth front.length p.root.column block) :=
  Splice.mapTop (Splice.blockSource p.root_before_last block) (g.initialSpliceControl D)

theorem initialSpliceControl_parent (g : RootGeometry p) (D : Nat) :
    (g.initialSpliceControl D).parent = ⟨p.root.column, p.root_before_last⟩ :=
  Fin.ext (congrArg Ref.column g.root_ref)

theorem spliceControl_parent (g : RootGeometry p) (D block : Nat) :
    (g.spliceControl D block).parent = Splice.blockCut p.root_before_last block := by
  change Splice.blockSource p.root_before_last block (g.initialSpliceControl D).parent = _
  rw [g.initialSpliceControl_parent, Splice.blockSource_root]

end RootGeometry
end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.storedEdge_atom
#print axioms OmegaY.Expansion.Preparation.retained_splice_classified
#print axioms OmegaY.Expansion.RootGeometry.spliceControl_parent
