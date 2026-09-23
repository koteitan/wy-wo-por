/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Forests/RefinedForestDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Forests
import Mathlib.Order.Hom.Basic

/-!
# Finite parent paths and a refined root's depth contribution

These statements use actual `ParentMap` edge equations and finite paths.
No depth equality is an input. A strictly increasing column embedding
preserves each source edge above a distinguished root. The target root may
have a longer path to the preserved source tail; that entire change is
shared by every node in the source root cone.

This is a structural forest result. Supplying these edge and root-path
equations for an actual omega-Y copy remains a separate obligation.
-/

namespace OmegaY.Forests

open ZeroY ZeroY.Forest

/-- A finite path with an explicit number of genuine parent edges. -/
inductive ParentSteps (parent : ParentMap) : Nat → Nat → Nat → Prop
  | nil (node : Nat) : ParentSteps parent node node 0
  | cons {node next endpoint length : Nat} (edge : parent node = some next)
      (tail : ParentSteps parent next endpoint length) :
      ParentSteps parent node endpoint (length + 1)

theorem ParentSteps.trans {parent : ParentMap} {a b c m n : Nat}
    (first : ParentSteps parent a b m) (second : ParentSteps parent b c n) :
    ParentSteps parent a c (m + n) := by
  induction first with
  | nil => simpa using second
  | cons hEdge _ ih =>
    have hNew := ParentSteps.cons hEdge (ih second)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hNew

theorem ParentSteps.depth {parent : ParentMap} (hLeft : Leftward parent)
    {node endpoint length : Nat} (path : ParentSteps parent node endpoint length) :
    parentDepth parent node = parentDepth parent endpoint + length := by
  induction path with
  | nil => omega
  | cons hEdge _ ih => rw [parentDepth_some hLeft hEdge, ih]; omega

theorem ParentSteps.endpoint_le {parent : ParentMap} (hLeft : Leftward parent)
    {node endpoint length : Nat} (path : ParentSteps parent node endpoint length) :
    endpoint ≤ node := by
  induction path with
  | nil => exact le_rfl
  | cons hEdge _ ih => exact ih.trans (hLeft hEdge).le

theorem ParentSteps.eq_or_ancestor {parent : ParentMap} {node endpoint length : Nat}
    (path : ParentSteps parent node endpoint length) :
    node = endpoint ∨ Ancestor parent node endpoint := by
  induction path with
  | nil => exact Or.inl rfl
  | cons hEdge _ ih =>
    rcases ih with rfl | hPath
    · exact Or.inr (.single hEdge)
    · exact Or.inr (ancestor_trans (.single hEdge) hPath)

theorem parentSteps_of_ancestor {parent : ParentMap} {node endpoint : Nat}
    (path : Ancestor parent node endpoint) :
    ∃ length, ParentSteps parent node endpoint (length + 1) := by
  induction path with
  | single hEdge => exact ⟨0, .cons hEdge (.nil _)⟩
  | tail _ hEdge ih =>
    obtain ⟨length, hPath⟩ := ih
    exact ⟨length + 1, by simpa using hPath.trans (.cons hEdge (.nil _))⟩

/-- The reflexive root cone uses actual source-parent paths. -/
def ParentCone (source : ParentMap) (root node : Nat) : Prop :=
  node = root ∨ Ancestor source node root

theorem parentSteps_of_cone {source : ParentMap} {root node : Nat}
    (hCone : ParentCone source root node) :
    ∃ length, ParentSteps source node root length := by
  rcases hCone with rfl | hPath
  · exact ⟨0, .nil _⟩
  · obtain ⟨length, hLength⟩ := parentSteps_of_ancestor hPath
    exact ⟨length + 1, hLength⟩

/-- Every source edge before reaching the root maps to one actual target
edge. No condition on the target root's outgoing edge is imposed. -/
theorem ParentSteps.map_root_cone {source target : ParentMap}
    (hSource : Leftward source) (embed : Nat ↪o Nat) {root : Nat}
    (hEdges : ∀ node parent, root < node → ParentCone source root node →
      source node = some parent → target (embed node) = some (embed parent))
    {node length : Nat} (path : ParentSteps source node root length) :
    ParentSteps target (embed node) (embed root) length := by
  induction path with
  | nil => exact .nil _
  | @cons node parent root length hEdge tail ih =>
    have hRoot : root < node := (tail.endpoint_le hSource).trans_lt (hSource hEdge)
    exact .cons (hEdges node parent hRoot (.inr (by
      rcases tail.eq_or_ancestor with he | hPath
      · exact he ▸ Relation.TransGen.single hEdge
      · exact ancestor_trans (.single hEdge) hPath)) hEdge) (ih hEdges)

/-- Root substitution contributes the same crossed-sum difference to every
source node in that root cone. In particular there is no natural subtraction. -/
theorem depth_balance_of_root_edges {source target : ParentMap}
    (hSource : Leftward source) (hTarget : Leftward target)
    (embed : Nat ↪o Nat) {root node : Nat}
    (hEdges : ∀ current parent, root < current → ParentCone source root current →
      source current = some parent → target (embed current) = some (embed parent))
    (hCone : ParentCone source root node) :
    parentDepth target (embed node) + parentDepth source root =
      parentDepth source node + parentDepth target (embed root) := by
  obtain ⟨length, path⟩ := parentSteps_of_cone hCone
  have hOld : parentDepth source node = parentDepth source root + length := path.depth hSource
  have hNew : parentDepth target (embed node) = parentDepth target (embed root) + length :=
    (path.map_root_cone hSource embed hEdges).depth hTarget
  omega

/-- A preserved finite left prefix supplies equality of its tail depths
from direct parent reads, including genuine `none` endpoints. -/
theorem depth_eq_of_embedded_prefix {source target : ParentMap}
    (hSource : Leftward source) (hTarget : Leftward target) (embed : Nat ↪o Nat)
    {bound : Nat}
    (hEdges : ∀ node, node ≤ bound → target (embed node) = (source node).map embed)
    {node : Nat} (hNode : node ≤ bound) :
    parentDepth target (embed node) = parentDepth source node := by
  induction node using Nat.strongRecOn with
  | ind node ih =>
    cases hParent : source node with
    | none =>
      have hNone : target (embed node) = none := by simpa only [hParent, Option.map_none] using hEdges node hNode
      rw [parentDepth_none hNone, parentDepth_none hParent]
    | some parent =>
      have hSome : target (embed node) = some (embed parent) := by
        simpa only [hParent, Option.map_some] using hEdges node hNode
      rw [parentDepth_some hTarget hSome, parentDepth_some hSource hParent,
        ih parent (hSource hParent) ((hSource hParent).le.trans hNode)]

/-- Refining the root's original edge into `extra + 1` actual target edges
adds exactly `extra` to every depth above that root. The old root-parent
tail is supplied by its direct edge equations, not by a depth assumption. -/
theorem depth_add_of_refined_root {source target : ParentMap}
    (hSource : Leftward source) (hTarget : Leftward target)
    (embed : Nat ↪o Nat) {root rootParent node extra : Nat}
    (hRoot : source root = some rootParent)
    (hTail : ∀ current, current ≤ rootParent →
      target (embed current) = (source current).map embed)
    (hRootPath : ParentSteps target (embed root) (embed rootParent) (extra + 1))
    (hEdges : ∀ current parent, root < current → ParentCone source root current →
      source current = some parent → target (embed current) = some (embed parent))
    (hCone : ParentCone source root node) :
    parentDepth target (embed node) = parentDepth source node + extra := by
  have hTailDepth : parentDepth target (embed rootParent) = parentDepth source rootParent :=
    depth_eq_of_embedded_prefix hSource hTarget embed hTail (Nat.le_refl rootParent)
  have hRootDepth : parentDepth target (embed root) = parentDepth target (embed rootParent) + (extra + 1) :=
    hRootPath.depth hTarget
  have hOldRoot : parentDepth source root = parentDepth source rootParent + 1 :=
    parentDepth_some hSource hRoot
  have hBalance : parentDepth target (embed node) + parentDepth source root =
      parentDepth source node + parentDepth target (embed root) :=
    depth_balance_of_root_edges hSource hTarget embed hEdges hCone
  omega

/-- The source-root-top case uses an actual target path to an actual top.
It allows the target reference root to have positive depth. -/
theorem depth_add_of_refined_top {source target : ParentMap}
    (hSource : Leftward source) (hTarget : Leftward target)
    (embed : Nat ↪o Nat) {root targetTop node extra : Nat}
    (hRoot : source root = none) (hTop : target targetTop = none)
    (hRootPath : ParentSteps target (embed root) targetTop extra)
    (hEdges : ∀ current parent, root < current → ParentCone source root current →
      source current = some parent → target (embed current) = some (embed parent))
    (hCone : ParentCone source root node) :
    parentDepth target (embed node) = parentDepth source node + extra := by
  have hRootDepth : parentDepth target (embed root) = parentDepth target targetTop + extra :=
    hRootPath.depth hTarget
  have hTopDepth : parentDepth target targetTop = 0 := parentDepth_none hTop
  have hOldRoot : parentDepth source root = 0 := parentDepth_none hRoot
  have hBalance : parentDepth target (embed node) + parentDepth source root =
      parentDepth source node + parentDepth target (embed root) :=
    depth_balance_of_root_edges hSource hTarget embed hEdges hCone
  omega

/-- An actual nonempty root-to-old-parent path supplies a single
nonnegative increment for the entire cone. The source-top case needs no
connection assumption. Path length is obtained from the actual ancestor
relation; the increment is not a supplied depth difference. -/
theorem depth_increment_of_root_connection {source target : ParentMap}
    (hSource : Leftward source) (hTarget : Leftward target)
    (embed : Nat ↪o Nat) {root : Nat}
    (hConnection : ∀ parent, source root = some parent →
      Ancestor target (embed root) (embed parent))
    (hTail : ∀ parent, source root = some parent → ∀ current, current ≤ parent →
      target (embed current) = (source current).map embed)
    (hEdges : ∀ current parent, root < current → ParentCone source root current →
      source current = some parent → target (embed current) = some (embed parent)) :
    ∃ extra, ∀ node, ParentCone source root node →
      parentDepth target (embed node) = parentDepth source node + extra := by
  cases hRoot : source root with
  | none =>
    refine ⟨parentDepth target (embed root), ?_⟩
    intro node hCone
    have hBalance : parentDepth target (embed node) + parentDepth source root =
        parentDepth source node + parentDepth target (embed root) :=
      depth_balance_of_root_edges hSource hTarget embed hEdges hCone
    rw [parentDepth_none hRoot, Nat.add_zero] at hBalance
    exact hBalance
  | some parent =>
    obtain ⟨extra, hPath⟩ := parentSteps_of_ancestor (hConnection parent hRoot)
    exact ⟨extra, fun _ hCone => depth_add_of_refined_root hSource hTarget embed
      hRoot (hTail parent hRoot) hPath hEdges hCone⟩

end OmegaY.Forests

#print axioms OmegaY.Forests.ParentSteps.trans
#print axioms OmegaY.Forests.ParentSteps.depth
#print axioms OmegaY.Forests.ParentSteps.endpoint_le
#print axioms OmegaY.Forests.ParentSteps.eq_or_ancestor
#print axioms OmegaY.Forests.parentSteps_of_ancestor
#print axioms OmegaY.Forests.parentSteps_of_cone
#print axioms OmegaY.Forests.ParentSteps.map_root_cone
#print axioms OmegaY.Forests.depth_balance_of_root_edges
#print axioms OmegaY.Forests.depth_eq_of_embedded_prefix
#print axioms OmegaY.Forests.depth_add_of_refined_root
#print axioms OmegaY.Forests.depth_add_of_refined_top
#print axioms OmegaY.Forests.depth_increment_of_root_connection
