/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CanonicalDepthAntitone.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalEventProjection

/-!
# Depth decreases with the event index in a canonically built mountain

Each later event edge projects to a nonempty earlier ancestor path.
Finite column induction therefore bounds its later depth by its earlier
depth. This concerns vertical events inside one built mountain, not a
decreasing measure for successive omega-Y expansions.
-/

namespace OmegaY.Forests

open ZeroY ZeroY.Forest

theorem parentDepth_le_of_edge_ancestors
    {earlier later : ParentMap} (hEarlier : Leftward earlier) (hLater : Leftward later)
    {bound : Nat}
    (hEdges : ∀ node parent, node ≤ bound → later node = some parent →
      Ancestor earlier node parent)
    {node : Nat} (hNode : node ≤ bound) :
    parentDepth later node ≤ parentDepth earlier node := by
  induction node using Nat.strongRecOn with
  | ind node ih =>
    cases hParent : later node with
    | none => rw [parentDepth_none hParent]; exact Nat.zero_le _
    | some parent =>
      have hLeft := hLater hParent
      have hParentDepth := ih parent hLeft (hLeft.le.trans hNode)
      have hOldDepth : parentDepth earlier parent < parentDepth earlier node :=
        ancestor_depth_lt (parent := earlier) hEarlier (hEdges node parent hNode hParent)
      have hStep : parentDepth later node = parentDepth later parent + 1 :=
        parentDepth_some (parent := later) hLater hParent
      rw [hStep]
      omega

end OmegaY.Forests

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem build_event_parentDepth_antitone
    {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound start finish : Nat} (hBound : bound < mountain.size)
    (hOrder : start ≤ finish) (hFinish : finish ≤ (Frame.ofMountain mountain).lastEvent)
    {column : Nat} (hColumn : column ≤ bound) :
    parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound finish) column ≤
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound start) column := by
  have hNormal := build_normal_of_success hBuild
  apply Forests.parentDepth_le_of_edge_ancestors
    (eventParentMap_leftward hNormal.toOrdered hWidth hBound start)
    (eventParentMap_leftward hNormal.toOrdered hWidth hBound finish) (bound := bound) ?_ hColumn
  intro node parent hNode hEdge
  have hActual := hNormal.eventParentMap_some hWidth hBound hNode hEdge
  have hNodeWidth : node < mountain.size := hNode.trans_lt hBound
  have hParentLeft : parent < node := eventParentMap_leftward hNormal.toOrdered hWidth hBound finish hEdge
  have hParentWidth : parent < mountain.size := hParentLeft.trans hNodeWidth
  rw [eventFrontierNat_eq hNormal.toOrdered hWidth finish hNodeWidth,
    eventFrontierNat_eq hNormal.toOrdered hWidth finish hParentWidth] at hActual
  have hProjected := build_event_parent_map_projection hBuild hWidth hBound hOrder hFinish
    ⟨node, hNodeWidth⟩ hNode hActual
  simpa only [(eventFrontier_spec hNormal.toOrdered finish ⟨parent, hParentWidth⟩).1]
    using hProjected.ancestor

end OmegaY.Expansion

#print axioms OmegaY.Forests.parentDepth_le_of_edge_ancestors
#print axioms OmegaY.Expansion.build_event_parentDepth_antitone
