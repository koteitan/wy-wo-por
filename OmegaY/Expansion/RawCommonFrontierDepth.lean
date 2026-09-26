/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawCommonFrontierDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawNumericSuffix

/-!+# Depth is constant while one actual raw frontier stays fixed

Raw row geometry and the father-upper bound keep the complete raw parent
chain on every cut at which its starting node is a frontier. Consequently
the depth of that node cannot depend on which such event is selected.
No numerical recognition or Normal assumption is imposed on the frame.
-/

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

theorem raw_event_parentDepth_of_common_frontier {F : Frame}
    (hF : F.Ordered) (hRaw : F.RawRowGeometry) (hFather : F.RawFatherUpperBound)
    (hWidth : 0 < F.width) {bound : Nat} (hBound : bound < F.width)
    {firstEvent secondEvent : Nat} {node : F.Node} (hNode : node.1.val ≤ bound)
    (hFirst : eventFrontier hF firstEvent node.1 = node)
    (hSecond : eventFrontier hF secondEvent node.1 = node) :
    parentDepth (eventParentMap hF hWidth bound secondEvent) node.1.val =
      parentDepth (eventParentMap hF hWidth bound firstEvent) node.1.val := by
  let firstMap : ParentMap := eventParentMap hF hWidth bound firstEvent
  let secondMap : ParentMap := eventParentMap hF hWidth bound secondEvent
  have hFirstLeft : Leftward firstMap := eventParentMap_leftward hF hWidth hBound firstEvent
  have hSecondLeft : Leftward secondMap := eventParentMap_leftward hF hWidth hBound secondEvent
  change parentDepth secondMap node.1.val = parentDepth firstMap node.1.val
  generalize hc : node.1.val = column
  induction column using Nat.strongRecOn generalizing node with
  | ind column ih =>
      have hFirstMap := eventParentMap_raw_at hF hWidth firstEvent node.1 hNode
      have hSecondMap := eventParentMap_raw_at hF hWidth secondEvent node.1 hNode
      rw [hFirst] at hFirstMap
      rw [hSecond] at hSecondMap
      change firstMap node.1.val = _ at hFirstMap
      change secondMap node.1.val = _ at hSecondMap
      cases hp : F.rawParent node with
      | none =>
          have hf : firstMap column = none := by
            simpa only [hc, hp, Option.map_none] using hFirstMap
          have hs : secondMap column = none := by
            simpa only [hc, hp, Option.map_none] using hSecondMap
          rw [parentDepth_none hs, parentDepth_none hf]
      | some parent =>
          have hFirstParent := eventFrontier_raw_parent_of_bound hF hRaw hFather firstEvent node.1
            (by rw [hFirst]; exact hp)
          have hSecondParent := eventFrontier_raw_parent_of_bound hF hRaw hFather secondEvent node.1
            (by rw [hSecond]; exact hp)
          have hf : firstMap column = some parent.1.val := by
            simpa only [hc, hp, Option.map_some] using hFirstMap
          have hs : secondMap column = some parent.1.val := by
            simpa only [hc, hp, Option.map_some] using hSecondMap
          have hLess : parent.1.val < column := by
            simpa only [hc] using rawParent_column_lt hF hp
          have hParentBound : parent.1.val ≤ bound := by omega
          rw [parentDepth_some hSecondLeft hs, parentDepth_some hFirstLeft hf,
            ih parent.1.val hLess hParentBound hFirstParent hSecondParent rfl]

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.raw_event_parentDepth_of_common_frontier
