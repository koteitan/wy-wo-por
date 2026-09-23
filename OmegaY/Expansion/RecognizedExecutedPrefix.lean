/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RecognizedExecutedPrefix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RecognizedPrefix
import OmegaY.Expansion.HistoryRawInvariants
import OmegaY.Expansion.ActualCommonMarkerBands
import OmegaY.Expansion.TotalBottomLegs

/-!
# Canonical reconstruction of any recognized executed column prefix

The prefix may end partway through a copied block. Its real history gives
sums and raw geometry; complete preservation in the actual final output
gives tops and bottom legs. Recognition confined to this strictly earlier
complete prefix then reconstructs its canonical build. This does not
assume recognition of a later current column or the whole final output.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem PreservesColumns.mountainTops_reflect {before after : Mountain}
    (preserved : PreservesColumns before after) (hTops : MountainTops after) : MountainTops before := by
  intro column hColumn
  have hRead := preserved.column_read (Array.getElem?_eq_getElem hColumn)
  have hAfter := (Array.getElem?_eq_some_iff.mp hRead).1
  have hEq : after[column] = before[column] :=
    Option.some.inj ((Array.getElem?_eq_getElem hAfter).symm.trans hRead)
  exact hEq ▸ hTops column hAfter

theorem PreservesColumns.bottomLegs_reflect {before after : Mountain}
    (preserved : PreservesColumns before after) (hLegs : BottomLegs after) : BottomLegs before := by
  intro column hColumn
  have hRead := preserved.column_read (Array.getElem?_eq_getElem hColumn)
  have hAfter := (Array.getElem?_eq_some_iff.mp hRead).1
  have hEq : after[column] = before[column] :=
    Option.some.inj ((Array.getElem?_eq_getElem hAfter).symm.trans hRead)
  obtain ⟨bottom, hBottom, hLeft⟩ := hLegs column hAfter
  exact ⟨bottom, hEq ▸ hBottom, hLeft⟩

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block previousCopies next : Nat} {start ambient result : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range previousCopies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)
  (preserved : PreservesColumns ambient result)
  {input : List Nat} (hLegal : Canonical.Legal input) {copies : Nat}
  (hRun : expandDiagram input copies = .ok result)
  (hKnown : ∀ (node parent : (Frame.ofMountain result).Node),
    node.1.val < ambient.size → Real node →
    (Frame.ofMountain result).rawParent node = some parent →
      (Frame.ofMountain result).P node = some parent)

include s history hLast hStartRun preserved hLegal hRun hKnown

theorem DynamicBlockState.executed_prefix_normal : (Frame.ofMountain ambient).Normal := by
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hTops := preserved.mountainTops_reflect (OmegaY.Expansion.expandDiagram_equations hLegal hRun).2
  have hSums := s.mountainSums_of_start_run history hLast hStartRun
  have hRaw := s.mountainRawGeometry_of_start_run history hLast hStartRun
  have hSearch := preserved.rawParentSearch_of_left_recognition s.ambient_valid.toOrdered hValid.toOrdered hKnown
  exact normal_of_raw_geometry_parent_search s.ambient_valid hSums hTops hRaw
    (mountainParentSearch_of_rawParentSearch s.ambient_valid.toOrdered hSearch)

theorem DynamicBlockState.executed_prefix_reconstruct :
    Canonical.build (bottomValues ambient) = .ok ambient := by
  exact build_reconstruct s.ambient_valid
    (s.executed_prefix_normal history hLast hStartRun preserved hLegal hRun hKnown)
    (preserved.bottomLegs_reflect (OmegaY.Expansion.expandDiagram_bottom_legs hLegal hRun))

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.mountainTops_reflect
#print axioms OmegaY.Expansion.PreservesColumns.bottomLegs_reflect
#print axioms OmegaY.Expansion.DynamicBlockState.executed_prefix_normal
#print axioms OmegaY.Expansion.DynamicBlockState.executed_prefix_reconstruct
