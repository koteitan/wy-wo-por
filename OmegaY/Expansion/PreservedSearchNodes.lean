/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedSearchNodes.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreservedFrameNodes
import OmegaY.Canonical.Locality

/-!
# Search results in a preserved complete left prefix

The actual searches inspect only the current cell and earlier columns.
Thus an already established source-prefix Q or P result survives later
complete-column appends. This is a locality statement, not numerical-parent
recognition for the newly appended columns.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem PreservesColumns.nextCandidate {before after : Mountain}
    (h : PreservesColumns before after) {current : Ref} (hColumn : current.column < before.size) :
    nextCandidate after current = nextCandidate before current := by
  apply nextCandidate_eq_of_columns
  exact fun c hc => h c (hc.trans_lt hColumn)

theorem PreservesColumns.findParent {before after : Mountain}
    (h : PreservesColumns before after) {current : Ref} (hColumn : current.column < before.size) :
    findParent after current = findParent before current := by
  apply findParent_eq_of_columns
  exact fun c hc => h c (hc.trans_lt hColumn)

theorem PreservesColumns.mapNode_Q {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    {node candidate : (Frame.ofMountain before).Node}
    (hQ : (Frame.ofMountain before).Q node = some candidate) :
    (Frame.ofMountain after).Q (h.mapNode node) = some (h.mapNode candidate) := by
  apply (Executable.nextCandidate_ref_iff hAfter _ _).mp
  rw [h.mapNode_ref, h.mapNode_ref, h.nextCandidate node.1.isLt]
  exact (Executable.nextCandidate_ref_iff hBefore _ _).mpr hQ

theorem PreservesColumns.mapNode_P {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    {node parent : (Frame.ofMountain before).Node}
    (hP : (Frame.ofMountain before).P node = some parent) :
    (Frame.ofMountain after).P (h.mapNode node) = some (h.mapNode parent) := by
  apply (Executable.findParent_ref_iff hAfter _ _).mp
  rw [h.mapNode_ref, h.mapNode_ref, h.findParent node.1.isLt]
  exact (Executable.findParent_ref_iff hBefore _ _).mpr hP

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.nextCandidate
#print axioms OmegaY.Expansion.PreservesColumns.findParent
#print axioms OmegaY.Expansion.PreservesColumns.mapNode_Q
#print axioms OmegaY.Expansion.PreservesColumns.mapNode_P
