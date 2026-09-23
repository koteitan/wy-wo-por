/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RecognizedPrefix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.TrivialSearchRecognition
import OmegaY.Expansion.BlocksBottomLegs

/-!
# Canonical complete prefixes from strict-left recognition

Recognition already proved on an ambient left prefix reflects to that
prefix by executable search locality. For a real completed-block prefix,
the independent sums, tops, raw geometry and bottom legs then reconstruct
its actual canonical build. This does not assume the ambient graph normal
or recognize any node in a current column outside the prefix.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem PreservesColumns.rawParentSearch_of_left_recognition
    {before after : Mountain} (hPreserved : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered)
    (hAfter : (Frame.ofMountain after).Ordered)
    (hKnown : ∀ (node parent : (Frame.ofMountain after).Node),
      node.1.val < before.size → Real node →
      (Frame.ofMountain after).rawParent node = some parent →
        (Frame.ofMountain after).P node = some parent) :
    (Frame.ofMountain before).RawParentSearch := by
  intro node parent hReal hRaw
  have hMapped := hKnown (hPreserved.mapNode node) (hPreserved.mapNode parent)
    (by rw [hPreserved.mapNode_column]; exact node.1.isLt)
    (hPreserved.mapNode_real hReal) (hPreserved.mapNode_rawParent hRaw)
  apply (Executable.findParent_ref_iff hBefore node parent).mp
  rw [← hPreserved.findParent node.1.isLt]
  simpa only [hPreserved.mapNode_ref] using
    (Executable.findParent_ref_iff hAfter _ _).mpr hMapped

theorem Preparation.blocks_normal_of_left_recognition
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {start ambient : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hPreserved : PreservesColumns start ambient)
    (hAmbient : (Frame.ofMountain ambient).Ordered)
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent) :
    (Frame.ofMountain start).Normal := by
  obtain ⟨built, hBuilt, hReady, hSums, hTops⟩ := p.blocks_equations hLast copies
  have he : built = start := Except.ok.inj (hBuilt.symm.trans hRun)
  subst built
  exact normal_of_raw_geometry_parent_search hReady.valid hSums hTops
    (p.blocks_raw_geometry_of_run hLast hRun)
    (mountainParentSearch_of_rawParentSearch hReady.valid.toOrdered
      (hPreserved.rawParentSearch_of_left_recognition hReady.valid.toOrdered hAmbient hKnown))

/-- The earlier-block canonical build is obtained from the induction
hypothesis on its columns, not assumed as an expansion invariant. -/
theorem Preparation.blocks_reconstruct_of_left_recognition
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {start ambient : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hPreserved : PreservesColumns start ambient)
    (hAmbient : (Frame.ofMountain ambient).Ordered)
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent) :
    ∃ values, valuesOf start = .ok values ∧ Canonical.build values = .ok start := by
  obtain ⟨built, hBuilt, hReady⟩ := p.blocks_total hLast copies
  have he : built = start := Except.ok.inj (hBuilt.symm.trans hRun)
  subst built
  obtain ⟨values, hValues, _, _⟩ := valuesOf_total_legal hReady.valid
  exact ⟨values, hValues, build_reconstruct_of_valuesOf hReady.valid
    (p.blocks_normal_of_left_recognition hLast hRun hPreserved hAmbient hKnown)
    (p.blocks_bottom_legs hLast copies hRun) hValues⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.rawParentSearch_of_left_recognition
#print axioms OmegaY.Expansion.Preparation.blocks_normal_of_left_recognition
#print axioms OmegaY.Expansion.Preparation.blocks_reconstruct_of_left_recognition
