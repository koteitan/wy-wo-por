/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DepthWordStart.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.HighEventDepthWord
import OmegaY.Expansion.CutDepthWords

/-!
# Equal-prefix removal and complete-prefix bounds for actual depth words

A strict word can be moved to a later start only after proving equality
at every removed event. Changing the column cutoff beyond both compared
columns preserves their complete parent depths. These are explicit
converters; actual prefix equality is supplied by copying theorems.
-/

namespace OmegaY.Forests

open ZeroY

theorem depthWordEq_trim_equal_prefix {F : Nat → ParentMap}
    {early later finish left right : Nat} (hOrder : early ≤ later)
    (hPrefix : ∀ event, early ≤ event → event < later → eventDepth F event left = eventDepth F event right) :
    DepthWordEq F early finish left right ↔ DepthWordEq F later finish left right := by
  constructor
  · exact fun h event hStart hEnd => h event (hOrder.trans hStart) hEnd
  · intro h event hStart hEnd
    by_cases hBefore : event < later
    · exact hPrefix event hStart hBefore
    · exact h event (le_of_not_gt hBefore) hEnd

theorem depthWordLt_trim_equal_prefix {F : Nat → ParentMap}
    {early later finish left right : Nat} (hOrder : early ≤ later)
    (hPrefix : ∀ event, early ≤ event → event < later → eventDepth F event left = eventDepth F event right) :
    DepthWordLt F early finish left right ↔ DepthWordLt F later finish left right := by
  constructor
  · rintro ⟨event, hStart, hEnd, hEarlier, hStrict⟩
    have hLater : later ≤ event := by
      by_contra hn
      exact (Nat.ne_of_lt hStrict) (hPrefix event hStart (lt_of_not_ge hn))
    exact ⟨event, hLater, hEnd, fun before hb hbe => hEarlier before (hOrder.trans hb) hbe, hStrict⟩
  · rintro ⟨event, hStart, hEnd, hEarlier, hStrict⟩
    refine ⟨event, hOrder.trans hStart, hEnd, ?_, hStrict⟩
    intro before hb hbe
    by_cases hBefore : before < later
    · exact hPrefix before hb hBefore
    · exact hEarlier before (le_of_not_gt hBefore) hbe

theorem depthWordLe_trim_equal_prefix {F : Nat → ParentMap}
    {early later finish left right : Nat} (hOrder : early ≤ later)
    (hPrefix : ∀ event, early ≤ event → event < later → eventDepth F event left = eventDepth F event right) :
    DepthWordLe F early finish left right ↔ DepthWordLe F later finish left right :=
  or_congr (depthWordEq_trim_equal_prefix hOrder hPrefix) (depthWordLt_trim_equal_prefix hOrder hPrefix)

theorem depthWordEq_of_eventDepth_eq {F G : Nat → ParentMap}
    {start finish left right : Nat}
    (hLeft : ∀ event, eventDepth F event left = eventDepth G event left)
    (hRight : ∀ event, eventDepth F event right = eventDepth G event right) :
    DepthWordEq F start finish left right ↔ DepthWordEq G start finish left right := by
  constructor
  · intro h event hs he
    rw [← hLeft, ← hRight]
    exact h event hs he
  · intro h event hs he
    rw [hLeft, hRight]
    exact h event hs he

theorem depthWordLt_of_eventDepth_eq {F G : Nat → ParentMap}
    {start finish left right : Nat}
    (hLeft : ∀ event, eventDepth F event left = eventDepth G event left)
    (hRight : ∀ event, eventDepth F event right = eventDepth G event right) :
    DepthWordLt F start finish left right ↔ DepthWordLt G start finish left right := by
  constructor
  · rintro ⟨event, hs, he, hEarlier, hStrict⟩
    refine ⟨event, hs, he, ?_, ?_⟩
    · intro before hb hbe
      rw [← hLeft, ← hRight]
      exact hEarlier before hb hbe
    · rwa [← hLeft, ← hRight]
  · rintro ⟨event, hs, he, hEarlier, hStrict⟩
    refine ⟨event, hs, he, ?_, ?_⟩
    · intro before hb hbe
      rw [hLeft, hRight]
      exact hEarlier before hb hbe
    · rwa [hLeft, hRight]

end OmegaY.Forests

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

theorem depthWord_bound_iff {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    (boundedInitial fullInitial : ParentMap) {bound left right start finish : Nat}
    (hBound : bound < F.width) (hLeft : left ≤ bound) (hRight : right ≤ bound) :
    let bounded := F.frontierForests boundedInitial (eventFrontierNat hF hWidth) bound
    let full := F.frontierForests fullInitial (eventFrontierNat hF hWidth) (F.width - 1)
    (Forests.DepthWordEq bounded start finish left right ↔ Forests.DepthWordEq full start finish left right) ∧
    (Forests.DepthWordLt bounded start finish left right ↔ Forests.DepthWordLt full start finish left right) ∧
    (Forests.DepthWordLe bounded start finish left right ↔ Forests.DepthWordLe full start finish left right) := by
  have hL : ∀ event, Forests.eventDepth
      (F.frontierForests boundedInitial (eventFrontierNat hF hWidth) bound) event left =
      Forests.eventDepth (F.frontierForests fullInitial (eventFrontierNat hF hWidth) (F.width - 1)) event left :=
    fun event => eventParentMap_depth_bound hF hWidth hBound hLeft event
  have hR : ∀ event, Forests.eventDepth
      (F.frontierForests boundedInitial (eventFrontierNat hF hWidth) bound) event right =
      Forests.eventDepth (F.frontierForests fullInitial (eventFrontierNat hF hWidth) (F.width - 1)) event right :=
    fun event => eventParentMap_depth_bound hF hWidth hBound hRight event
  exact ⟨Forests.depthWordEq_of_eventDepth_eq hL hR,
    Forests.depthWordLt_of_eventDepth_eq hL hR,
    or_congr (Forests.depthWordEq_of_eventDepth_eq hL hR) (Forests.depthWordLt_of_eventDepth_eq hL hR)⟩

end OmegaY.Geometry.Frame

#print axioms OmegaY.Forests.depthWordEq_trim_equal_prefix
#print axioms OmegaY.Forests.depthWordLt_trim_equal_prefix
#print axioms OmegaY.Forests.depthWordLe_trim_equal_prefix
#print axioms OmegaY.Geometry.Frame.depthWord_bound_iff
