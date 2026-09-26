/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawGeometryCounterexample.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawSearchReconstruction
import OmegaY.Expansion.RawFrontier
import Mathlib.Tactic.FinCases

/-!
# A noncanonical artificial mountain with raw B and raw D

This finite mountain is NOT asserted to be an actual expansion output.
It separates raw geometry and additive reconstruction from numerical
parent-search recovery. Its bottom values are [1, 2, 3], but its last
bottom stores column zero as its raw parent while numerical P chooses
column one.
-/

namespace OmegaY.Expansion.RawGeometryCounterexample

open Canonical Geometry

def col0 : Column := #[phantom, ⟨1, 1, none⟩]
def col1 : Column := #[phantom, ⟨1, 2, some ⟨0, 0⟩⟩, ⟨2, 1, some ⟨0, 1⟩⟩]
def col2 : Column := #[phantom, ⟨1, 3, some ⟨1, 0⟩⟩, ⟨2, 2, some ⟨0, 1⟩⟩,
  ⟨Row.ofList [0, 1], 1, some ⟨0, 1⟩⟩]
def mountain : Mountain := #[col0, col1, col2]
def frame : Frame := Frame.ofMountain mountain

def lastBottom : frame.Node := ⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩
def rawFather : frame.Node := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
def trueFather : frame.Node := ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩

theorem raw_parent : frame.rawParent lastBottom = some rawFather := by decide
theorem true_parent : frame.P lastBottom = some trueFather := by decide
theorem executable_parent : findParent mountain ⟨2, 1⟩ = .ok ⟨1, 1⟩ := by decide

theorem raw_father_bound : frame.RawFatherUpperBound := by
  have hTop : ∀ u parent : frame.Node, Frame.Real u → frame.rawParent u = some parent →
      frame.upper parent = none := by unfold Frame.Real; decide
  intro u parent upper parentUpper hReal hParent _ hParentUpper
  rw [hTop u parent hReal hParent] at hParentUpper
  cases hParentUpper

theorem not_raw_parent_search : ¬ frame.RawParentSearch := by
  intro h
  have he := (h lastBottom rawFather (by unfold Frame.Real; decide) raw_parent).symm.trans true_parent
  have hn : (some rawFather : Option frame.Node) ≠ some trueFather := by decide
  exact hn he

theorem ordered : frame.Ordered := by
  refine {
    length_ge_two := by decide
    phantom := ?_
    bottom_row := ?_
    rows_strict := ?_
    real_positive := by unfold Frame.Real; decide
    stored_valid := ?_ }
  · intro c h
    fin_cases c <;> rfl
  · intro c h
    fin_cases c <;> rfl
  · intro c
    fin_cases c <;> unfold StrictMono <;> decide
  · have hStored : ∀ u : frame.Node,
        (frame.cell u).left = none ∨
          ∃ parent : frame.Node, (frame.cell u).left = some (Frame.ref parent) ∧
            parent.1.val < u.1.val ∧ (frame.height parent = 0 ∨ frame.height parent = 1) ∧
              0 < u.2.val := by decide
    have hPositive : ∀ u : frame.Node, 0 < u.2.val →
        (frame.height u = 1 ∨ (1 : Row) < frame.height u) := by decide
    intro u ref hLeft
    rcases hStored u with hNone | ⟨parent, hRef, hColumn, hParentRow, hReal⟩
    · rw [hLeft] at hNone
      cases hNone
    have hEq : ref = Frame.ref parent := Option.some.inj (hLeft.symm.trans hRef)
    subst ref
    refine ⟨parent, Frame.lookup_ref frame parent, hColumn, ?_⟩
    rcases hParentRow with hZero | hOne
    · rw [hZero]
      exact Row.zero_le _
    · rw [hOne]
      rcases hPositive u hReal with hEq | hLt
      · exact le_of_eq hEq.symm
      · exact hLt.le

theorem raw_row_geometry : frame.RawRowGeometry := by
  have hn1 : ∀ i, Row.coeff (1 : Row) i = if i = 0 then 1 else 0 := by
    intro i
    change Row.coeff (Row.ofList [1]) i = _
    cases i <;> simp
  have hn2 : ∀ i, Row.coeff (2 : Row) i = if i = 0 then 2 else 0 := by
    intro i
    change Row.coeff (Row.ofList [2]) i = _
    cases i <;> simp
  have h11 : Row.B 1 1 = 2 := by
    rw [Row.B_self]
    apply Row.ext
    intro i
    simp only [Row.coeff_bump, hn1, hn2]
    split_ifs <;> omega
  have h21 : Row.B 2 1 = Row.ofList [0, 1] := by
    have hj : Row.jump 2 1 = 1 := by
      apply Row.jump_eq_succ_of_last (i := 0) (by decide)
      intro j hj
      simp only [hn1, hn2, if_neg (Nat.ne_of_gt hj)]
    rw [Row.B, hj]
    apply Row.ext
    intro i
    rcases i with _ | _ | i
    · rfl
    · simp only [Row.coeff_bump_at, hn2]
      rfl
    · rw [Row.coeff_bump_high (by omega), hn2,
        Row.coeff_ofList_above [0, 1] (i+2) (by simp)]
      simp
  have hParent : ∀ u : frame.Node, 0 < u.2.val → frame.upper u ≠ none →
      frame.rawParent u = some rawFather := by decide
  have hB : ∀ u upper : frame.Node, 0 < u.2.val → frame.upper u = some upper →
      frame.height upper = Row.B (frame.height u) 1 := by
    have hRows : ∀ u upper : frame.Node, 0 < u.2.val → frame.upper u = some upper →
        (frame.height u = 1 ∧ frame.height upper = 2) ∨
          (frame.height u = 2 ∧ frame.height upper = Row.ofList [0, 1]) := by decide
    intro u upper hu he
    rcases hRows u upper hu he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, h11]
    · rw [h1, h2, h21]
  intro u upper hReal hUpper
  have hp := hParent u hReal (by rw [hUpper]; simp)
  exact ⟨rawFather, hp, Frame.rawParent_column_lt ordered hp,
    Frame.one_le_height ordered hReal, hB u upper hReal hUpper⟩

theorem valid : MountainValid mountain := by
  have hExists : ∀ u : frame.Node, 0 < u.2.val → 0 < u.1.val →
      (frame.cell u).left ≠ none := by decide
  have hFirst : ∀ u : frame.Node, 0 < u.2.val → u.1.val = 0 →
      frame.value u = 1 := by decide
  intro c hc
  let cf : Fin frame.width := ⟨c, hc⟩
  refine {
    size_ge_two := ordered.length_ge_two cf
    phantom := ?_
    bottom_row := ?_
    rows_strict := ?_
    real_positive := ?_
    stored_valid := ?_
    stored_exists := ?_
    first_values := ?_ }
  · have h0 : 0 < mountain[c].size := lt_of_lt_of_le (by decide) (ordered.length_ge_two cf)
    exact (Array.getElem?_eq_getElem h0).trans (congrArg some (ordered.phantom cf h0))
  · intro cell hCell
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.mp hCell
    rw [← he]
    exact ordered.bottom_row cf hi
  · intro i j a b ha hb hij
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ha
    obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
    exact ordered.rows_strict cf (show (⟨i, hi⟩ : Fin (frame.length cf)) < ⟨j, hj⟩ from hij)
  · intro i cell hCell hi
    obtain ⟨hSize, rfl⟩ := Array.getElem?_eq_some_iff.mp hCell
    exact ordered.real_positive ⟨cf, ⟨i, hSize⟩⟩ hi
  · intro i cell ref hCell hRef
    obtain ⟨hSize, rfl⟩ := Array.getElem?_eq_some_iff.mp hCell
    let u : frame.Node := ⟨cf, ⟨i, hSize⟩⟩
    obtain ⟨parent, hLookup, hColumn, hRow⟩ := ordered.stored_valid u ref hRef
    have hRefEq := Frame.lookup_spec hLookup
    refine ⟨?_, frame.cell parent, ?_, hRow⟩
    · simpa only [← hRefEq, Frame.ref] using hColumn
    · rw [← hRefEq]
      exact cellAt_ok_iff.mpr ⟨mountain[parent.1.val],
        Array.getElem?_eq_getElem parent.1.isLt, Array.getElem?_eq_getElem parent.2.isLt⟩
  · intro i cell hCell hi hcpos
    obtain ⟨hSize, rfl⟩ := Array.getElem?_eq_some_iff.mp hCell
    have h := hExists ⟨cf, ⟨i, hSize⟩⟩ hi hcpos
    cases he : (mountain[c][i]).left with
    | none => exact False.elim (h he)
    | some ref => exact ⟨ref, rfl⟩
  · intro i cell hCell hi hc0
    obtain ⟨hSize, rfl⟩ := Array.getElem?_eq_some_iff.mp hCell
    exact hFirst ⟨cf, ⟨i, hSize⟩⟩ hi hc0

theorem raw_geometry : MountainRawGeometry mountain :=
  mountainRawGeometry_of_rawRowGeometry raw_row_geometry

theorem sums : MountainSums mountain := by
  intro c hc
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 := by change c < 3 at hc; omega
  rcases hc' with rfl | rfl | rfl
  · change [phantom, ⟨1, 1, none⟩].IsChain (AdjacentSum mountain)
    simp [List.isChain_cons_cons, AdjacentSum, phantom]
  · change [phantom, ⟨1, 2, some ⟨0, 0⟩⟩, ⟨2, 1, some ⟨0, 1⟩⟩].IsChain _
    rw [List.isChain_cons_cons, List.isChain_cons_cons]
    refine ⟨?_, ?_, List.isChain_singleton _⟩
    · intro h; exact False.elim (h rfl)
    · intro _
      exact ⟨⟨0, 1⟩, ⟨1, 1, none⟩, rfl, rfl, by decide, rfl⟩
  · change [phantom, ⟨1, 3, some ⟨1, 0⟩⟩, ⟨2, 2, some ⟨0, 1⟩⟩,
        ⟨Row.ofList [0, 1], 1, some ⟨0, 1⟩⟩].IsChain _
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    refine ⟨?_, ?_, ?_, List.isChain_singleton _⟩
    · intro h; exact False.elim (h rfl)
    · intro _
      exact ⟨⟨0, 1⟩, ⟨1, 1, none⟩, rfl, rfl, by decide, rfl⟩
    · intro _
      exact ⟨⟨0, 1⟩, ⟨1, 1, none⟩, rfl, rfl, by decide, rfl⟩

theorem tops : MountainTops mountain := by
  intro c hc
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 := by change c < 3 at hc; omega
  rcases hc' with rfl | rfl | rfl
  · exact ⟨⟨1, 1, none⟩, rfl, rfl⟩
  · exact ⟨⟨2, 1, some ⟨0, 1⟩⟩, rfl, rfl⟩
  · exact ⟨⟨Row.ofList [0, 1], 1, some ⟨0, 1⟩⟩, rfl, rfl⟩

theorem bottom_legs : BottomLegs mountain := by
  intro c hc
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 := by change c < 3 at hc; omega
  rcases hc' with rfl | rfl | rfl
  · exact ⟨⟨1, 1, none⟩, rfl, rfl⟩
  · exact ⟨⟨1, 2, some ⟨0, 0⟩⟩, rfl, rfl⟩
  · exact ⟨⟨1, 3, some ⟨1, 0⟩⟩, rfl, rfl⟩

/-- The strict-left columns already agree with numerical P. -/
theorem strict_left_recognized : ∀ u parent : frame.Node,
    u.1.val < 2 → 0 < u.2.val → frame.rawParent u = some parent →
      frame.P u = some parent := by decide

/-- All nodes strictly above the bottom already agree with numerical P. -/
theorem upper_nodes_recognized : ∀ u parent : frame.Node,
    1 < u.2.val → frame.rawParent u = some parent → frame.P u = some parent := by decide

theorem actual_candidate : frame.Q lastBottom = some trueFather := by decide
theorem candidate_parent : frame.P trueFather = some rawFather := by decide

/-- Even the desired record reachability holds in this example. -/
theorem record_path : Frame.ParentPath frame trueFather rawFather :=
  .cons candidate_parent (.refl rawFather)

/-- The last record is too small, so it must not be skipped. -/
theorem last_record_fails_barrier : frame.value trueFather < frame.value lastBottom := by decide

theorem not_canonical_build (values : List Nat) : Canonical.build values ≠ .ok mountain := by
  intro h
  have hN : frame.Normal := build_normal_of_success h
  have he := (hN.rawParent_eq_P (show Frame.Real lastBottom by unfold Frame.Real; decide)).symm.trans raw_parent
  have hn : (some rawFather : Option frame.Node) ≠ some trueFather := by decide
  exact hn (he.symm.trans true_parent)

/-- A fully finite obstruction to recovery from the raw local laws alone.
No claim is made that this mountain can be produced by `expandDiagram`. -/
theorem counterexample :
    MountainValid mountain ∧ MountainRawGeometry mountain ∧ frame.RawFatherUpperBound ∧
      MountainSums mountain ∧ MountainTops mountain ∧ BottomLegs mountain ∧
        ¬ frame.RawParentSearch :=
  ⟨valid, raw_geometry, raw_father_bound, sums, tops, bottom_legs, not_raw_parent_search⟩

end OmegaY.Expansion.RawGeometryCounterexample

#print axioms OmegaY.Expansion.RawGeometryCounterexample.raw_parent
#print axioms OmegaY.Expansion.RawGeometryCounterexample.true_parent
#print axioms OmegaY.Expansion.RawGeometryCounterexample.executable_parent
#print axioms OmegaY.Expansion.RawGeometryCounterexample.raw_row_geometry
#print axioms OmegaY.Expansion.RawGeometryCounterexample.raw_father_bound
#print axioms OmegaY.Expansion.RawGeometryCounterexample.not_raw_parent_search
#print axioms OmegaY.Expansion.RawGeometryCounterexample.ordered
#print axioms OmegaY.Expansion.RawGeometryCounterexample.valid
#print axioms OmegaY.Expansion.RawGeometryCounterexample.raw_geometry
#print axioms OmegaY.Expansion.RawGeometryCounterexample.sums
#print axioms OmegaY.Expansion.RawGeometryCounterexample.tops
#print axioms OmegaY.Expansion.RawGeometryCounterexample.bottom_legs
#print axioms OmegaY.Expansion.RawGeometryCounterexample.strict_left_recognized
#print axioms OmegaY.Expansion.RawGeometryCounterexample.upper_nodes_recognized
#print axioms OmegaY.Expansion.RawGeometryCounterexample.actual_candidate
#print axioms OmegaY.Expansion.RawGeometryCounterexample.candidate_parent
#print axioms OmegaY.Expansion.RawGeometryCounterexample.record_path
#print axioms OmegaY.Expansion.RawGeometryCounterexample.last_record_fails_barrier
#print axioms OmegaY.Expansion.RawGeometryCounterexample.not_canonical_build
#print axioms OmegaY.Expansion.RawGeometryCounterexample.counterexample
