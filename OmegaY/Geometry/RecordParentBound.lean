/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RecordParentBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.RowShadow
import OmegaY.Expansion.FrontierEvents

/-!
# A raw-parent upper bound from strict-left numerical records

Only columns strictly before the current column supply canonical facts.
The current node supplies its actual Q candidate, an explicit record path
to the intended parent, and its independently obtained raw B row equation.
Neither P of the current node nor normality of its column is assumed.

Record-path reachability is still an input. This module does not establish
that copied references lie on those record paths or recover first-smaller
parents in the current column.
-/

namespace OmegaY.Geometry.Frame

/-- The local induction packet needed from strictly earlier columns.
The father bound is only for actual numerical P edges whose child is already
strictly left of the current bound; it does not assert a bound for the
current node or for an unrecognized raw-parent edge. -/
structure LeftParentGeometry (F : Frame) (bound : Nat) : Prop where
  upper_exists : ∀ node, node.1.val < bound → Real node → 1 < F.value node →
    ∃ upper, F.upper node = some upper
  upper_nontrivial : ∀ node upper, node.1.val < bound → Real node →
    F.upper node = some upper → 1 < F.value node
  upper_row : ∀ node upper, node.1.val < bound → Real node →
    F.upper node = some upper →
      ∃ parent, F.P node = some parent ∧ F.height upper = Row.B (F.height node) (F.height parent)
  father_bound : ∀ node parent, node.1.val < bound → F.P node = some parent →
    1 < F.value parent → F.aboveHeight node ≤ F.aboveHeight parent

/-- Existing source normality supplies the packet, but is not required by
the current-column results below. A column induction may instead supply
these fields from previously proved columns alone. -/
theorem LeftParentGeometry.of_normal {F : Frame} (hF : F.Normal) (bound : Nat) :
    LeftParentGeometry F bound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro node _ hReal hValue
    exact hF.upper_exists node hReal hValue
  · intro node upper _ hReal hUpper
    exact hF.upper_nontrivial node upper hReal hUpper
  · intro node upper _ hReal hUpper
    obtain ⟨parent, hParent, hRow, _⟩ := hF.upper_step node upper hReal hUpper
    exact ⟨parent, hParent, hRow⟩
  · intro node parent _ hParent hValue
    exact father_upper_bound hF hParent hValue

theorem ParentPath.real_of_start {F : Frame} (hF : F.Ordered) {q p : F.Node}
    (path : ParentPath F q p) (hReal : Real q) : Real p := by
  revert hReal
  induction path with
  | refl => exact fun h => h
  | cons hParent _ ih =>
    intro _
    exact ih (real_of_value_pos hF (P_value hF hParent).1)

/-- Both the column and height of the record endpoint are automatically
bounded by the actual first Q candidate and current node. -/
theorem record_parent_left_and_below {F : Frame} (hF : F.Ordered)
    {u q p : F.Node} (hQ : F.Q u = some q) (path : ParentPath F q p) :
    p.1.val < u.1.val ∧ F.height p ≤ F.height u :=
  ⟨(path.column_le hF).trans_lt (Q_column_lt hF hQ),
    (path.height_le hF).trans (Q_height_le hF hQ)⟩

/-- Propagate earlier-column father bounds along the actual records.
The current node's upper row is not used, and no current numerical-parent
claim is made. The candidate's upper is above the current node by Q's
actual maximum search. -/
theorem current_below_record_parent_upper {F : Frame} (hF : F.Ordered)
    {u q p parentUpper : F.Node} (hLeft : LeftParentGeometry F u.1.val)
    (hReal : Real u) (hQ : F.Q u = some q) (path : ParentPath F q p)
    (hParentUpper : F.upper p = some parentUpper) : F.height u < F.height parentUpper := by
  have hQLeft := Q_column_lt hF hQ
  have hQReal := Q_real hF hReal hQ
  have hParentLeft := (record_parent_left_and_below hF hQ path).1
  have hParentReal := path.real_of_start hF hQReal
  have hParentValue : 1 < F.value p :=
    hLeft.upper_nontrivial p parentUpper hParentLeft hParentReal hParentUpper
  have hQValue : 1 < F.value q := hParentValue.trans_le (path.value_le hF)
  obtain ⟨qUpper, hQUpper⟩ := hLeft.upper_exists q hQLeft hQReal hQValue
  have hChain := path.above_le_of_left_induction hF hLeft.father_bound hQLeft hParentValue
  have hChainRows : F.height qUpper ≤ F.height parentUpper := by
    simpa only [aboveHeight_of_upper hQUpper, aboveHeight_of_upper hParentUpper] using hChain
  exact (Q_upper_gt hF hQ hQUpper).trans_le hChainRows

/-- The raw B equation turns record reachability into the missing upper
bound. The parent's own upper follows its already proved left-column
numerical B rule, so Row.interval_bound applies without using P u. -/
theorem record_parent_upper_bound {F : Frame} (hF : F.Ordered)
    {u q p upper parentUpper : F.Node} (hLeft : LeftParentGeometry F u.1.val)
    (hReal : Real u) (hQ : F.Q u = some q) (path : ParentPath F q p)
    (_hUpper : F.upper u = some upper)
    (hRawB : F.height upper = Row.B (F.height u) (F.height p))
    (hParentUpper : F.upper p = some parentUpper) :
    F.height upper ≤ F.height parentUpper := by
  have hParentFacts := record_parent_left_and_below hF hQ path
  have hParentReal := path.real_of_start hF (Q_real hF hReal hQ)
  obtain ⟨grandparent, _, hParentRow⟩ :=
    hLeft.upper_row p parentUpper hParentFacts.1 hParentReal hParentUpper
  have hAbove := current_below_record_parent_upper hF hLeft hReal hQ path hParentUpper
  rw [hRawB, hParentRow]
  exact Row.interval_bound hParentFacts.2 (by simpa only [hParentRow] using hAbove)

/-- At every cut below the current upper, the record endpoint is exactly
its column's actual finite frontier. If the endpoint has no upper, the
selector's upper-barrier condition is vacuous and the same proof applies. -/
theorem record_parent_frontier {F : Frame} (hF : F.Ordered)
    {u q p upper : F.Node} (hLeft : LeftParentGeometry F u.1.val)
    (hReal : Real u) (hQ : F.Q u = some q) (path : ParentPath F q p)
    (hUpper : F.upper u = some upper)
    (hRawB : F.height upper = Row.B (F.height u) (F.height p))
    {cut : Row} (hCut : (1 : Row) ≤ cut) (hCurrentBelow : F.height u ≤ cut)
    (hUpperAbove : cut < F.height upper) :
    frontierAt hF cut hCut p.1 = p := by
  apply frontierAt_eq_of_upper_barrier hF hCut
  · exact (record_parent_left_and_below hF hQ path).2.trans hCurrentBelow
  · intro parentUpper hParentUpper
    exact hUpperAbove.trans_le
      (record_parent_upper_bound hF hLeft hReal hQ path hUpper hRawB hParentUpper)

/-- For the actual frontier selector, its reality and cut bounds need no
separate premises. Only left-column geometry, the current raw B equation,
and the still-explicit record reachability remain to be supplied. -/
theorem frontierAt_record_parent {F : Frame} (hF : F.Ordered)
    {cut : Row} (hCut : (1 : Row) ≤ cut) (column : Fin F.width)
    (hLeft : LeftParentGeometry F column.val) {q p upper : F.Node}
    (hQ : F.Q (frontierAt hF cut hCut column) = some q)
    (path : ParentPath F q p)
    (hUpper : F.upper (frontierAt hF cut hCut column) = some upper)
    (hRawB : F.height upper = Row.B (F.height (frontierAt hF cut hCut column)) (F.height p)) :
    frontierAt hF cut hCut p.1 = p := by
  have hSpec := frontierAt_spec hF hCut column
  exact record_parent_frontier hF hLeft hSpec.2.1 hQ path hUpper hRawB hCut
    hSpec.2.2.1 (hSpec.2.2.2.2 upper hUpper)

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.LeftParentGeometry.of_normal
#print axioms OmegaY.Geometry.Frame.ParentPath.real_of_start
#print axioms OmegaY.Geometry.Frame.record_parent_left_and_below
#print axioms OmegaY.Geometry.Frame.current_below_record_parent_upper
#print axioms OmegaY.Geometry.Frame.record_parent_upper_bound
#print axioms OmegaY.Geometry.Frame.record_parent_frontier
#print axioms OmegaY.Geometry.Frame.frontierAt_record_parent
