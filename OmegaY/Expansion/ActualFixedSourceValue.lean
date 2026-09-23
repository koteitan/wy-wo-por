/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFixedSourceValue.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAllUpperLift
import OmegaY.Expansion.ActualMixedCommonParentUpper
import OmegaY.Expansion.TotalEquations

/-!
# Exact values for actual copies with a fixed immediate source parent

Above a source edge whose father lies in the good part, every later source
father remains in that good part, or the source reaches its top. These
uppers are unmarked. Actual execution therefore identifies each effective
upper with the next effective source occurrence. Stored fixed parents keep
their complete original cells. Induction on the strictly decreasing source
value now identifies both backfill sums, without any target numerical P.
-/

namespace OmegaY.Geometry.Frame

theorem Normal.upper_parent_column_le {F : Frame} (hF : F.Normal)
    {child parent upper next : F.Node} (hParent : F.P child = some parent)
    (hUpper : F.upper child = some upper) (hNext : F.P upper = some next) :
    next.1.val ≤ parent.1.val := by
  obtain ⟨candidate, hCandidate, trace⟩ := (P_iff hF.toOrdered).mp hNext
  have hBefore := trace.column_le hF.toOrdered
  rcases candidate_after_upper hF hParent hUpper with hSame | ⟨plus, hPlus, _, hSame⟩
  · have he : candidate = parent := Option.some.inj (hCandidate.symm.trans hSame)
    simpa only [he] using hBefore
  · have he : candidate = plus := Option.some.inj (hCandidate.symm.trans hSame)
    simpa only [he, (upper_spec hPlus).1] using hBefore

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem parentless_source_not_marked
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {source : (Frame.ofMountain p.reduced).Node} (hReal : Real source)
    (hNone : (Frame.ofMountain p.reduced).P source = none) :
    ¬ BucketMem p.marked source.1.val (Frame.ref source) := by
  intro hMarked
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hRight, low, _, hColumn, _, hPath, _⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mp hMarked
  cases hPath with
  | refl => have hc := congrArg Fin.val hColumn; omega
  | cons hParent _ => rw [hNone] at hParent; cases hParent

private theorem unmarked_index_of_not_marked
    {front : List Nat} {last : Nat} (p : Preparation front last)
    (node : (Frame.ofMountain p.reduced).Node)
    (hNot : ¬ BucketMem p.marked node.1.val (Frame.ref node)) :
    node.2.val ∉ (p.marked[node.1.val]?.getD []).map Ref.index := by
  intro h
  obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
  have he : marker = Frame.ref node := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
  exact hNot (he ▸ hm)

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

include copy

/-- The existing executed column supplies every other source occurrence in
that same column, without a fresh copy execution or history assumption. -/
theorem in_same_column (hLast : 1 < last)
    {other : (Frame.ofMountain p.reduced).Node} (hColumn : other.1 = source.1) :
    Nonempty (EffectiveCopyOccurrence p block start references other result) := by
  rcases source with ⟨column, sourceIndex⟩
  rcases other with ⟨otherColumn, otherIndex⟩
  change otherColumn = column at hColumn
  subst otherColumn
  have hSource : p.reduced[column.val]? = some copy.data.sources :=
    (copy.state.base_ambient _ column.isLt).symm.trans copy.data.source_column
  have hRead : copy.data.sources[otherIndex.val]? =
      some ((Frame.ofMountain p.reduced).cell ⟨column, otherIndex⟩) :=
    copy.data.frame_source_read hSource (u := ⟨column, otherIndex⟩) rfl
  obtain ⟨hNoPrem, hPP, hPL⟩ := copy.state.column_data_parent_inputs hLast column.isLt copy.data
  obtain ⟨read⟩ := copy.data.effective_copy_read hPP hPL hNoPrem copy.read.copy_run hRead
  exact ⟨⟨copy.before, copy.column, copy.state, copy.data, read, copy.preserved⟩⟩

private theorem fixed_raw_parent (hLast : 1 < last)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hFixed : parent.1.val < p.root.column) :
    RawRefEdge result copy.outputRef (Frame.ref parent) ∧
      Canonical.cellAt result (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent) := by
  obtain ⟨actual, _, _, hEdge, hRead⟩ := copy.state.actual_fixed_parent hLast hParent rfl hFixed copy.read.copy_run
  have hEqual := ((actual.extend copy.preserved).unique copy).1
  change actual.outputRef = copy.outputRef at hEqual
  refine ⟨by simpa only [hEqual] using hEdge.preserve copy.preserved, ?_⟩
  obtain ⟨nodes, hNodes, hAt⟩ := cellAt_ok_iff.mp hRead
  exact cellAt_ok_iff.mpr ⟨nodes, copy.preserved.column_read hNodes, hAt⟩

/-- Complete fixed-parent values are retained even if the effective lower
row moves. Only actual equations, tops and execution are used. -/
theorem value_of_fixed_or_terminal (hLast : 1 < last)
    (hValid : MountainValid result) (hSums : MountainSums result) (hTops : MountainTops result)
    (hReal : Real source)
    (hExit : (Frame.ofMountain p.reduced).P source = none ∨
      ∃ parent, (Frame.ofMountain p.reduced).P source = some parent ∧ parent.1.val < p.root.column) :
    copy.read.outputCell.value = (Frame.ofMountain p.reduced).value source := by
  have hNormal := build_normal_of_success p.reduced_build
  generalize hValue : (Frame.ofMountain p.reduced).value source = value
  induction value using Nat.strongRecOn generalizing source with
  | ind value ih =>
    obtain ⟨actual, hRef, hCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
    have hActualReal : Real actual := by
      have hi : actual.2.val = copy.read.outputIndex := congrArg Ref.index hRef
      change 0 < actual.2.val
      rw [hi]
      exact copy.read.output_real hReal
    rcases hExit with hNone | ⟨parent, hParent, hFixed⟩
    · have hTop : (Frame.ofMountain p.reduced).upper source = none := by
        cases hu : (Frame.ofMountain p.reduced).upper source with
        | none => rfl
        | some upper =>
          obtain ⟨father, hp, _⟩ := hNormal.upper_step source upper hReal hu
          rw [hNone] at hp
          cases hp
      have hSourceOne := hNormal.value_one_of_upper_none hReal hTop
      have hActualOne := MountainTops.value_one_of_upper_none hTops (copy.top_upper_none hLast hTop hRef)
      exact (congrArg Cell.value hCell).symm.trans (hActualOne.trans (hSourceOne.symm.trans hValue))
    · obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hParent
      have hUpperReal := upper_real hUpper
      have hUpperExit : (Frame.ofMountain p.reduced).P upper = none ∨
          ∃ father, (Frame.ofMountain p.reduced).P upper = some father ∧ father.1.val < p.root.column := by
        cases hp : (Frame.ofMountain p.reduced).P upper with
        | none => exact Or.inl rfl
        | some father => exact Or.inr ⟨father, rfl,
            (hNormal.upper_parent_column_le hParent hUpper hp).trans_lt hFixed⟩
      have hUpperNotMarked : ¬ BucketMem p.marked upper.1.val (Frame.ref upper) := by
        rcases hUpperExit with hn | ⟨father, hp, hf⟩
        · exact parentless_source_not_marked p hUpperReal hn
        · exact p.fixed_parent_not_marked hp hf
      obtain ⟨upperCopy⟩ := copy.in_same_column hLast (upper_spec hUpper).1
      obtain ⟨nextCell, hNextRead, hNextRow⟩ := copy.effective_upper_row_all hLast hReal upperCopy hUpper
        (unmarked_index_of_not_marked p upper hUpperNotMarked)
      obtain ⟨next, hNextRef, hNextCell⟩ := Canonical.frame_node_of_cellAt hNextRead
      obtain ⟨upperNode, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt upperCopy.output_read
      have hNodeColumn : next.1 = upperNode.1 := Fin.ext (by
        have hn : next.1.val = copy.outputRef.column := congrArg Ref.column hNextRef
        have hu : upperNode.1.val = upperCopy.outputRef.column := congrArg Ref.column hUpperRef
        rw [hn, hu, copy.source_column, upperCopy.source_column, (upper_spec hUpper).1])
      have hNodeRow : (Frame.ofMountain result).height next = (Frame.ofMountain result).height upperNode := by
        change ((Frame.ofMountain result).cell next).row = ((Frame.ofMountain result).cell upperNode).row
        rw [hNextCell, hUpperCell]
        exact hNextRow
      have hNextEq := node_eq_of_column_height hValid.toOrdered hNodeColumn hNodeRow
      have hActualUpper : (Frame.ofMountain result).upper actual = some upperNode := by
        simpa only [hNextEq] using Frame.upper_of_refs hRef hNextRef
      obtain ⟨sourceParent, hSourceParent, _, hDifference, _⟩ := hNormal.upper_step source upper hReal hUpper
      have hSourceParentEq : sourceParent = parent := Option.some.inj (hSourceParent.symm.trans hParent)
      subst sourceParent
      change (Frame.ofMountain p.reduced).value upper =
        (Frame.ofMountain p.reduced).value source - (Frame.ofMountain p.reduced).value parent at hDifference
      have hSmall : (Frame.ofMountain p.reduced).value upper < value := by
        have hp := P_value hNormal.toOrdered hParent
        omega
      have hUpperValue := ih ((Frame.ofMountain p.reduced).value upper) hSmall upperCopy hUpperReal hUpperExit rfl
      obtain ⟨hEdge, hParentRead⟩ := copy.fixed_raw_parent hLast hParent hFixed
      obtain ⟨parentNode, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt hParentRead
      have hRaw := hEdge.rawParent hRef hParentRef
      obtain ⟨sumParent, hSumRaw, _, _, _, hSum, _⟩ := hSums.rawParent_upper hValid hActualReal hActualUpper
      have hSumParentEq : sumParent = parentNode := Option.some.inj (hSumRaw.symm.trans hRaw)
      subst sumParent
      have hActualValue : (Frame.ofMountain result).value actual = copy.read.outputCell.value := congrArg Cell.value hCell
      have hActualUpperValue : (Frame.ofMountain result).value upperNode =
          (Frame.ofMountain p.reduced).value upper := (congrArg Cell.value hUpperCell).trans hUpperValue
      have hActualParentValue : (Frame.ofMountain result).value parentNode =
          (Frame.ofMountain p.reduced).value parent := congrArg Cell.value hParentCell
      have hp := P_value hNormal.toOrdered hParent
      rw [hActualValue, hActualUpperValue, hActualParentValue] at hSum
      omega

theorem value_of_fixed_parent_expansion (hLast : 1 < last)
    {input : List Nat} (hLegal : Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hFixed : parent.1.val < p.root.column) :
    copy.read.outputCell.value = (Frame.ofMountain p.reduced).value source := by
  have hNormal := build_normal_of_success p.reduced_build
  have hp := P_value hNormal.toOrdered hParent
  obtain ⟨hSums, hTops⟩ := expandDiagram_equations hLegal hRun
  exact copy.value_of_fixed_or_terminal hLast (expandDiagram_valid_of_success hLegal hRun)
    hSums hTops (real_of_value_pos hNormal.toOrdered (hp.1.trans hp.2)) (.inr ⟨parent, hParent, hFixed⟩)

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.upper_parent_column_le
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.in_same_column
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.value_of_fixed_or_terminal
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.value_of_fixed_parent_expansion
