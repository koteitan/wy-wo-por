/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ReducedHighTail.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootInterval
import OmegaY.Canonical.DecrementBuild

/-!
# The exact root suffix in the actual reduced last column

The generic decrement theorem records only that a suffix comes from some
earlier column. Here the actual old penultimate node identifies that column
and cut: the appended tail is exactly the bad root's strict upper suffix.
All comparisons use the two independently constructed canonical mountains.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem cells_eq {a b : Cell} (hr : a.row = b.row) (hv : a.value = b.value)
    (hl : a.left = b.left) : a = b := by
  cases a
  cases b
  simp_all

/-- Identical real cells over identical earlier columns have identical
complete upper suffixes. This follows by running the actual continuation
builder twice on the same artificial target, not by assuming suffix equality. -/
theorem normal_upperSuffix_eq_of_same_cell {before after : Mountain}
    (hBefore : (Frame.ofMountain before).Normal)
    (hAfter : (Frame.ofMountain after).Normal)
    {u : (Frame.ofMountain before).Node} {v : (Frame.ofMountain after).Node}
    (hu : Frame.Real u) (hv : Frame.Real v)
    (hCell : (Frame.ofMountain before).cell u = (Frame.ofMountain after).cell v)
    (hRight : u.1.val ≤ after.size)
    (hColumns : ∀ c, c < u.1.val → before[c]? = after[c]?) :
    upperSuffix before u = upperSuffix after v := by
  let target : Column := #[(Frame.ofMountain before).cell u]
  have hTop : target.back? = some ((Frame.ofMountain before).cell u) := by rfl
  have hOtherTop : target.back? = some ((Frame.ofMountain after).cell v) := by rw [← hCell]; exact hTop
  let fuel := (Frame.ofMountain before).value u - 1
  obtain ⟨one, hOne, hOneList, _⟩ := growColumn_graft_transfer hBefore hu hTop
    hRight hColumns (fuel := fuel) (le_refl _)
  have hEnough : (Frame.ofMountain after).value v - 1 ≤ fuel := by
    change ((Frame.ofMountain after).cell v).value - 1 ≤ _
    rw [← hCell]
    exact le_refl _
  obtain ⟨two, hTwo, hTwoList, _⟩ := growColumn_graft_of_normal hAfter hv hOtherTop hEnough
  have hEq : one = two := Except.ok.inj (hOne.symm.trans hTwo)
  exact List.append_cancel_left (hOneList.symm.trans ((congrArg Array.toList hEq).trans hTwoList))

/-- In the actual reduced mountain, the old penultimate reference contains
its decremented cell. The complete tail above it is precisely the original
bad root's strict upper suffix, including values and stored references. -/
theorem Preparation.reduced_exact_root_suffix {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (g : RootGeometry p) :
    ∃ lower : (Frame.ofMountain p.reduced).Node,
      Frame.ref lower = Frame.ref g.lower ∧
      (Frame.ofMountain p.reduced).cell lower = decCell ((Frame.ofMountain p.initial).cell g.lower) ∧
      upperSuffix p.reduced lower = upperSuffix p.initial g.rootNode := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hN : F.Normal := build_normal_of_success p.initial_build
  have hM : G.Normal := build_normal_of_success p.reduced_build
  have hRead := p.reduced_below_top_cell hLast g.lower g.lower_column g.lower_lt_top
  obtain ⟨lower, hRef, hCell⟩ := Canonical.frame_node_of_cellAt hRead
  have hCellG : G.cell lower = decCell (F.cell g.lower) := hCell
  have hReal : Frame.Real lower := by
    unfold Frame.Real
    have hi : lower.2.val = g.lower.2.val := congrArg Ref.index hRef
    rw [hi]
    exact g.lower_real
  have hTopReal : Frame.Real g.topNode := by
    unfold Frame.Real
    have := g.top_index_gt_one
    omega
  have hTopOne : F.value g.topNode = 1 := by
    by_contra hNot
    have hPos := hN.real_positive g.topNode hTopReal
    obtain ⟨next, hNext⟩ := hN.upper_exists g.topNode hTopReal (by omega)
    have hi := (Frame.upper_spec hNext).2
    have hc := (Frame.upper_spec hNext).1
    have hb := next.2.isLt
    have hLength : F.length next.1 = g.topNode.2.val + 1 :=
      (congrArg F.length hc).trans g.top_last.symm
    omega
  have hOldValue : F.value g.lower = F.value g.rootNode + 1 :=
    ((upper_value_one_iff_parent_add_one hN g.lower_parent g.lower_upper).mp hTopOne).symm
  have hValue : G.value lower = F.value g.rootNode := by
    change (G.cell lower).value = _
    rw [hCell, decCell_value]
    change F.value g.lower - 1 = _
    omega
  refine ⟨lower, hRef, hCell, ?_⟩
  by_cases hOne : F.value g.rootNode = 1
  · rw [upperSuffix_of_value_one hM hReal (hValue.trans hOne),
      upperSuffix_of_value_one hN g.root_real hOne]
  · have hRootPos := hN.real_positive g.rootNode g.root_real
    have hLarge : 1 < F.value g.rootNode := by omega
    have hColumns : ∀ c, c < g.lower.1.val → p.initial[c]? = p.reduced[c]? := by
      intro c hc
      exact build_changed_last_preserves_prefix p.initial_build p.reduced_build
        (by simpa only [g.lower_column] using hc)
    obtain ⟨step⟩ := build_decrement_step p.initial_build hLarge hOldValue hRead
      (show (decCell (F.cell g.lower)).value = F.value g.rootNode by
        change F.value g.lower - 1 = _; omega) rfl rfl hColumns
    have hOldParent : step.oldParent = g.rootNode := by
      apply Executable.ref_injective F
      exact Except.ok.inj (step.old_parent.symm.trans g.lower_actual_parent) |>.trans g.root_ref.symm
    rcases step.cases with ⟨_, hSmall, _⟩ | ⟨_, _, rootUpper, hRootUpper, hNext⟩
    · rw [hOldParent] at hSmall
      exact False.elim ((lt_irrefl _) hSmall)
    · rw [hOldParent] at hRootUpper
      obtain ⟨next, hNextUpper⟩ := hM.upper_exists lower hReal (by rw [hValue]; exact hLarge)
      obtain ⟨parent, hParent, hRow, hDifference, hLeft⟩ := hM.upper_step lower next hReal hNextUpper
      have hActual := (Executable.findParent_ref_iff hM.toOrdered lower parent).mpr hParent
      have hParentRef : Frame.ref parent = Frame.ref step.newParent := by
        rw [hRef] at hActual
        exact Except.ok.inj (hActual.symm.trans step.new_parent)
      have hParentCell : G.cell parent = F.cell step.newParent := by
        have hTyped := cellAt_of_frame_node p.reduced parent
        rw [hParentRef] at hTyped
        exact Except.ok.inj (hTyped.symm.trans step.parent_read)
      have hNextCell : G.cell next = F.cell rootUpper := by
        calc
          G.cell next = decrementNextCell (decCell (F.cell g.lower)) (F.cell step.newParent)
              (Frame.ref step.newParent) := by
            apply cells_eq
            · simpa only [decrementNextCell, Frame.height, hCellG, hParentCell] using hRow
            · simpa only [decrementNextCell, Frame.value, hCellG, hParentCell] using hDifference
            · simpa only [decrementNextCell, hParentRef] using hLeft
          _ = F.cell rootUpper := hNext
      have hRootColumn : rootUpper.1.val = p.root.column :=
        (congrArg Fin.val (Frame.upper_spec hRootUpper).1).trans (congrArg Ref.column g.root_ref)
      have hSize := build_size p.reduced_build
      simp only [List.length_append, List.length_singleton] at hSize
      have hTails : upperSuffix p.initial rootUpper = upperSuffix p.reduced next :=
        normal_upperSuffix_eq_of_same_cell hN hM (upper_real hRootUpper) (upper_real hNextUpper)
          hNextCell.symm (by rw [hRootColumn]; have := p.root_before_last; omega)
          (fun c hc => build_changed_last_preserves_prefix p.initial_build p.reduced_build
            (by rw [hRootColumn] at hc; exact hc.trans p.root_before_last))
      rw [upperSuffix_of_upper hNextUpper, upperSuffix_of_upper hRootUpper, hNextCell, hTails]

/-- Above a node's actual height, membership in its sparse column is
equivalent to membership in its strict upper suffix. -/
theorem upperSuffix_high_rows_iff {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    (u : (Frame.ofMountain mountain).Node) {row : Row}
    (hAbove : (Frame.ofMountain mountain).height u < row) :
    row ∈ (upperSuffix mountain u).map Cell.row ↔
      row ∈ mountain[u.1.val].toList.map Cell.row := by
  constructor
  · intro hMem
    obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hMem
    exact List.mem_map.mpr ⟨cell, List.mem_of_mem_drop hCell, hRow⟩
  · intro hRow
    obtain ⟨cell, hCell, hCellRow⟩ := List.mem_map.mp hRow
    obtain ⟨i, hRead⟩ := List.mem_iff_getElem?.mp hCell
    have hArray : mountain[u.1.val][i]? = some cell := by
      simpa only [Array.getElem?_toList] using hRead
    obtain ⟨hi, hValue⟩ := Array.getElem?_eq_some_iff.mp hArray
    have hIndex : u.2.val < i := by
      by_contra hn
      have hLe : (⟨i, hi⟩ : Fin ((Frame.ofMountain mountain).length u.1)) ≤ u.2 :=
        Nat.le_of_not_gt hn
      have hRows := (hOrdered.rows_strict u.1).monotone hLe
      change mountain[u.1.val][i].row ≤ (Frame.ofMountain mountain).height u at hRows
      rw [hValue, hCellRow] at hRows
      exact (not_lt_of_ge hRows) hAbove
    apply List.mem_map.mpr
    refine ⟨cell, List.mem_iff_getElem?.mpr ⟨i - (u.2.val + 1), ?_⟩, hCellRow⟩
    simpa only [upperSuffix, List.getElem?_drop, Nat.add_sub_of_le (by omega : u.2.val + 1 ≤ i)]
      using hRead

/-- Actual last-column and root-column reads in the reduced mountain have
identical row support from the original last top upwards. -/
theorem Preparation.reduced_high_rows_iff {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last)
    {lastColumn rootColumn : Column}
    (hLastColumn : p.reduced[front.length]? = some lastColumn)
    (hRootColumn : p.reduced[p.root.column]? = some rootColumn)
    {row : Row} (hHigh : p.lastTop.row ≤ row) :
    row ∈ lastColumn.toList.map Cell.row ↔ row ∈ rootColumn.toList.map Cell.row := by
  obtain ⟨g⟩ := p.root_geometry hLast
  obtain ⟨lower, hRef, hCell, hSuffix⟩ := p.reduced_exact_root_suffix hLast g
  have hLowerColumn : lower.1.val = front.length :=
    (congrArg Ref.column hRef).trans g.lower_column
  have hLowerRow : (Frame.ofMountain p.reduced).height lower =
      (Frame.ofMountain p.initial).height g.lower := by
    simpa only [Frame.height, decCell_row] using congrArg Cell.row hCell
  have hLowerRead : p.reduced[lower.1.val]? = some lastColumn := by
    rw [hLowerColumn]; exact hLastColumn
  have hLastEq := (Array.getElem?_eq_some_iff.mp hLowerRead).2
  have hRootIndex : g.rootNode.1.val = p.root.column := congrArg Ref.column g.root_ref
  have hOldRoot : p.initial[g.rootNode.1.val]? = some rootColumn := by
    rw [hRootIndex, build_changed_last_preserves_prefix p.initial_build p.reduced_build p.root_before_last]
    exact hRootColumn
  have hRootEq := (Array.getElem?_eq_some_iff.mp hOldRoot).2
  have hRootRow : (Frame.ofMountain p.initial).height g.rootNode = p.rootCell.row :=
    congrArg Cell.row g.root_cell
  have hLow : (Frame.ofMountain p.reduced).height lower < row :=
    hLowerRow ▸ g.lower_lt_top.trans_le hHigh
  have hRootLow : (Frame.ofMountain p.initial).height g.rootNode < row :=
    hRootRow ▸ (p.root_row_lt_top hLast).trans_le hHigh
  calc
    row ∈ lastColumn.toList.map Cell.row ↔ row ∈ (upperSuffix p.reduced lower).map Cell.row := by
      simpa only [hLastEq] using (upperSuffix_high_rows_iff p.reduced_valid.toOrdered lower hLow).symm
    _ ↔ row ∈ (upperSuffix p.initial g.rootNode).map Cell.row := by rw [hSuffix]
    _ ↔ row ∈ rootColumn.toList.map Cell.row := by
      simpa only [hRootEq] using upperSuffix_high_rows_iff p.initial_valid.toOrdered g.rootNode hRootLow

/-- An actual adjacent upper is a barrier for every larger row occurring
in the same sparse column. There is no density assumption on rows. -/
theorem column_row_ge_upper {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    {u v : (Frame.ofMountain mountain).Node}
    (hUpper : (Frame.ofMountain mountain).upper u = some v)
    {row : Row} (hAbove : (Frame.ofMountain mountain).height u < row)
    (hMem : row ∈ mountain[u.1.val].toList.map Cell.row) :
    (Frame.ofMountain mountain).height v ≤ row := by
  obtain ⟨cell, hCell, hCellRow⟩ := List.mem_map.mp hMem
  obtain ⟨i, hRead⟩ := List.mem_iff_getElem?.mp hCell
  have hArray : mountain[u.1.val][i]? = some cell := by
    simpa only [Array.getElem?_toList] using hRead
  obtain ⟨hi, hValue⟩ := Array.getElem?_eq_some_iff.mp hArray
  have hIndex : u.2.val < i := by
    by_contra hn
    have hLe : (⟨i, hi⟩ : Fin ((Frame.ofMountain mountain).length u.1)) ≤ u.2 := Nat.le_of_not_gt hn
    have hRows := (hOrdered.rows_strict u.1).monotone hLe
    change mountain[u.1.val][i].row ≤ (Frame.ofMountain mountain).height u at hRows
    rw [hValue, hCellRow] at hRows
    exact (not_lt_of_ge hRows) hAbove
  obtain ⟨hc, hv⟩ := Frame.upper_spec hUpper
  have hvBound : v.2.val < (Frame.ofMountain mountain).length u.1 := by
    have hb := v.2.isLt
    simpa only [hc] using hb
  have hLe : (⟨v.2.val, hvBound⟩ : Fin ((Frame.ofMountain mountain).length u.1)) ≤ ⟨i, hi⟩ := by
    change v.2.val ≤ i
    omega
  have hRows := (hOrdered.rows_strict u.1).monotone hLe
  have hVHeight : ((Frame.ofMountain mountain).cells u.1 ⟨v.2.val, hvBound⟩).row =
      (Frame.ofMountain mountain).height v := by
    cases v with
    | mk c j => dsimp only at hc; subst c; rfl
  rw [hVHeight] at hRows
  change (Frame.ofMountain mountain).height v ≤ mountain[u.1.val][i].row at hRows
  simpa only [hValue, hCellRow] using hRows

theorem upperSuffix_of_upper_none {mountain : Mountain}
    {u : (Frame.ofMountain mountain).Node}
    (hNone : (Frame.ofMountain mountain).upper u = none) : upperSuffix mountain u = [] := by
  have hBound : (Frame.ofMountain mountain).length u.1 ≤ u.2.val + 1 := by
    unfold Frame.upper at hNone
    split at hNone
    · cases hNone
    · omega
  apply List.drop_eq_nil_of_le
  simpa only [Array.length_toList, Frame.ofMountain] using hBound

/-- Every reduced last-column row at least the old top lies at or above
the root's actual upper. In particular the half-open interval between
the old top and that upper contains no reduced last-column rows. -/
theorem Preparation.reduced_high_row_ge_badRoot_upper {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {lastColumn : Column}
    (hLastColumn : p.reduced[front.length]? = some lastColumn)
    {root upper : (Frame.ofMountain p.reduced).Node} (hRoot : Frame.ref root = p.root)
    (hUpper : (Frame.ofMountain p.reduced).upper root = some upper)
    {row : Row} (hHigh : p.lastTop.row ≤ row) (hMem : row ∈ lastColumn.toList.map Cell.row) :
    (Frame.ofMountain p.reduced).height upper ≤ row := by
  have hc : root.1.val = p.root.column := congrArg Ref.column hRoot
  have hRootRead := cellAt_of_frame_node p.reduced root
  rw [hRoot] at hRootRead
  have hCell : (Frame.ofMountain p.reduced).cell root = p.rootCell :=
    Except.ok.inj (hRootRead.symm.trans p.restored_root)
  have hRootRow : (Frame.ofMountain p.reduced).height root = p.rootCell.row := congrArg Cell.row hCell
  have hColumn : p.reduced[p.root.column]? = some p.reduced[root.1.val] := by
    rw [← hc]
    exact Array.getElem?_eq_getElem root.1.isLt
  exact column_row_ge_upper p.reduced_valid.toOrdered hUpper
    (hRootRow ▸ (p.root_row_lt_top hLast).trans_le hHigh)
    ((p.reduced_high_rows_iff hLast hLastColumn hColumn hHigh).mp hMem)

/-- If the actual root has no upper, its graft is empty and every row
of the reduced last column lies strictly below the old last top. -/
theorem Preparation.reduced_last_rows_lt_top_of_root_top {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {lastColumn : Column}
    (hLastColumn : p.reduced[front.length]? = some lastColumn)
    {root : (Frame.ofMountain p.reduced).Node} (hRoot : Frame.ref root = p.root)
    (hNone : (Frame.ofMountain p.reduced).upper root = none) :
    ∀ row ∈ lastColumn.toList.map Cell.row, row < p.lastTop.row := by
  intro row hMem
  by_contra hn
  have hHigh : p.lastTop.row ≤ row := le_of_not_gt hn
  have hc : root.1.val = p.root.column := congrArg Ref.column hRoot
  have hRootRead := cellAt_of_frame_node p.reduced root
  rw [hRoot] at hRootRead
  have hCell : (Frame.ofMountain p.reduced).cell root = p.rootCell :=
    Except.ok.inj (hRootRead.symm.trans p.restored_root)
  have hRootRow : (Frame.ofMountain p.reduced).height root = p.rootCell.row := congrArg Cell.row hCell
  have hColumn : p.reduced[p.root.column]? = some p.reduced[root.1.val] := by
    rw [← hc]
    exact Array.getElem?_eq_getElem root.1.isLt
  have hRootMem := (p.reduced_high_rows_iff hLast hLastColumn hColumn hHigh).mp hMem
  have hTailMem := (upperSuffix_high_rows_iff p.reduced_valid.toOrdered root
    (hRootRow ▸ (p.root_row_lt_top hLast).trans_le hHigh)).mpr hRootMem
  rw [upperSuffix_of_upper_none hNone] at hTailMem
  simp at hTailMem

end OmegaY.Expansion

#print axioms OmegaY.Expansion.normal_upperSuffix_eq_of_same_cell
#print axioms OmegaY.Expansion.Preparation.reduced_exact_root_suffix
#print axioms OmegaY.Expansion.Preparation.reduced_high_rows_iff
#print axioms OmegaY.Expansion.Preparation.reduced_high_row_ge_badRoot_upper
#print axioms OmegaY.Expansion.Preparation.reduced_last_rows_lt_top_of_root_top
