/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNextBoundaryAll.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNextBoundaryPath

/-!
# Every actual next boundary in a lower root interval

A marked source frontier below the interval cap must sit at the root row.
Its actual source upper is the successor row. Source selector maximality
then forces the cap to be that successor, and the actual reference target
to stay at the root row. The real marker-copy successor supplies the output
selector barrier. Thus no source marker restriction remains for low roots.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem source_marker_parent_row {front : List Nat} {last : Nat}
    (p : Preparation front last) {source parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source)) :
    (Frame.ofMountain p.reduced).height parent = (Frame.ofMountain p.reduced).height source := by
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  obtain ⟨hRight, low, _, hColumn, _, hPath, hRow⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mp hMarked
  cases hPath with
  | refl =>
      have hc := congrArg Fin.val hColumn
      omega
  | @cons source actual low hActual tail =>
      have he : actual = parent := Option.some.inj (hActual.symm.trans hParent)
      subst actual
      exact le_antisymm (Frame.P_height_le hNormal.toOrdered hParent)
        (by rw [hRow]; exact tail.height_le hNormal.toOrdered)

/-- A genuinely marked source's effective occurrence has a real immediate
successor. Its height is one ordinal successor above the actual target;
the statement includes zero gaps and consecutive physical source markers. -/
theorem EffectiveCopyOccurrence.marked_successor_read
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source parent : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result) (hLast : 1 < last)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source)) :
    ∃ upper, Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok upper ∧
      upper.row = Row.bump copy.read.outputCell.row 0 := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  let md := d.marker_data (Frame.ref source) hMarked
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hParent
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hCurrent : md.current = F.cell source := Option.some.inj
    (md.current_at.symm.trans (d.frame_source_read hSources rfl))
  have hUpperSource : d.sources[source.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSources (congrArg Fin.val (Frame.upper_spec hSourceUpper).1)
    simpa only [(Frame.upper_spec hSourceUpper).2] using hRead
  have hUpperCell : md.upper = F.cell sourceUpper := Option.some.inj
    (md.upper_at.symm.trans hUpperSource)
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨actualParent, hActual, hB, _, hStored⟩ :=
    hNormal.upper_step source sourceUpper hSourceReal hSourceUpper
  have he : actualParent = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actualParent
  have hParentRef : md.sourceParent = Frame.ref parent := Option.some.inj
    (md.upper_left.symm.trans (by simpa only [hUpperCell] using hStored))
  have hEqualRows := source_marker_parent_row p hParent hMarked
  have hSuccessor : md.upper.row = Row.bump md.current.row 0 := by
    rw [hUpperCell, hCurrent]
    change F.height sourceUpper = Row.bump (F.height source) 0
    rw [hB, hEqualRows, Row.B_self]
  have hParentRight : p.root.column ≤ parent.1.val := by
    by_contra hn
    exact p.fixed_parent_not_marked hParent (Nat.lt_of_not_ge hn) hMarked
  have hRoot : p.root.column ≤ md.sourceParent.column := by
    rw [hParentRef]
    exact hParentRight
  have hReference := copy.read.marked_reference hMarked
  have hLowerRow : copy.read.outputCell.row = md.targetCell.row := Except.ok.inj
    (hReference.symm.trans (by simpa only [hCurrent] using md.reference))
  obtain ⟨hNoPremature, hParentPower, hParentLow⟩ :=
    copy.state.column_data_parent_inputs hLast source.1.isLt d
  obtain ⟨upper, hUpperAt, hUpperRow, _⟩ := d.effective_marker_upper
    hParentPower hParentLow hNoPremature copy.read.copy_run hMarked hSuccessor hRoot
      copy.read.output_at hLowerRow
  have hRead : Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok upper :=
    cellAt_ok_iff.mpr ⟨copy.column,
      copy.preserved.column_read (by simp [EffectiveCopyOccurrence.outputRef, EffectiveCopyRead.outputRef]),
      hUpperAt⟩
  exact ⟨upper, hRead, by simpa only [hLowerRow] using hUpperRow⟩

/-- A marked source frontier and source-upper cap barrier force the
interval target to stay at its root, not merely below an arbitrary cap. -/
theorem EffectiveCopyOccurrence.marked_cap_successor
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result ambient : Mountain} {references : List Ref}
    {source sourceUpper parent : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump rootRow a.degree) source)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    (hUpperCap : Row.bump rootRow a.degree ≤ (Frame.ofMountain p.reduced).height sourceUpper)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source)) :
    (Frame.ofMountain p.reduced).height source = rootRow ∧
      Row.bump rootRow a.degree = Row.bump rootRow 0 ∧ a.target.row = rootRow ∧
      copy.read.outputCell.row = rootRow := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hNoOpen := marker_not_in_open_interval p.reduced_valid.toOrdered
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    p.root_valid p.markers_built (congrArg Ref.column a.root_ref) a.root_upper_barrier
      hMarked (Canonical.cellAt_of_frame_node p.reduced source)
  have hSourceRow : F.height source = rootRow := by
    have hLower : rootRow ≤ F.height source := by simpa only [a.root_row] using hInside.2.1
    apply le_antisymm _ hLower
    by_contra hn
    have hStrict : F.height a.root < F.height source := by
      rw [a.root_row]
      exact lt_of_not_ge hn
    exact hNoOpen ⟨hStrict, hInside.2.2⟩
  have hParentRow := source_marker_parent_row p hParent hMarked
  have hSuccessor : F.height sourceUpper = Row.bump rootRow 0 := by
    have hB := (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
    rw [hParentRow, Row.B_self, hSourceRow] at hB
    exact hB
  have hCap : Row.bump rootRow a.degree = Row.bump rootRow 0 := le_antisymm
    (hUpperCap.trans_eq hSuccessor) (Row.bump_mono_exponent rootRow (Nat.zero_le _))
  have hTarget : a.target.row = rootRow := by
    have hHigh : a.target.row < Row.bump rootRow 0 := by simpa only [hCap] using a.target_below
    exact (Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero
      (Row.jump_le_of_lt_bump a.target_lower hHigh))).symm
  have hLift := copy.interval_row a hInside copy.state.next_lower
  have hOutput : copy.read.outputCell.row = rootRow := by
    change copy.read.outputCell.row = Row.lift rootRow a.target.row (F.height source) at hLift
    simpa only [hSourceRow, Row.lift_at_root, hTarget] using hLift
  exact ⟨hSourceRow, hCap, hTarget, hOutput⟩

/-- Every source frontier in a real root interval is the actual copied
selector below that cap. Source marker membership is exhausted internally. -/
theorem EffectiveCopyOccurrence.below_interval_cap
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result ambient : Mountain} {references : List Ref}
    {source sourceUpper parent : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hValid : MountainValid result) (hLast : 1 < last)
    {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump rootRow a.degree) source)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    (hUpperCap : Row.bump rootRow a.degree ≤ (Frame.ofMountain p.reduced).height sourceUpper) :
    below result copy.outputRef.column (Row.bump rootRow a.degree) = .ok copy.outputRef := by
  by_cases hMarked : BucketMem p.marked source.1.val (Frame.ref source)
  · obtain ⟨_, hCap, _, hOutput⟩ := copy.marked_cap_successor a hInside hParent hUpper hUpperCap hMarked
    obtain ⟨upper, hRead, hRow⟩ := copy.marked_successor_read hLast hParent hMarked
    have hBelow : copy.read.outputCell.row < Row.bump rootRow a.degree := by
      rw [hOutput, hCap]
      exact Row.lt_bump _ _
    have hUpperRow : upper.row = Row.bump rootRow a.degree := by
      rw [hRow, hOutput, hCap]
    obtain ⟨nodes, hNodes, hLowerAt⟩ := cellAt_ok_iff.mp copy.output_read
    obtain ⟨other, hOther, hUpperAt⟩ := cellAt_ok_iff.mp hRead
    have he : other = nodes := Option.some.inj (hOther.symm.trans hNodes)
    subst other
    exact below_eq_of_adjacent hValid hNodes hLowerAt hUpperAt hBelow hUpperRow.ge
  · have hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index := by
      intro hm
      obtain ⟨marker, hMember, hIndex⟩ := List.mem_map.mp hm
      have hColumn := copy.data.marker_columns marker hMember
      have he : marker = Frame.ref source := congrArg₂ Ref.mk hColumn hIndex
      exact hMarked (he ▸ hMember)
    exact copy.below_interval_cap_of_nonmarker hValid hLast a hInside hParent hUpper hUpperCap hUnmarked


private theorem next_path_root_cone {F : Frame} (hF : F.Normal) {u root : F.Node}
    (hRoot : Frame.Real root) (path : Frame.ParentPath F u root) : Frame.RootCone F root u := by
  induction path with
  | refl root => exact ⟨root, hRoot, rfl, rfl, .refl _⟩
  | cons hParent tail ih =>
      exact (Frame.root_cone_child_of_parent hF hParent (ih hRoot)
        (tail.height_le hF.toOrdered)).1

/-- A completed block's actual selector in any lower root interval has a
real raw-parent path to the actual selector in the block's start. Both
selectors use the same original root-upper cut. There is no source marker
restriction and neither selector identity nor the path is assumed. -/
theorem DynamicBlockState.next_low_boundary_path
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper)
    {source : (Frame.ofMountain p.reduced).Node}
    (hSourceBelow : below p.reduced (p.reduced.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
      .ok (Frame.ref source)) :
    ∃ (sourceRoot : (Frame.ofMountain p.reduced).Node)
      (sourceCopy : EffectiveCopyOccurrence p block start references source ambient)
      (rootCopy : EffectiveRootEndpoint p start references sourceRoot ambient),
      Frame.ref sourceRoot = Frame.ref root ∧
      (Frame.ofMountain p.reduced).cell sourceRoot = (Frame.ofMountain p.initial).cell root ∧
      below ambient (ambient.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
        .ok sourceCopy.outputRef ∧
      below start (start.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
        .ok rootCopy.reference ∧
      RawRefPath ambient sourceCopy.outputRef rootCopy.reference := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨reducedRoot, reducedUpper, hRootRef, hRootCell, hUpperRef, hUpperCell,
      hReducedUpper, hReducedReal, _, hSourceColumn, hSourceLow, hSourceHigh, hSourcePath⟩ :=
    p.low_boundary_source_data hLast hRootReal hRootColumn hBefore hRootUpper hSourceBelow
  have hReducedRootColumn : reducedRoot.1.val = p.root.column :=
    (congrArg Ref.column hRootRef).trans hRootColumn
  have hRootNodes : p.initial[p.root.column]? = some p.initial[root.1.val] := by
    rw [← hRootColumn]
    exact Array.getElem?_eq_getElem root.1.isLt
  have hRootAt : p.initial[root.1.val][root.2.val]? = some (F.cell root) :=
    Array.getElem?_eq_getElem root.2.isLt
  have hRootPositive : 0 < (F.cell root).row :=
    Row.zero_lt_one.trans_le (Frame.one_le_height (build_normal_of_success p.initial_build).toOrdered hRootReal)
  obtain ⟨a⟩ := s.actual_root_interval hLast hRootNodes hRootAt hBefore.le hRootPositive
  have haRoot : a.root = reducedRoot := by
    apply Executable.ref_injective G
    rw [a.root_ref, hRootRef]
    exact congrArg₂ Ref.mk hRootColumn.symm rfl
  obtain ⟨b, hbRoot, _, hCapMember⟩ := s.with_exact_root_cap hLast a
  have hbRoot' : b.root = reducedRoot := hbRoot.trans haRoot
  have hCap : Row.bump (F.height root) b.degree = F.height rootUpper :=
    (b.cap_eq_upper_of_boundary hLast hCapMember hBefore
      (by simpa only [hbRoot'] using hReducedUpper)).trans (congrArg Cell.row hUpperCell)
  have hPath : Frame.ParentPath G source b.root := by simpa only [hbRoot'] using hSourcePath
  have hInside : Frame.RootInterval G b.root (Row.bump (F.height root) b.degree) source :=
    ⟨next_path_root_cone hNormal b.root_real hPath,
      by simpa only [hbRoot'] using hSourceLow, by simpa only [hCap] using hSourceHigh⟩
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRight : p.root.column < source.1.val := by
    have hRootBefore := p.root_before_last
    omega
  obtain ⟨sourceCopy⟩ := s.prior_effective_occurrence history hLast hRight source.1.isLt
  have hParentExists : ∃ parent, G.P source = some parent := by
    cases hPath with
    | refl =>
        have hc : b.root.1.val = p.root.column := congrArg Ref.column b.root_ref
        omega
    | @cons child parent root hParent tail => exact ⟨parent, hParent⟩
  obtain ⟨parent, hParent⟩ := hParentExists
  obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hParent
  have hSourceUpperRef : Frame.ref sourceUpper =
      ⟨(Frame.ref source).column, (Frame.ref source).index + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hSourceUpper).1, (Frame.upper_spec hSourceUpper).2⟩
  have hSourceUpperRead : Canonical.cellAt p.reduced
      ⟨(Frame.ref source).column, (Frame.ref source).index + 1⟩ = .ok (G.cell sourceUpper) := by
    rw [← hSourceUpperRef]
    exact Canonical.cellAt_of_frame_node p.reduced sourceUpper
  have hUpperBarrier : Row.bump (F.height root) b.degree ≤ G.height sourceUpper := by
    rw [hCap]
    exact below_parent_upper_bound_at hSourceBelow hSourceUpperRead
  have hSelected : below ambient sourceCopy.outputRef.column (Row.bump (F.height root) b.degree) =
      .ok sourceCopy.outputRef := sourceCopy.below_interval_cap s.ambient_valid hLast b
        hInside hParent hSourceUpper hUpperBarrier
  have hOutputColumn : sourceCopy.outputRef.column = ambient.size - 1 := by
    have hc := sourceCopy.source_column
    have hs := s.size_eq
    omega
  obtain ⟨selectedRoot, hSelectedRoot, _⟩ := s.exact_effective_root_reference hLast b rfl
  let rootCopy : EffectiveRootEndpoint p start references b.root ambient := .selected selectedRoot
  have hStartSelected : below start (start.size - 1) (F.height rootUpper) = .ok rootCopy.reference := by
    change below start (start.size - 1) (F.height rootUpper) = .ok selectedRoot.reference
    rw [hSelectedRoot, ← hCap]
    exact b.start_below
  have hNewPath := s.recorded_effective_path_to_root history hLast hStartRun hPath
    (congrArg Ref.column b.root_ref) hRight source.1.isLt sourceCopy rootCopy
  exact ⟨b.root, sourceCopy, rootCopy, by rw [hbRoot']; exact hRootRef,
    by rw [hbRoot']; exact hRootCell,
    by simpa only [hOutputColumn, hCap] using hSelected, hStartSelected, hNewPath⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.marked_successor_read
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.marked_cap_successor
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.below_interval_cap
#print axioms OmegaY.Expansion.DynamicBlockState.next_low_boundary_path
