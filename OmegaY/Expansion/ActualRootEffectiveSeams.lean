/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootEffectiveSeams.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualContourRootParent
import OmegaY.Expansion.AdjacentMarkerExecution
import OmegaY.Expansion.BadRootHighQuery

/-!
# Actual root-parent contours including marker seams

The upper source cell may be a marked endpoint. Its physical copy is
derived from the actual sorted segment seam, and an original root-column
barrier proves that the interval lift fixes its row. No target adjacency
or copied numerical parent is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A real source parent in the root prefix determines its interval from
this block's actual boundary map. Its precise cap membership is retained. -/
theorem DynamicBlockState.root_parent_exact_interval
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hRootColumn : parent.1.val = p.root.column) (hPrefix : parent.2.val ≤ p.root.index) :
    ∃ a : ActualRootInterval p start ambient references parent.2.val
        ((Frame.ofMountain p.reduced).height parent),
      parent = a.root ∧ Row.bump ((Frame.ofMountain p.reduced).height parent) a.degree ∈ p.boundaries := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hParent).1
  have hRef : Frame.ref parent = ⟨p.root.column, parent.2.val⟩ := by simp only [Frame.ref, hRootColumn]
  have hOld : Canonical.cellAt p.initial ⟨p.root.column, parent.2.val⟩ = .ok (F.cell parent) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, parent.2.val⟩)
      p.initial_build p.reduced_build p.root_before_last).trans
      (by simpa only [hRef] using cellAt_of_frame_node p.reduced parent)
  obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp hOld
  obtain ⟨a0⟩ := s.actual_root_interval hLast hNodes hRead hPrefix
    (Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hReal))
  have hEq : parent = a0.root := Executable.ref_injective F (hRef.trans a0.root_ref.symm)
  obtain ⟨a, hRoot, _, hCap⟩ := s.with_exact_root_cap hLast a0
  exact ⟨a, hEq.trans hRoot.symm, hCap⟩

/-- A parent strictly below the bad root has a real upper. Its exact cap
is that upper's row, and the original father bound keeps its child below. -/
theorem ActualRootInterval.child_below_cap_of_parent_before
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref}
    {child parent : (Frame.ofMountain p.reduced).Node}
    (a : ActualRootInterval p start ambient references parent.2.val
      ((Frame.ofMountain p.reduced).height parent))
    (hLast : 1 < last) (hParentEq : parent = a.root)
    (hCap : Row.bump ((Frame.ofMountain p.reduced).height parent) a.degree ∈ p.boundaries)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hBefore : parent.2.val < p.root.index) :
    (Frame.ofMountain p.reduced).height child <
      Row.bump ((Frame.ofMountain p.reduced).height parent) a.degree := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hRootColumn : parent.1.val = p.root.column :=
    (congrArg (fun node => node.1.val) hParentEq).trans (congrArg Ref.column a.root_ref)
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hBadColumn : badRoot.1 = parent.1 := Fin.ext
    ((congrArg Ref.column hBadRef).trans hRootColumn.symm)
  have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
  have hBound : parent.2.val + 1 < F.length parent.1 := by
    have hb : p.root.index < F.length parent.1 := calc
      p.root.index = badRoot.2.val := hBadIndex.symm
      _ < F.length badRoot.1 := badRoot.2.isLt
      _ = F.length parent.1 := congrArg F.length hBadColumn
    omega
  let parentUpper : F.Node := ⟨parent.1, ⟨parent.2.val + 1, hBound⟩⟩
  have hpUpper : F.upper parent = some parentUpper := by simp only [Frame.upper, hBound, ↓reduceDIte, parentUpper]
  have hRootUpper : F.upper a.root = some parentUpper := by simpa only [hParentEq] using hpUpper
  have hCapRow := a.cap_eq_upper_of_boundary hLast hCap hBefore hRootUpper
  obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hParent
  have hBoundUpper := Frame.father_upper_bound_nodes hNormal hParent hUpper hpUpper
  have hUpperRow : F.height upper = Row.B (F.height child) (F.height parent) :=
    (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
  rw [hCapRow]
  exact (show F.height child < F.height upper by rw [hUpperRow]; exact Row.lt_B _ _).trans_le hBoundUpper

set_option maxHeartbeats 800000 in
/-- Within the actual root-parent interval, every unmarked source child
has the correct effective edge, including when its source upper is itself
marked. Wrappers below derive the interval and cap test from source data. -/
theorem DynamicBlockState.actual_interval_root_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next rootIndex : Nat}
    {rootRow : Row} (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hParentEq : parent = a.root) (hChildColumn : child.1.val = next)
    (hChildCap : (Frame.ofMountain p.reduced).height child < Row.bump rootRow a.degree)
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (rootCopy : EffectiveRootReference p start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef rootCopy.reference := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hParentReal := Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hParent).1
  have hRootRow : F.height a.root = rootRow := a.root_row
  have hRootCol : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hRootIndex : a.root.2.val ≤ p.root.index := (congrArg Ref.index a.root_ref).trans_le a.root_prefix
  have hConeParent : Frame.RootCone F a.root parent := by
    rw [← hParentEq]
    exact ⟨parent, hParentReal, rfl, rfl, .refl parent⟩
  obtain ⟨hCone, hRootLower⟩ := Frame.root_cone_child_of_parent hNormal hParent hConeParent
    (by rw [← hParentEq])
  have hInside : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) child :=
    ⟨hCone, hRootLower, by simpa only [hRootRow] using hChildCap⟩
  have hBarrier : ∀ upper, F.upper a.root = some upper →
      Row.bump (F.height a.root) a.degree ≤ F.height upper := by
    simpa only [hRootRow] using a.root_upper_barrier
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  have hUpperRef : Frame.ref sourceUpper = ⟨child.1.val, child.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead := d.frame_source_read hSource (rfl : child.1.val = child.1.val)
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    have hr := d.frame_source_read hSource (congrArg Fin.val (Frame.upper_spec hUpper).1)
    simpa only [(Frame.upper_spec hUpper).2] using hr
  have hQuery : referenceAt ambient references (F.height a.root) = .ok a.target.row := by
    simpa only [hRootRow] using a.ambient_query
  obtain ⟨marker, hm, hMarkerRow, hTargetRow⟩ := d.prepared_active_parent_marker_data
    hSource a.root_real hRootCol hRootIndex hInside rfl s.next_lower hQuery
  let md := d.marker_data marker hm
  have hBefore : marker.index ≤ child.2.val := by
    by_contra hn
    have hLt := d.source_valid.rows_strict _ _ _ _ hChildRead md.current_at (Nat.lt_of_not_ge hn)
    change F.height child < md.current.row at hLt
    rw [show md.current.row = F.height a.root from hMarkerRow] at hLt
    exact (not_lt_of_ge hRootLower) hLt
  have hAfter : marker.index < child.2.val := by
    have hMember : marker.index ∈ d.bucket.map Ref.index := List.mem_map.mpr ⟨marker, hm, rfl⟩
    have hNe : marker.index ≠ child.2.val := fun he => hUnmarked (he ▸ hMember)
    omega
  have hNoBetween := d.prepared_no_markers_through_source_index hSource hRootCol hBarrier
    hm hMarkerRow hChildRead hInside.2.2
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  have hReadRow := read.output_row_of_marker hm hBefore hNoBetween
  obtain ⟨upper, candidate, hUpperOut, hCopy, hShape⟩ : ∃ upper candidate,
      column[read.outputIndex + 1]? = some upper ∧
      copyEdge ambient (Frame.ref sourceUpper)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift rootRow a.target.row (F.height sourceUpper)) = .ok candidate ∧
      SameShape candidate upper := by
    by_cases hMarkedUpper : child.2.val + 1 ∈ d.bucket.map Ref.index
    · obtain ⟨upper, candidate, hUpperOut, _, hCopy, hShape⟩ :=
        d.effective_upper_marker_execution hParentPower hParentLow hNoPremature read hSourceUpper hMarkedUpper
      obtain ⟨higher, hHigher, hHigherIndex⟩ := List.mem_map.mp hMarkedUpper
      have hHigherRef : higher = Frame.ref sourceUpper := by
        rw [hUpperRef]
        cases higher
        simp only [Ref.mk.injEq]
        exact ⟨d.marker_columns _ hHigher, hHigherIndex⟩
      have hUpperMem : BucketMem p.marked child.1.val (Frame.ref sourceUpper) := hHigherRef ▸ hHigher
      have hLowerUpper : F.height a.root < F.height sourceUpper := by
        have hB : F.height sourceUpper = Row.B (F.height child) (F.height parent) :=
          (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
        rw [hB]
        exact hRootLower.trans_lt (Row.lt_B _ _)
      have hNoOpen := marker_not_in_open_interval hNormal.toOrdered
        (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
        p.root_valid p.markers_built hRootCol hBarrier hUpperMem (cellAt_of_frame_node p.reduced sourceUpper)
      have hCapUpper : Row.bump rootRow a.degree ≤ F.height sourceUpper := by
        apply le_of_not_gt
        intro hn
        have hn' : F.height sourceUpper < Row.bump (F.height a.root) a.degree := by
          rw [hRootRow]
          exact hn
        exact hNoOpen ⟨hLowerUpper, hn'⟩
      have hFixed := Row.lift_eq_of_ge_cap a.target_lower a.target_below hCapUpper
      refine ⟨upper, candidate, hUpperOut, ?_, hShape⟩
      rw [hFixed, hUpperRef]
      exact hCopy
    · have hNoBetweenUpper : ∀ middle, marker.index < middle → middle ≤ child.2.val + 1 →
          middle ∉ d.bucket.map Ref.index := by
        intro middle hLo hHi
        by_cases hLe : middle ≤ child.2.val
        · exact hNoBetween middle hLo hLe
        · have he : middle = child.2.val + 1 := by omega
          exact he ▸ hMarkedUpper
      obtain ⟨position, lower, upper, candidate, hLowerOut, hUpperOut,
          hLowerRow, _, hCopy, hShape⟩ := d.copyColumn_source_adjacent_execution
        hParentPower hParentLow hNoPremature hRun hm hChildRead hSourceUpper hAfter hNoBetweenUpper
      obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
      have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
      subst actual
      have hPosition : position = read.outputIndex := column_read_index_eq_of_row
        hValid hLowerOut read.output_at (hLowerRow.trans hReadRow.symm)
      refine ⟨upper, candidate, hPosition ▸ hUpperOut, ?_, hShape⟩
      change copyEdge ambient ⟨child.1.val, child.2.val + 1⟩
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift md.current.row md.targetCell.row (F.height sourceUpper)) = .ok candidate at hCopy
      have hLow : md.current.row = rootRow := hMarkerRow.trans hRootRow
      have hTarget : md.targetCell.row = a.target.row := hTargetRow
      rw [hLow, hTarget] at hCopy
      rw [hUpperRef]
      exact hCopy
  obtain ⟨rootRead, hReferenceEq, _⟩ := s.exact_effective_root_reference hLast a hParentEq
  obtain ⟨hActualCopy, _, _, _, _, _⟩ := s.copyEdge_root_parent_below_cap
    a hParent hParentEq rfl hUpper hChildCap
  have hCandidate : candidate =
      (⟨Row.lift rootRow a.target.row (F.height sourceUpper), 0, some a.reference⟩ : Cell) :=
    Except.ok.inj (hCopy.symm.trans hActualCopy)
  let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  let rootCopy := rootRead.extend (PreservesColumns.push ambient column)
  refine ⟨childCopy, rootCopy, rfl, rfl, read.outputCell, upper,
    rootRead.target, read.output_read, ?_, ?_, rootCopy.result_read⟩
  · exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
      EffectiveCopyRead.outputRef], hUpperOut⟩
  · have hLeft : upper.left = some a.reference := hShape.2.symm.trans (congrArg Cell.left hCandidate)
    simpa only [rootCopy, EffectiveRootReference.extend, hReferenceEq] using hLeft

/-- All upper-marker cases are included for a parent strictly below the
bad root. The actual interval and the child's cap test are both derived. -/
theorem DynamicBlockState.actual_lower_root_effective_parent_all_uppers
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRootColumn : parent.1.val = p.root.column)
    (hBefore : parent.2.val < p.root.index)
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (rootCopy : EffectiveRootReference p start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef rootCopy.reference := by
  obtain ⟨a, hParentEq, hCap⟩ := s.root_parent_exact_interval hLast hParent hRootColumn hBefore.le
  exact s.actual_interval_root_effective_parent hLast a hParent hParentEq hChildColumn
    (a.child_below_cap_of_parent_before hLast hParentEq hCap hParent hBefore) hUnmarked hRun

/-- For the bad root itself, low children use its exact reference cap;
high children use high-boundary support derived from the real outer loop.
Both cases select the same root-row reference, including stationary high
queries and marked source uppers. -/
theorem DynamicBlockState.actual_badRoot_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hParentRef : Frame.ref parent = p.root) (hChildColumn : child.1.val = next)
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (rootCopy : EffectiveRootReference p start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef rootCopy.reference := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hRootColumn : parent.1.val = p.root.column := congrArg Ref.column hParentRef
  have hRootIndex : parent.2.val = p.root.index := congrArg Ref.index hParentRef
  obtain ⟨a, hParentEq, hCapMem⟩ := s.root_parent_exact_interval hLast hParent hRootColumn hRootIndex.le
  have hCap := a.cap_eq_lastTop_of_boundary hCapMem hRootIndex
  by_cases hLow : F.height child < p.lastTop.row
  · exact s.actual_interval_root_effective_parent hLast a hParent hParentEq rfl
      (by simpa only [hCap] using hLow) hUnmarked hRun
  · have hHigh : p.lastTop.row ≤ F.height child := le_of_not_gt hLow
    obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
    obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
    have hSource : p.reduced[child.1.val]? = some d.sources :=
      (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
    have hChildRead := d.frame_source_read hSource (rfl : child.1.val = child.1.val)
    have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
      have hr := d.frame_source_read hSource (congrArg Fin.val (Frame.upper_spec hUpper).1)
      simpa only [(Frame.upper_spec hUpper).2] using hr
    have hUpperRef : Frame.ref sourceUpper = ⟨child.1.val, child.2.val + 1⟩ := by
      simp only [Frame.ref, Ref.mk.injEq]
      exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
    obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
    obtain ⟨upper, candidate, hUpperOut, _, hCopy, hShape⟩ := s.effective_high_upper_execution
      hLast child.1.isLt d hParentPower hParentLow hNoPremature read hSourceUpper hHigh
    have hBadRef : Frame.ref a.root = p.root := (congrArg Frame.ref hParentEq).symm.trans hParentRef
    obtain ⟨hBelow, _, _, _, _⟩ := s.below_badRoot_high_query hLast hStartRun
      a hBadRef hCap hParent hParentRef hUpper hHigh
    have hUpperRow : F.height sourceUpper = Row.B (F.height child) (F.height parent) :=
      (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
    have hHighUpper : Row.bump (F.height parent) a.degree ≤ F.height sourceUpper := by
      rw [hCap, hUpperRow]
      exact hHigh.trans (Row.lt_B _ _).le
    have hFixed := Row.lift_eq_of_ge_cap a.target_lower a.target_below hHighUpper
    have hSelected : below ambient (start.size - 1)
        (Row.lift (F.height parent) a.target.row (F.height sourceUpper)) = .ok a.reference := by
      rw [hFixed, ← s.boundary_copy_index]
      exact hBelow
    obtain ⟨hExpected, _, _, _, _, _⟩ :=
      s.copyEdge_root_parent_of_below a hParent hParentEq rfl hUpper hSelected
    have hCandidate : candidate =
        (⟨F.height sourceUpper, 0, some a.reference⟩ : Cell) := by
      rw [hFixed, hUpperRef] at hExpected
      exact Except.ok.inj (hCopy.symm.trans hExpected)
    obtain ⟨rootRead, hReferenceEq, _⟩ := s.exact_effective_root_reference hLast a hParentEq
    let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
      ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
    let rootCopy := rootRead.extend (PreservesColumns.push ambient column)
    refine ⟨childCopy, rootCopy, rfl, rfl, read.outputCell, upper,
      rootRead.target, read.output_read, ?_, ?_, rootCopy.result_read⟩
    · exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
        EffectiveCopyRead.outputRef], hUpperOut⟩
    · have hLeft : upper.left = some a.reference := hShape.2.symm.trans (congrArg Cell.left hCandidate)
      simpa only [rootCopy, EffectiveRootReference.extend, hReferenceEq] using hLeft

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.root_parent_exact_interval
#print axioms OmegaY.Expansion.DynamicBlockState.actual_interval_root_effective_parent
#print axioms OmegaY.Expansion.DynamicBlockState.actual_lower_root_effective_parent_all_uppers
#print axioms OmegaY.Expansion.DynamicBlockState.actual_badRoot_effective_parent
