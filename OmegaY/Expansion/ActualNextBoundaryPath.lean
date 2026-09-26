/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNextBoundaryPath.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialBoundaryFrontierPath
import OmegaY.Expansion.RecordedRootPaths
import OmegaY.Expansion.ActualCommonParentUpper

/-!
# Actual next-boundary paths in a lower root interval

The selected source frontier is not assumed to be the new boundary
reference. For a nonmarker source frontier, its actual immediate upper
and the source selector's upper barrier prove that identification. The
source path is constructed by the initial lower-root projection and then
transported through the real copy history to this block's old boundary.

The main theorem below covers roots strictly below the bad root and a
nonmarker source frontier. Marker frontiers and the bad-root interval
are not claimed here.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem real_of_positive_height {F : Frame} (hF : F.Ordered) {u : F.Node}
    (hHeight : 0 < F.height u) : Frame.Real u := by
  by_contra hn
  have hi : u.2.val = 0 := by unfold Frame.Real at hn; omega
  have hi' : u.2 = ⟨0, by have := u.2.isLt; omega⟩ := Fin.ext hi
  change 0 < (F.cells u.1 u.2).row at hHeight
  rw [hi', hF.phantom] at hHeight
  exact (lt_irrefl (0 : Row)) hHeight

private theorem path_root_cone {F : Frame} (hF : F.Normal) {u root : F.Node}
    (hRoot : Frame.Real root) (path : Frame.ParentPath F u root) : Frame.RootCone F root u := by
  induction path with
  | refl root => exact ⟨root, hRoot, rfl, rfl, .refl _⟩
  | cons hParent tail ih =>
      exact (Frame.root_cone_child_of_parent hF hParent (ih hRoot) (tail.height_le hF.toOrdered)).1

/-- The output selector is recovered from two actual consecutive reads.
In particular, no assumption says the new reference is an effective copy.
The source successor may itself be a marker. -/
theorem EffectiveCopyOccurrence.below_interval_cap_of_nonmarker
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
    (hUpperCap : Row.bump rootRow a.degree ≤ (Frame.ofMountain p.reduced).height sourceUpper)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index) :
    below result copy.outputRef.column (Row.bump rootRow a.degree) = .ok copy.outputRef := by
  have hLower : rootRow ≤ (Frame.ofMountain p.reduced).height source := by
    simpa only [a.root_row] using hInside.2.1
  have hLift := copy.interval_row a hInside copy.state.next_lower
  have hBelow : copy.read.outputCell.row < Row.bump rootRow a.degree := by
    rw [hLift]
    exact (Row.lift_mem_interval a.target_lower a.target_below hLower hInside.2.2).2
  obtain ⟨upper, hRead, hRow⟩ :=
    copy.upper_read_of_lower_lift hLast hUnmarked hParent hUpper hLower hLift
  have hUpperRow : upper.row = (Frame.ofMountain p.reduced).height sourceUpper :=
    hRow.trans (Row.lift_eq_of_ge_cap a.target_lower a.target_below hUpperCap)
  obtain ⟨nodes, hNodes, hLowerAt⟩ := cellAt_ok_iff.mp copy.output_read
  obtain ⟨other, hOther, hUpperAt⟩ := cellAt_ok_iff.mp hRead
  have he : other = nodes := Option.some.inj (hOther.symm.trans hNodes)
  subst other
  exact below_eq_of_adjacent hValid hNodes hLowerAt hUpperAt hBelow (hUpperRow ▸ hUpperCap)

/-- All source data below are recovered from the actual initial/reduced
builds and the real reduced selector. No source ancestry path is an input. -/
theorem Preparation.low_boundary_source_data
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper)
    {source : (Frame.ofMountain p.reduced).Node}
    (hBelow : below p.reduced (p.reduced.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
      .ok (Frame.ref source)) :
    ∃ reducedRoot reducedUpper : (Frame.ofMountain p.reduced).Node,
      Frame.ref reducedRoot = Frame.ref root ∧
      (Frame.ofMountain p.reduced).cell reducedRoot = (Frame.ofMountain p.initial).cell root ∧
      Frame.ref reducedUpper = Frame.ref rootUpper ∧
      (Frame.ofMountain p.reduced).cell reducedUpper = (Frame.ofMountain p.initial).cell rootUpper ∧
      (Frame.ofMountain p.reduced).upper reducedRoot = some reducedUpper ∧
      Frame.Real reducedRoot ∧ Frame.Real source ∧ source.1.val = p.reduced.size - 1 ∧
      (Frame.ofMountain p.reduced).height reducedRoot ≤ (Frame.ofMountain p.reduced).height source ∧
      (Frame.ofMountain p.reduced).height source < (Frame.ofMountain p.initial).height rootUpper ∧
      Frame.ParentPath (Frame.ofMountain p.reduced) source reducedRoot := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hRootLeft : root.1.val < front.length := hRootColumn ▸ p.root_before_last
  have hUpperLeft : rootUpper.1.val < front.length :=
    (congrArg Fin.val (Frame.upper_spec hRootUpper).1).trans_lt hRootLeft
  have hRootRead : Canonical.cellAt p.reduced (Frame.ref root) = .ok (F.cell root) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hRootLeft).symm.trans
      (Canonical.cellAt_of_frame_node p.initial root)
  have hUpperRead : Canonical.cellAt p.reduced (Frame.ref rootUpper) = .ok (F.cell rootUpper) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hUpperLeft).symm.trans
      (Canonical.cellAt_of_frame_node p.initial rootUpper)
  obtain ⟨reducedRoot, hRootRef, hRootCell⟩ := Canonical.frame_node_of_cellAt hRootRead
  obtain ⟨reducedUpper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hOldUpperRef : Frame.ref rootUpper = ⟨(Frame.ref root).column, (Frame.ref root).index + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hRootUpper).1, (Frame.upper_spec hRootUpper).2⟩
  have hUpper : G.upper reducedRoot = some reducedUpper :=
    Frame.upper_of_refs hRootRef (hUpperRef.trans hOldUpperRef)
  have hReducedReal : Frame.Real reducedRoot := by
    have hi : reducedRoot.2.val = root.2.val := congrArg Ref.index hRootRef
    change 0 < reducedRoot.2.val
    rw [hi]
    exact hRootReal
  obtain ⟨selected, cell, hSelected, hRead, hLow, hHigh, hPath⟩ :=
    p.initial_low_root_reference_path hLast hRootReal hRootColumn hBefore hRootUpper
  have hSelectedEq : selected = Frame.ref source := Except.ok.inj (hSelected.symm.trans hBelow)
  subst selected
  have hSourceCell : G.cell source = cell := Except.ok.inj
    ((Canonical.cellAt_of_frame_node p.reduced source).symm.trans hRead)
  have hSourceLow : G.height reducedRoot ≤ G.height source := by
    change (G.cell reducedRoot).row ≤ (G.cell source).row
    rw [hRootCell, hSourceCell]
    exact hLow
  have hSourceHigh : G.height source < F.height rootUpper := by
    change (G.cell source).row < F.height rootUpper
    rw [hSourceCell]
    exact hHigh
  have hSourceReal : Frame.Real source := real_of_positive_height hNormal.toOrdered
    ((Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hReducedReal)).trans_le hSourceLow)
  have hSourceColumn : source.1.val = p.reduced.size - 1 :=
    (below_result (Array.getElem?_eq_getElem p.reduced_last_exists) hBelow).1
  have hNumerical : Frame.ParentPath G source reducedRoot :=
    hPath.toParentPath hNormal.toOrdered (bound := p.reduced.size)
      (fun _ _ hReal => hNormal.rawParent_eq_P hReal) rfl hRootRef hSourceReal source.1.isLt
  exact ⟨reducedRoot, reducedUpper, hRootRef, hRootCell, hUpperRef, hUpperCell,
    hUpper, hReducedReal, hSourceReal, hSourceColumn, hSourceLow, hSourceHigh, hNumerical⟩

/-- A completed actual block has a new low-root boundary reference with
a genuine path to that source root's endpoint in this block's start.
The only branch restriction is that the *source* last-column frontier is
unmarked. Its selected effective occurrence and the target path are outputs. -/
theorem DynamicBlockState.next_low_boundary_path_of_nonmarker
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
      .ok (Frame.ref source))
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index) :
    ∃ (sourceRoot : (Frame.ofMountain p.reduced).Node)
      (sourceCopy : EffectiveCopyOccurrence p block start references source ambient)
      (rootCopy : EffectiveRootEndpoint p start references sourceRoot ambient),
      Frame.ref sourceRoot = Frame.ref root ∧
      (Frame.ofMountain p.reduced).cell sourceRoot = (Frame.ofMountain p.initial).cell root ∧
      below ambient (ambient.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
        .ok sourceCopy.outputRef ∧
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
    ⟨path_root_cone hNormal b.root_real hPath,
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
      .ok sourceCopy.outputRef := sourceCopy.below_interval_cap_of_nonmarker s.ambient_valid hLast b
        hInside hParent hSourceUpper hUpperBarrier hUnmarked
  have hOutputColumn : sourceCopy.outputRef.column = ambient.size - 1 := by
    have hc := sourceCopy.source_column
    have hs := s.size_eq
    omega
  obtain ⟨selectedRoot, _, _⟩ := s.exact_effective_root_reference hLast b rfl
  let rootCopy : EffectiveRootEndpoint p start references b.root ambient := .selected selectedRoot
  have hNewPath := s.recorded_effective_path_to_root history hLast hStartRun hPath
    (congrArg Ref.column b.root_ref) hRight source.1.isLt sourceCopy rootCopy
  exact ⟨b.root, sourceCopy, rootCopy, by rw [hbRoot']; exact hRootRef,
    by rw [hbRoot']; exact hRootCell,
    by simpa only [hOutputColumn, hCap] using hSelected, hNewPath⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.below_interval_cap_of_nonmarker
#print axioms OmegaY.Expansion.Preparation.low_boundary_source_data
#print axioms OmegaY.Expansion.DynamicBlockState.next_low_boundary_path_of_nonmarker
