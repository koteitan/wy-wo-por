/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNextHighestBoundary.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BoundaryRecordPath
import OmegaY.Expansion.ActualMixedCommonParentUpper
import OmegaY.Expansion.ActualNextBoundaryPath

/-!
# The next highest boundary when the original bad root has a parent

The initial decrement graft makes the highest reduced reference point
directly to the original bad root's parent, which is strictly left of the
root column. Its actual effective copy in every completed block remains
the new selector below the original terminal top. Hence the new highest
reference has a direct raw edge to that same fixed original parent, not
to the previous block's highest reference or to the bad root itself.

The parentless bad-root case has no such outgoing edge and is not asserted
by this module. No copied numerical parent recognition is used.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A genuine effective occurrence of a source row below the terminal
top remains below it. This uses the actual controlling reference cap,
including the phantom case, and does not assume row density. -/
theorem EffectiveCopyOccurrence.row_lt_lastTop
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last) (hLow : (Frame.ofMountain p.reduced).height source < p.lastTop.row) :
    copy.read.outputCell.row < p.lastTop.row := by
  let md := copy.data.marker_data copy.read.marker copy.read.marker_mem
  obtain ⟨degree, hTarget, hCap⟩ := copy.state.marker_caps_below_lastTop
    hLast copy.data source.1.isLt copy.read.marker copy.read.marker_mem
  rw [copy.read.output_row]
  change Row.lift md.current.row md.targetCell.row ((Frame.ofMountain p.reduced).height source) < p.lastTop.row
  by_cases hInside : (Frame.ofMountain p.reduced).height source < Row.bump md.current.row degree
  · exact (Row.lift_mem_interval md.target_lower hTarget copy.read.source_lower hInside).2.trans_le hCap
  · rw [Row.lift_eq_of_ge_cap md.target_lower hTarget (le_of_not_gt hInside)]
    exact hLow

/-- The source selector's actual upper barrier and its fixed-parent
upper execution determine the new selector. The output effective node
and its consecutive upper are not supplied as hypotheses. -/
theorem EffectiveCopyOccurrence.below_lastTop_of_fixed_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source parent : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hValid : MountainValid result) (hLast : 1 < last)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hFixed : parent.1.val < p.root.column)
    (hSourceBelow : below p.reduced source.1.val p.lastTop.row = .ok (Frame.ref source)) :
    below result copy.outputRef.column p.lastTop.row = .ok copy.outputRef := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceColumn := Array.getElem?_eq_getElem source.1.isLt
  obtain ⟨_, found, hFound, hLow⟩ := below_result hSourceColumn hSourceBelow
  have hFoundEq : found = F.cell source := Option.some.inj
    (hFound.symm.trans (Array.getElem?_eq_getElem source.2.isLt))
  have hSourceLow : F.height source < p.lastTop.row := by
    change (F.cell source).row < p.lastTop.row
    rw [← hFoundEq]
    exact hLow
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  have hUpperRef : Frame.ref sourceUpper =
      ⟨(Frame.ref source).column, (Frame.ref source).index + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  have hSourceUpperRead : Canonical.cellAt p.reduced
      ⟨(Frame.ref source).column, (Frame.ref source).index + 1⟩ = .ok (F.cell sourceUpper) := by
    rw [← hUpperRef]
    exact cellAt_of_frame_node p.reduced sourceUpper
  have hBarrier : p.lastTop.row ≤ F.height sourceUpper :=
    below_parent_upper_bound_at hSourceBelow hSourceUpperRead
  obtain ⟨upper, hUpperRead, hUpperRow⟩ := copy.fixed_parent_upper_read hLast hParent hFixed hUpper
  obtain ⟨nodes, hNodes, hLowerAt⟩ := cellAt_ok_iff.mp copy.output_read
  obtain ⟨other, hOther, hUpperAt⟩ := cellAt_ok_iff.mp hUpperRead
  have he : other = nodes := Option.some.inj (hOther.symm.trans hNodes)
  subst other
  exact below_eq_of_adjacent hValid hNodes hLowerAt hUpperAt
    (copy.row_lt_lastTop hLast hSourceLow) (hUpperRow ▸ hBarrier)

private theorem real_of_positive_height {F : Frame} (hF : F.Ordered) {u : F.Node}
    (hHeight : 0 < F.height u) : Frame.Real u := by
  by_contra hn
  have hi : u.2.val = 0 := by unfold Frame.Real at hn; omega
  have hi' : u.2 = ⟨0, by have := u.2.isLt; omega⟩ := Fin.ext hi
  change 0 < (F.cells u.1 u.2).row at hHeight
  rw [hi', hF.phantom] at hHeight
  exact (lt_irrefl (0 : Row)) hHeight

/-- At the end of every actual block, the new highest reference has a
single stored edge to the original bad root's fixed numerical parent.
Its source selector, effective occurrence, new selector and full parent
read are all derived. No outer-loop or target-path assumption is needed. -/
theorem DynamicBlockState.next_highest_boundary_edge
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient)
    (hLast : 1 < last) (g : RootGeometry p)
    {parent : (Frame.ofMountain p.initial).Node}
    (hParent : (Frame.ofMountain p.initial).P g.rootNode = some parent) :
    ∃ (source : (Frame.ofMountain p.reduced).Node)
      (copy : EffectiveCopyOccurrence p block start references source ambient),
      below p.reduced (p.reduced.size - 1) p.lastTop.row = .ok (Frame.ref source) ∧
      source.1.val = p.reduced.size - 1 ∧
      below ambient (ambient.size - 1) p.lastTop.row = .ok copy.outputRef ∧
      RawRefEdge ambient copy.outputRef (Frame.ref parent) ∧
      Canonical.cellAt ambient (Frame.ref parent) = .ok ((Frame.ofMountain p.initial).cell parent) ∧
      copy.read.outputCell.row < p.lastTop.row := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hParentFixed : parent.1.val < p.root.column := by
    have hp := Frame.P_column_lt (build_normal_of_success p.initial_build).toOrdered hParent
    simpa only [show g.rootNode.1.val = p.root.column from congrArg Ref.column g.root_ref] using hp
  obtain ⟨source, hSourceBelow, hSourceColumn, hSourceEdge, hParentRead, hSourceLow, hSourceHigh⟩ :=
    p.initial_badRoot_reference_edge hLast g hParent
  obtain ⟨reducedParent, hReducedRef, hReducedCell⟩ := Canonical.frame_node_of_cellAt hParentRead
  have hReducedFixed : reducedParent.1.val < p.root.column :=
    (congrArg Ref.column hReducedRef).trans_lt hParentFixed
  have hRootPositive : 0 < p.rootCell.row := by
    have hp := Row.zero_lt_one.trans_le
      (Frame.one_le_height (build_normal_of_success p.initial_build).toOrdered g.root_real)
    change 0 < (F.cell g.rootNode).row at hp
    have hc : F.cell g.rootNode = p.rootCell := g.root_cell
    rw [hc] at hp
    exact hp
  have hSourceReal : Frame.Real source := real_of_positive_height hNormal.toOrdered
    (hRootPositive.trans_le hSourceLow)
  have hRaw : G.rawParent source = some reducedParent := hSourceEdge.rawParent rfl hReducedRef
  have hSourceParent : G.P source = some reducedParent :=
    (hNormal.rawParent_eq_P hSourceReal).symm.trans hRaw
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRight : p.root.column < source.1.val := by
    have hBefore := p.root_before_last
    omega
  obtain ⟨copy⟩ := s.prior_effective_occurrence history hLast hRight source.1.isLt
  have hSelected : below ambient copy.outputRef.column p.lastTop.row = .ok copy.outputRef :=
    copy.below_lastTop_of_fixed_parent s.ambient_valid hLast hSourceParent hReducedFixed
      (by simpa only [hSourceColumn] using hSourceBelow)
  have hOutputColumn : copy.outputRef.column = ambient.size - 1 := by
    have hc := copy.source_column
    have hs := s.size_eq
    omega
  obtain ⟨hEdge, hRead⟩ := s.recorded_fixed_parent history hLast hSourceParent
    hRight source.1.isLt hReducedFixed copy
  exact ⟨source, copy, hSourceBelow, hSourceColumn,
    by simpa only [hOutputColumn] using hSelected,
    by simpa only [hReducedRef] using hEdge,
    by simpa only [hReducedRef, hReducedCell] using hRead,
    copy.row_lt_lastTop hLast hSourceHigh⟩

/-- The root-geometry witness is constructed internally from the actual
preparation. The only parent premise is a successful source search at
the original bad-root reference. -/
theorem DynamicBlockState.next_highest_boundary_edge_of_actual_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient)
    (hLast : 1 < last) {parent : (Frame.ofMountain p.initial).Node}
    (hParent : Canonical.findParent p.initial p.root = .ok (Frame.ref parent)) :
    ∃ (source : (Frame.ofMountain p.reduced).Node)
      (copy : EffectiveCopyOccurrence p block start references source ambient),
      below p.reduced (p.reduced.size - 1) p.lastTop.row = .ok (Frame.ref source) ∧
      source.1.val = p.reduced.size - 1 ∧
      below ambient (ambient.size - 1) p.lastTop.row = .ok copy.outputRef ∧
      RawRefEdge ambient copy.outputRef (Frame.ref parent) ∧
      Canonical.cellAt ambient (Frame.ref parent) = .ok ((Frame.ofMountain p.initial).cell parent) ∧
      copy.read.outputCell.row < p.lastTop.row := by
  obtain ⟨g⟩ := p.root_geometry hLast
  have hp : (Frame.ofMountain p.initial).P g.rootNode = some parent :=
    (Executable.findParent_ref_iff (build_normal_of_success p.initial_build).toOrdered g.rootNode parent).mp
      (by simpa only [g.root_ref] using hParent)
  exact s.next_highest_boundary_edge history hLast g hp

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.row_lt_lastTop
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.below_lastTop_of_fixed_parent
#print axioms OmegaY.Expansion.DynamicBlockState.next_highest_boundary_edge
#print axioms OmegaY.Expansion.DynamicBlockState.next_highest_boundary_edge_of_actual_parent
