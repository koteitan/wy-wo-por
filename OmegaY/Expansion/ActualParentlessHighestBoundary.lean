/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualParentlessHighestBoundary.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNextHighestBoundary
import OmegaY.Expansion.CopiedParentTop

/-!
# Parentless highest references are genuine terminal nodes

`Canonical.findParent` returns `Except BuildError Ref`, not `Option Ref`.
Absence of a numerical parent is expressed by its `toOption = none`,
using the executable/typed-search equivalence on the actual source.

If the original bad root has no parent, its graft has no upper tail.
The old penultimate node is therefore the reduced last-column top.
Actual highest-contour copying places its effective occurrence at the
new column top, below Z, with value one and no stored outgoing parent.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem upper_none_of_parent_none {F : Frame} (hNormal : F.Normal)
    {u : F.Node} (hReal : Frame.Real u) (hNone : F.P u = none) : F.upper u = none := by
  cases hUpper : F.upper u with
  | none => rfl
  | some upper =>
      obtain ⟨parent, hParent, _⟩ := hNormal.upper_step u upper hReal hUpper
      rw [hNone] at hParent
      cases hParent

private theorem value_one_of_upper_none {F : Frame} (hNormal : F.Normal)
    {u : F.Node} (hReal : Frame.Real u) (hNone : F.upper u = none) : F.value u = 1 := by
  have hPositive := hNormal.real_positive u hReal
  by_contra hn
  obtain ⟨upper, hUpper⟩ := hNormal.upper_exists u hReal (by omega)
  rw [hNone] at hUpper
  cases hUpper

/-- The actual graft identifies the source highest selector precisely:
it is the decremented old penultimate reference and now has no upper. -/
theorem Preparation.initial_parentless_highest_source
    {front : List Nat} {last : Nat} (p : Preparation front last)
    (hLast : 1 < last) (g : RootGeometry p)
    (hNone : (Frame.ofMountain p.initial).P g.rootNode = none) :
    ∃ source : (Frame.ofMountain p.reduced).Node,
      Frame.ref source = Frame.ref g.lower ∧
      source.1.val = p.reduced.size - 1 ∧
      below p.reduced (p.reduced.size - 1) p.lastTop.row = .ok (Frame.ref source) ∧
      Frame.Real source ∧ (Frame.ofMountain p.reduced).upper source = none ∧
      (Frame.ofMountain p.reduced).value source = 1 ∧
      (Frame.ofMountain p.reduced).height source < p.lastTop.row := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hOldNormal := build_normal_of_success p.initial_build
  have hNormal := build_normal_of_success p.reduced_build
  have hRootTop := upper_none_of_parent_none hOldNormal g.root_real hNone
  obtain ⟨source, hRef, hCell, hTail⟩ := p.reduced_exact_root_suffix hLast g
  have hSourceTop : G.upper source = none := by
    rw [upperSuffix_of_upper_none hRootTop] at hTail
    cases hUpper : G.upper source with
    | none => rfl
    | some upper =>
        rw [upperSuffix_of_upper hUpper] at hTail
        cases hTail
  have hSourceReal : Frame.Real source := by
    have hi : source.2.val = g.lower.2.val := congrArg Ref.index hRef
    change 0 < source.2.val
    rw [hi]
    exact g.lower_real
  have hSourceLow : G.height source < p.lastTop.row := by
    change (G.cell source).row < p.lastTop.row
    rw [hCell, decCell_row]
    exact g.lower_lt_top
  have hSourceColumn : source.1.val = p.reduced.size - 1 := by
    have hc := congrArg Ref.column hRef
    have hs := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hs
    change source.1.val = g.lower.1.val at hc
    rw [hc, g.lower_column]
    omega
  have hNoNext : ¬ source.2.val + 1 < G.length source.1 := by
    intro hn
    simp only [Frame.upper, hn, ↓reduceDIte] at hSourceTop
    cases hSourceTop
  have hLastIndex : source.2.val = p.reduced[source.1.val].size - 1 := by
    have hb := source.2.isLt
    change ¬ source.2.val + 1 < p.reduced[source.1.val].size at hNoNext
    change source.2.val < p.reduced[source.1.val].size at hb
    omega
  have hAt : p.reduced[source.1.val][p.reduced[source.1.val].size - 1]? = some (G.cell source) := by
    rw [← hLastIndex]
    exact Array.getElem?_eq_getElem source.2.isLt
  have hBelow := below_eq_of_top (Array.getElem?_eq_getElem source.1.isLt) hAt hSourceLow
  refine ⟨source, hRef, hSourceColumn, ?_, hSourceReal, hSourceTop,
    value_one_of_upper_none hNormal hSourceReal hSourceTop, hSourceLow⟩
  have hBelow' : below p.reduced source.1.val p.lastTop.row = .ok (Frame.ref source) := by
    have hSelected : (⟨source.1.val, p.reduced[source.1.val].size - 1⟩ : Ref) = Frame.ref source :=
      congrArg₂ Ref.mk rfl hLastIndex.symm
    exact hBelow.trans (congrArg (fun ref => (Except.ok ref : Result Ref)) hSelected)
  exact (congrArg (fun c => below p.reduced c p.lastTop.row) hSourceColumn).symm.trans hBelow'

/-- Actual source-top copying places the effective occurrence at the
last output index and gives it value one. The maximal controlling marker
is inferred from the real effective-occurrence certificate. -/
theorem EffectiveCopyOccurrence.top_of_source_top
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last) (hSourceTop : (Frame.ofMountain p.reduced).upper source = none) :
    copy.read.outputIndex = copy.column.size - 1 ∧ copy.read.outputCell.value = 1 := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  have hSource : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hSourceAt := d.frame_source_read hSource (rfl : source.1.val = source.1.val)
  have hSize : F.length source.1 = d.sources.size :=
    congrArg Array.size (Array.getElem?_eq_some_iff.mp hSource).2
  change F.upper source = none at hSourceTop
  have hNoNext : ¬ source.2.val + 1 < d.sources.size := by
    intro hn
    have hn' : source.2.val + 1 < F.length source.1 := lt_of_lt_of_eq hn hSize.symm
    simp only [Frame.upper, hn', ↓reduceDIte] at hSourceTop
    cases hSourceTop
  have hSourceLast : source.2.val = d.sources.size - 1 := by
    have hb := (Array.getElem?_eq_some_iff.mp hSourceAt).1
    omega
  have hHighest : ∀ marker ∈ d.bucket, marker.index ≤ copy.read.marker.index := by
    intro marker hm
    by_contra hn
    have hMarkerBefore : marker.index < d.sources.size - 1 := d.marker_before_source_top hm
    exact copy.read.no_between marker.index (Nat.lt_of_not_ge hn)
      (by omega) (List.mem_map.mpr ⟨marker, hm, rfl⟩)
  obtain ⟨hNoPrem, hPP', hPL'⟩ := copy.state.column_data_parent_inputs hLast source.1.isLt d
  obtain ⟨top, hTop, hTopRow, hTopValue⟩ := d.copyColumn_lifted_source_top
    hPP' hPL' hNoPrem copy.read.copy_run copy.read.marker_mem hHighest
      (by simpa only [hSourceLast] using hSourceAt)
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = copy.column := Except.ok.inj (hActual.symm.trans copy.read.copy_run)
  subst actual
  have hIndex : copy.read.outputIndex = copy.column.size - 1 :=
    column_read_index_eq_of_row hValid copy.read.output_at hTop
      (copy.read.output_row.trans hTopRow.symm)
  have hCell : copy.read.outputCell = top := Option.some.inj
    (copy.read.output_at.symm.trans (by simpa only [hIndex] using hTop))
  exact ⟨hIndex, (congrArg Cell.value hCell).trans hTopValue⟩

/-- In a completed real block the parentless highest selector is the
actual effective copy of the decremented penultimate source. It is a real
value-one terminal with no upper and hence no raw outgoing edge. -/
theorem DynamicBlockState.next_parentless_highest_terminal
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient)
    (hLast : 1 < last) (g : RootGeometry p)
    (hNone : (Frame.ofMountain p.initial).P g.rootNode = none) :
    ∃ (source : (Frame.ofMountain p.reduced).Node)
      (copy : EffectiveCopyOccurrence p block start references source ambient)
      (terminal : (Frame.ofMountain ambient).Node),
      Frame.ref source = Frame.ref g.lower ∧
      below p.reduced (p.reduced.size - 1) p.lastTop.row = .ok (Frame.ref source) ∧
      (Frame.ofMountain p.reduced).upper source = none ∧
      Frame.ref terminal = copy.outputRef ∧
      below ambient (ambient.size - 1) p.lastTop.row = .ok (Frame.ref terminal) ∧
      terminal.1.val = ambient.size - 1 ∧ Frame.Real terminal ∧
      (Frame.ofMountain ambient).value terminal = 1 ∧
      (Frame.ofMountain ambient).upper terminal = none ∧
      (Frame.ofMountain ambient).rawParent terminal = none ∧
      (Frame.ofMountain ambient).height terminal < p.lastTop.row := by
  let T := Frame.ofMountain ambient
  obtain ⟨source, hSourceRef, hSourceColumn, hSourceBelow, hSourceReal,
    hSourceTop, _, hSourceLow⟩ := p.initial_parentless_highest_source hLast g hNone
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRight : p.root.column < source.1.val := by
    have hBefore := p.root_before_last
    omega
  obtain ⟨copy⟩ := s.prior_effective_occurrence history hLast hRight source.1.isLt
  obtain ⟨hTopIndex, hTopValue⟩ := copy.top_of_source_top hLast hSourceTop
  have hLow := copy.row_lt_lastTop hLast hSourceLow
  have hNodes : ambient[copy.outputRef.column]? = some copy.column :=
    copy.preserved.column_read (by simp [EffectiveCopyOccurrence.outputRef, EffectiveCopyRead.outputRef])
  have hTopRead : copy.column[copy.column.size - 1]? = some copy.read.outputCell := by
    simpa only [hTopIndex] using copy.read.output_at
  have hBelow := below_eq_of_top hNodes hTopRead hLow
  have hRefIndex : (⟨copy.outputRef.column, copy.column.size - 1⟩ : Ref) = copy.outputRef := by
    exact congrArg₂ Ref.mk rfl hTopIndex.symm
  have hSelected : below ambient copy.outputRef.column p.lastTop.row = .ok copy.outputRef :=
    hBelow.trans (congrArg (fun ref => (Except.ok ref : Result Ref)) hRefIndex)
  have hOutputColumn : copy.outputRef.column = ambient.size - 1 := by
    have hc := copy.source_column
    have hs := s.size_eq
    omega
  obtain ⟨terminal, hTerminalRef, hTerminalCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
  have hTerminalColumn : terminal.1.val = copy.outputRef.column := congrArg Ref.column hTerminalRef
  have hTerminalIndex : terminal.2.val = copy.read.outputIndex := congrArg Ref.index hTerminalRef
  have hTerminalLength : T.length terminal.1 = copy.column.size := by
    have hColumn : ambient[terminal.1.val]? = some copy.column := by
      simpa only [hTerminalColumn] using hNodes
    exact congrArg Array.size (Array.getElem?_eq_some_iff.mp hColumn).2
  have hNoNext : ¬ terminal.2.val + 1 < T.length terminal.1 := by omega
  have hUpperNone : T.upper terminal = none := by
    simp only [Frame.upper, hNoNext, ↓reduceDIte]
  have hValue : T.value terminal = 1 := (congrArg Cell.value hTerminalCell).trans hTopValue
  have hHeight : T.height terminal < p.lastTop.row := by
    change (T.cell terminal).row < p.lastTop.row
    rw [hTerminalCell]
    exact hLow
  refine ⟨source, copy, terminal, hSourceRef, hSourceBelow, hSourceTop, hTerminalRef,
    ?_, hTerminalColumn.trans hOutputColumn, ?_, hValue, hUpperNone,
    Frame.rawParent_none_of_upper_none hUpperNone, hHeight⟩
  · exact (congrArg (fun c => below ambient c p.lastTop.row) hOutputColumn).symm.trans
      (hSelected.trans (congrArg (fun ref => (Except.ok ref : Result Ref)) hTerminalRef.symm))
  · change 0 < terminal.2.val
    rw [hTerminalIndex]
    exact copy.read.output_real hSourceReal

/-- Executable absence uses `toOption = none`: `findParent` itself has
no `.ok none` constructor. On the actual built source this is equivalent
to the typed numerical parent being absent, so no malformed-graph error
is being treated as evidence for a terminal. -/
theorem DynamicBlockState.next_parentless_highest_terminal_of_actual_search
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient)
    (hLast : 1 < last)
    (hNone : (Canonical.findParent p.initial p.root).toOption = none) :
    ∃ (source : (Frame.ofMountain p.reduced).Node)
      (copy : EffectiveCopyOccurrence p block start references source ambient)
      (terminal : (Frame.ofMountain ambient).Node),
      below p.reduced (p.reduced.size - 1) p.lastTop.row = .ok (Frame.ref source) ∧
      (Frame.ofMountain p.reduced).upper source = none ∧
      Frame.ref terminal = copy.outputRef ∧
      below ambient (ambient.size - 1) p.lastTop.row = .ok (Frame.ref terminal) ∧
      terminal.1.val = ambient.size - 1 ∧ Frame.Real terminal ∧
      (Frame.ofMountain ambient).value terminal = 1 ∧
      (Frame.ofMountain ambient).upper terminal = none ∧
      (Frame.ofMountain ambient).rawParent terminal = none ∧
      (Frame.ofMountain ambient).height terminal < p.lastTop.row := by
  obtain ⟨g⟩ := p.root_geometry hLast
  have hMapNone : ((Frame.ofMountain p.initial).P g.rootNode).map Frame.ref = none :=
    (Executable.findParent_toOption (build_normal_of_success p.initial_build).toOrdered g.rootNode).symm.trans
      (by simpa only [g.root_ref] using hNone)
  have hParentNone : (Frame.ofMountain p.initial).P g.rootNode = none := by
    cases hp : (Frame.ofMountain p.initial).P g.rootNode with
    | none => rfl
    | some parent => simp only [hp, Option.map_some] at hMapNone; cases hMapNone
  obtain ⟨source, copy, terminal, _, hSourceBelow, hSourceTop, hRef, hBelow,
    hColumn, hReal, hOne, hUpper, hRaw, hLow⟩ := s.next_parentless_highest_terminal history hLast g hParentNone
  exact ⟨source, copy, terminal, hSourceBelow, hSourceTop, hRef, hBelow,
    hColumn, hReal, hOne, hUpper, hRaw, hLow⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_parentless_highest_source
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.top_of_source_top
#print axioms OmegaY.Expansion.DynamicBlockState.next_parentless_highest_terminal
#print axioms OmegaY.Expansion.DynamicBlockState.next_parentless_highest_terminal_of_actual_search
