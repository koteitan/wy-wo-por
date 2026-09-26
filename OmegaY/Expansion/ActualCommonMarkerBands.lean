/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonMarkerBands.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CommonMarkerBands
import OmegaY.Expansion.HistoryColumnData
import OmegaY.Expansion.BlockEquations

/-!
# Common marker comparison from an actual within-block history

Earlier source columns are recovered from the real copy history. The next
column, its input-side parent support, and its successful copy are supplied
by the dynamic step theorem. Numerical sums are reconstructed from the
actual block-start prefix and all recorded completed-column executions.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Every column after the block start is the result of one actual recorded
copy. Their real finish equations, transported into the current mountain,
supply all sums. There is no recognition or copied Normal premise. -/
theorem DynamicBlockState.mountainSums_of_history {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient)
    (hStart : MountainSums start) : MountainSums ambient := by
  intro c hc
  by_cases hOld : c < start.size
  · have hRead : ambient[c]? = some start[c] :=
      s.start_preserved.column_read (Array.getElem?_eq_getElem hOld)
    have hEq : start[c] = ambient[c] := Option.some.inj
      (hRead.symm.trans (Array.getElem?_eq_getElem hc))
    rw [← hEq]
    exact (hStart c hOld).imp (fun _ _ hSum => hSum.preserve s.start_preserved)
  · let shift := block * (p.reduced.size - 1 - p.root.column)
    let sourceColumn := c - shift
    have hLower : p.root.column < sourceColumn := by
      have hs := s.start_size
      dsimp only [sourceColumn, shift]
      omega
    have hUpper : sourceColumn < next := by
      have hs := s.size_eq
      dsimp only [sourceColumn, shift]
      omega
    have hIndex : sourceColumn + shift = c := by
      have hs := s.start_size
      dsimp only [sourceColumn, shift]
      omega
    obtain ⟨before, column, _, hRun, hPreserve, hRead⟩ := history.column_read hLower hUpper
    have hReadAt : ambient[c]? = some column := by
      change ambient[sourceColumn + shift]? = some column at hRead
      simpa only [hIndex] using hRead
    have hEq : column = ambient[c] := Option.some.inj
      (hReadAt.symm.trans (Array.getElem?_eq_getElem hc))
    rw [← hEq]
    have hBefore : PreservesColumns before ambient :=
      (PreservesColumns.push before column).trans hPreserve
    exact (copyColumn_finished_of_success hRun).adjacent_sums.imp
      (fun _ _ hSum => hSum.preserve hBefore)

/-- A genuine finite outer-loop prefix provides the initial sums needed
above, so no numerical-sum invariant is required from the caller. -/
theorem DynamicBlockState.mountainSums_of_start_run {front : List Nat} {last : Nat}
    {p : Preparation front last} {block copies : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start) : MountainSums ambient := by
  obtain ⟨actual, hActual, _, hSums, _⟩ := p.blocks_equations hLast copies
  have hEq : actual = start := Except.ok.inj (hActual.symm.trans hStartRun)
  exact s.mountainSums_of_history history (hEq ▸ hSums)

/-- In one actual block, recover the earlier blocker column and construct
the current column. All copy data, parent support, selected target, final
reads and numerical invariants are conclusions of the real history.
The remaining comparison concerns only the two actual effective endpoints. -/
theorem DynamicBlockState.actual_common_marker_bands {front : List Nat} {last : Nat}
    {p : Preparation front last} {block copies : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {u z parent zUpper : (Frame.ofMountain p.reduced).Node}
    (hUColumn : u.1.val = next)
    (hZColumn : z.1.val < u.1.val)
    (hUParent : (Frame.ofMountain p.reduced).P u = some parent)
    (hZParent : (Frame.ofMountain p.reduced).P z = some parent)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some zUpper)
    (hOrder : (Frame.ofMountain p.reduced).height z ≤ (Frame.ofMountain p.reduced).height u)
    (hBefore : (Frame.ofMountain p.reduced).height u < (Frame.ofMountain p.reduced).height zUpper)
    (hParentRight : p.root.column ≤ parent.1.val)
    (hUMarker : BucketMem p.marked (Frame.ref u).column (Frame.ref u)) :
    ∃ (uColumn zColumn : Column) (target : Row),
      copyColumn ambient p.marked references u.1.val
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok uColumn ∧
      (ambient.push uColumn)[ambient.size]? = some uColumn ∧
      (ambient.push uColumn)[z.1.val + block * (p.reduced.size - 1 - p.root.column)]? = some zColumn ∧
      referenceAt start references ((Frame.ofMountain p.reduced).height parent) = .ok target ∧
      ∃ pair : CommonMarkerBandPair uColumn zColumn ((Frame.ofMountain p.reduced).height parent) target,
        (bandValue uColumn pair.leftBand.start 0 ≤ bandValue zColumn pair.rightBand.start 0 ↔
          bandValue uColumn pair.leftBand.start pair.gap.length ≤
            bandValue zColumn pair.rightBand.start pair.gap.length) ∧
        (bandValue uColumn pair.leftBand.start 0 < bandValue zColumn pair.rightBand.start 0 ↔
          bandValue uColumn pair.leftBand.start pair.gap.length <
            bandValue zColumn pair.rightBand.start pair.gap.length) := by
  let F := Frame.ofMountain p.reduced
  have hNormal : F.Normal := build_normal_of_success p.reduced_build
  have hZRight : p.root.column < z.1.val :=
    hParentRight.trans_lt (Frame.P_column_lt hNormal.toOrdered hZParent)
  obtain ⟨before, zColumn, sz, hZRun, hZPreserve, hZRead⟩ :=
    history.column_read hZRight (hZColumn.trans_eq hUColumn)
  have su : DynamicBlockState p block start references u.1.val ambient := by
    simpa only [hUColumn] using s
  obtain ⟨du, _, hUPP, hUPL⟩ := su.column_data hLast u.1.isLt
  obtain ⟨dz, _, hZPP, hZPL⟩ := sz.column_data hLast z.1.isLt
  have hUSource : p.reduced[u.1.val]? = some du.sources :=
    (su.base_ambient _ u.1.isLt).symm.trans du.source_column
  have hZSource : p.reduced[z.1.val]? = some dz.sources :=
    (sz.base_ambient _ z.1.isLt).symm.trans dz.source_column
  have hPreserve : PreservesColumns before ambient :=
    (PreservesColumns.push before zColumn).trans hZPreserve
  have hRefs : ∀ ref ∈ references, ValidRef before ref := by
    intro ref hRef
    exact sz.start_preserved.validRef
      (RootRowsInColumn.references_valid s.boundary_rows s.reference_map ref hRef)
  obtain ⟨rootNodes, hRootNodes, hRootRead⟩ := Canonical.cellAt_ok_iff.mp p.restored_root
  obtain ⟨hRootColumnBound, hRootColumnEq⟩ := Array.getElem?_eq_some_iff.mp hRootNodes
  have hRootIndex : p.root.index < p.reduced[p.root.column].size := by
    rw [hRootColumnEq]
    exact (Array.getElem?_eq_some_iff.mp hRootRead).1
  let root : F.Node := ⟨⟨p.root.column, hRootColumnBound⟩, ⟨p.root.index, hRootIndex⟩⟩
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := p.markers_built
  obtain ⟨uColumn, hURun, hFinished, _, _, hFinalValid⟩ := du.copyColumn_valid
  obtain ⟨pair⟩ := build_common_parent_marker_bands p.reduced_build hMarkers hUParent hZParent
    hZUpper hOrder hBefore hParentRight du dz hUSource hZSource hUPP hUPL hZPP hZPL
    hPreserve hRefs hURun hZRun hUMarker
  let md := du.marker_data (Frame.ref u) hUMarker
  have hUCell : md.current = F.cell u := Except.ok.inj
    ((Canonical.cellAt_ok_iff.mpr (show ∃ nodes, p.reduced[(Frame.ref u).column]? = some nodes ∧
      nodes[(Frame.ref u).index]? = some md.current from ⟨du.sources, hUSource, md.current_at⟩)).symm.trans
      (Canonical.cellAt_of_frame_node p.reduced u))
  obtain ⟨_, _, hURow, _, _⟩ := build_common_parent_marker_rows p.reduced_build hMarkers
    hUParent hZParent hZUpper hOrder hBefore hParentRight (.inl hUMarker)
  have hTarget : referenceAt start references (F.height parent) = .ok md.targetCell.row := by
    have hRead := (su.referenceAt_preserved md.current.row).symm.trans md.reference
    have hRow : md.current.row = F.height parent := by rw [hUCell]; exact hURow
    simpa only [hRow] using hRead
  have hFinalU : (ambient.push uColumn)[ambient.size]? = some uColumn := by simp
  have hFinalZ : (ambient.push uColumn)[z.1.val + block * (p.reduced.size - 1 - p.root.column)]? =
      some zColumn := (PreservesColumns.push ambient uColumn).column_read hZRead
  have hFinalSums : MountainSums (ambient.push uColumn) :=
    (s.mountainSums_of_start_run history hLast hStartRun).push hFinished
  exact ⟨uColumn, zColumn, md.targetCell.row, hURun, hFinalU, hFinalZ, hTarget,
    pair, pair.compare hFinalSums hFinalValid hFinalU hFinalZ⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.mountainSums_of_history
#print axioms OmegaY.Expansion.DynamicBlockState.mountainSums_of_start_run
#print axioms OmegaY.Expansion.DynamicBlockState.actual_common_marker_bands
