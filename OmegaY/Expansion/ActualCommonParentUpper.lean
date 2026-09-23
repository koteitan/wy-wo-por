/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonParentUpper.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRaisedSeamParent
import OmegaY.Expansion.ContourFatherBound
import OmegaY.Expansion.CommonParentDepthWord

/-!
# Actual common upper rows of copied source blockers

All occurrences below contain their real local state, completed copy run,
and column preservation. The copied frame need not have numerical parents.
For nonmarker sources, an actual immediate upper follows the same row lift
as the source edge, including a physical-marker seam. A raised common-parent
pair shares an actual source root interval; stationary pairs keep the old
upper row. This proves copied upper-row synchrony from actual execution.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem frame_upper_of_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : Frame.ref before = ⟨column, index⟩)
    (hAfter : Frame.ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref} {result : Mountain}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- The actual immediate output upper has the source upper's full contour
lift. If the upper is itself a marker, its physical row is fixed by the
preceding actual reference cap, and gives the same formula. -/
theorem upper_lift_read (hLast : 1 < last)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper) :
    ∃ upper,
      Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok upper ∧
      upper.row = Row.lift
        (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row
        (copy.data.marker_data copy.read.marker copy.read.marker_mem).targetCell.row
        ((Frame.ofMountain p.reduced).height sourceUpper) := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  let md := d.marker_data copy.read.marker copy.read.marker_mem
  obtain ⟨hNoPremature, hParentPower, hParentLow⟩ :=
    copy.state.column_data_parent_inputs hLast source.1.isLt d
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hSourceUpper : d.sources[source.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSources (congrArg Fin.val (Frame.upper_spec hUpper).1)
    simpa only [(Frame.upper_spec hUpper).2] using hRead
  obtain ⟨upper, hRead, hRow⟩ : ∃ upper,
      copy.column[copy.read.outputIndex + 1]? = some upper ∧
      upper.row = Row.lift md.current.row md.targetCell.row (F.height sourceUpper) := by
    by_cases hMarked : source.2.val + 1 ∈ d.bucket.map Ref.index
    · obtain ⟨upper, _, hRead, hRow, _, _⟩ :=
        d.effective_upper_marker_execution hParentPower hParentLow hNoPremature copy.read hSourceUpper hMarked
      obtain ⟨marker, hm, hi⟩ := List.mem_map.mp hMarked
      have hOrder : copy.read.marker.index < marker.index := by have := copy.read.marker_before; omega
      have hCell : (d.marker_data marker hm).current = F.cell sourceUpper := Option.some.inj
        ((d.marker_data marker hm).current_at.symm.trans (by simpa only [hi] using hSourceUpper))
      obtain ⟨degree, hTarget, hCap⟩ :=
        d.reference_caps copy.read.marker copy.read.marker_mem marker hm hOrder
      have hFixed : Row.lift md.current.row md.targetCell.row (F.height sourceUpper) =
          F.height sourceUpper := Row.lift_eq_of_ge_cap md.target_lower hTarget
            (by simpa only [hCell, Frame.height] using hCap)
      exact ⟨upper, hRead, hRow.trans hFixed.symm⟩
    · have hAfter : copy.read.marker.index < source.2.val := by
        have hLe := copy.read.marker_before
        have hNe : copy.read.marker.index ≠ source.2.val := by
          intro he
          exact hUnmarked (he ▸ List.mem_map.mpr ⟨copy.read.marker, copy.read.marker_mem, rfl⟩)
        omega
      have hNoBetween : ∀ middle, copy.read.marker.index < middle → middle ≤ source.2.val + 1 →
          middle ∉ d.bucket.map Ref.index := by
        intro middle hlo hhi
        by_cases hBefore : middle ≤ source.2.val
        · exact copy.read.no_between middle hlo hBefore
        · exact (show middle = source.2.val + 1 by omega) ▸ hMarked
      obtain ⟨index, lower, upper, _, hLowerRead, hUpperRead, hLowerRow, hUpperRow, _, _⟩ :=
        d.copyColumn_source_adjacent_execution hParentPower hParentLow hNoPremature copy.read.copy_run
          copy.read.marker_mem copy.read.source_at hSourceUpper hAfter hNoBetween
      obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
      have he : actual = copy.column := Except.ok.inj (hActual.symm.trans copy.read.copy_run)
      subst actual
      have hIndex : index = copy.read.outputIndex := column_read_index_eq_of_row hValid
        hLowerRead copy.read.output_at (hLowerRow.trans copy.read.output_row.symm)
      exact ⟨upper, by simpa only [hIndex] using hUpperRead, hUpperRow⟩
  exact ⟨upper, cellAt_ok_iff.mpr ⟨copy.column,
    copy.preserved.column_read (by simp [outputRef, EffectiveCopyRead.outputRef]), hRead⟩, hRow⟩

/-- A known common lift at the lower effective node determines its actual
upper through the source power step. Equality of controlling-marker records
is not required, and no output power/canonicality premise is used. -/
theorem upper_read_of_lower_lift (hLast : 1 < last)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {sourceUpper parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    {root target : Row} (hRoot : root ≤ (Frame.ofMountain p.reduced).height source)
    (hLower : copy.read.outputCell.row =
      Row.lift root target ((Frame.ofMountain p.reduced).height source)) :
    ∃ upper,
      Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok upper ∧
      upper.row = Row.lift root target ((Frame.ofMountain p.reduced).height sourceUpper) := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨upper, hRead, hRow⟩ := copy.upper_lift_read hLast hUnmarked hUpper
  have hB : F.height sourceUpper = Row.B (F.height source) (F.height parent) :=
    (Frame.aboveHeight_of_upper hUpper).symm.trans ((build_normal_of_success p.reduced_build).above_row hParent)
  have hOwnRoot : (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row ≤
      F.height source := copy.read.source_lower
  refine ⟨upper, hRead, ?_⟩
  rw [hRow, hB, Row.B, Row.lift_bump hOwnRoot, Row.lift_bump hRoot]
  have hLift : Row.lift (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row
      (copy.data.marker_data copy.read.marker copy.read.marker_mem).targetCell.row (F.height source) =
        Row.lift root target (F.height source) := copy.read.output_row.symm.trans hLower
  rw [hLift]

/-- The raised occurrence constructs an actual source interval containing
both common-parent sources whose old upper rows coincide. The other source
need not be assumed raised, nor assigned a contour/root certificate. -/
theorem common_parent_interval_of_raised (hLast : 1 < last)
    {other parent sourceUpper otherUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hOtherParent : (Frame.ofMountain p.reduced).P other = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    (hOtherUpper : (Frame.ofMountain p.reduced).upper other = some otherUpper)
    (hSame : (Frame.ofMountain p.reduced).height sourceUpper =
      (Frame.ofMountain p.reduced).height otherUpper)
    (hMoved : p.root.column ≤ parent.1.val)
    (hRaised : (Frame.ofMountain p.reduced).height source < copy.read.outputCell.row) :
    ∃ rootIndex, ∃ a : ActualRootInterval p start copy.before references rootIndex
        (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row,
      Frame.RootInterval (Frame.ofMountain p.reduced) a.root
        (Row.bump (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row a.degree) source ∧
      Frame.RootInterval (Frame.ofMountain p.reduced) a.root
        (Row.bump (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row a.degree) other := by
  let F := Frame.ofMountain p.reduced
  let md := copy.data.marker_data copy.read.marker copy.read.marker_mem
  have hNormal := build_normal_of_success p.reduced_build
  have hRaisedLift : F.height source < Row.lift md.current.row md.targetCell.row (F.height source) := by
    simpa only [copy.read.output_row, Frame.height, md, F] using hRaised
  rcases copy.state.marker_source_transport hLast copy.data copy.read.marker_mem rfl copy.read.marker_before with
    ⟨_, hFixed⟩ | ⟨index, a, _, hTargetRaised, hSourceInside | ⟨_, hFixed⟩⟩
  · exact False.elim ((ne_of_lt hRaisedLift) hFixed.symm)
  · have hRootRow : F.height a.root = md.current.row := a.root_row
    have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
    have hSourceInside' : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) source := by
      simpa only [hRootRow] using hSourceInside
    have hRootBarrier : ∀ upper, F.upper a.root = some upper →
        Row.bump (F.height a.root) a.degree ≤ F.height upper := by
      simpa only [hRootRow] using a.root_upper_barrier
    have hParentInside : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) parent := by
      rcases Frame.root_interval_parent_bump hNormal a.root_real (a.raised_degree hTargetRaised)
          hRootBarrier hParent hSourceInside' with hi | ⟨hb, _⟩
      · exact hi
      · have hCol := hb.1
        rw [hRootColumn] at hCol
        omega
    have hUpperCap : F.height sourceUpper ≤ Row.bump (F.height a.root) a.degree := by
      rw [(Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)]
      exact Row.B_le_cap_of_same_interval hSourceInside'.2.1 hSourceInside'.2.2
        hParentInside.2.1 hParentInside.2.2
    have hOtherBelow : F.height other < Row.bump (F.height a.root) a.degree := by
      have hB : F.height otherUpper = Row.B (F.height other) (F.height parent) :=
        (Frame.aboveHeight_of_upper hOtherUpper).symm.trans (hNormal.above_row hOtherParent)
      exact ((Row.lt_B _ _).trans_eq hB.symm).trans_le (hSame ▸ hUpperCap)
    obtain ⟨hCone, hLower⟩ := Frame.root_cone_child_of_parent hNormal hOtherParent
      hParentInside.1 hParentInside.2.1
    exact ⟨index, a, hSourceInside, by simpa only [hRootRow] using
      (show Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) other from
        ⟨hCone, hLower, hOtherBelow⟩)⟩
  · exact False.elim ((ne_of_lt hRaisedLift) hFixed.symm)

end EffectiveCopyOccurrence

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref} {result : Mountain}
  {u z : (Frame.ofMountain p.reduced).Node}
  (uCopy : EffectiveCopyOccurrence p block start references u result)
  (zCopy : EffectiveCopyOccurrence p block start references z result)

/-- Same old upper rows for common-parent nonmarkers give same actual
immediate copied upper rows. Every father-column case is included, including
the root column. Only source numerical parents appear in the hypotheses. -/
theorem common_parent_upper_rows (hLast : 1 < last)
    (hUUnmarked : u.2.val ∉ (p.marked[u.1.val]?.getD []).map Ref.index)
    (hZUnmarked : z.2.val ∉ (p.marked[z.1.val]?.getD []).map Ref.index)
    {parent uUpper zUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUUpper : (Frame.ofMountain p.reduced).upper u = some uUpper)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some zUpper)
    (hSame : (Frame.ofMountain p.reduced).height uUpper =
      (Frame.ofMountain p.reduced).height zUpper) :
    ∃ actualUUpper actualZUpper,
      Canonical.cellAt result ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok actualUUpper ∧
      Canonical.cellAt result ⟨zCopy.outputRef.column, zCopy.outputRef.index + 1⟩ = .ok actualZUpper ∧
      actualUUpper.row = actualZUpper.row := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hOfCommonLift (root target : Row) (hRootU : root ≤ F.height u) (hRootZ : root ≤ F.height z)
      (hLiftU : uCopy.read.outputCell.row = Row.lift root target (F.height u))
      (hLiftZ : zCopy.read.outputCell.row = Row.lift root target (F.height z)) :
      ∃ actualUUpper actualZUpper,
        Canonical.cellAt result ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok actualUUpper ∧
        Canonical.cellAt result ⟨zCopy.outputRef.column, zCopy.outputRef.index + 1⟩ = .ok actualZUpper ∧
        actualUUpper.row = actualZUpper.row := by
    obtain ⟨actualU, hURead, hURow⟩ :=
      uCopy.upper_read_of_lower_lift hLast hUUnmarked hUP hUUpper hRootU hLiftU
    obtain ⟨actualZ, hZRead, hZRow⟩ :=
      zCopy.upper_read_of_lower_lift hLast hZUnmarked hZP hZUpper hRootZ hLiftZ
    exact ⟨actualU, actualZ, hURead, hZRead, by rw [hURow, hZRow, hSame]⟩
  by_cases hFixed : parent.1.val < p.root.column
  · obtain ⟨actualU, hURead, hURow⟩ := uCopy.upper_lift_read hLast hUUnmarked hUUpper
    obtain ⟨actualZ, hZRead, hZRow⟩ := zCopy.upper_lift_read hLast hZUnmarked hZUpper
    have hUFixed := uCopy.state.fixed_parent_marker_lift_upper hLast uCopy.data
      uCopy.read.marker_mem hUP rfl uCopy.read.marker_before hUUpper hFixed
    have hZFixed := zCopy.state.fixed_parent_marker_lift_upper hLast zCopy.data
      zCopy.read.marker_mem hZP rfl zCopy.read.marker_before hZUpper hFixed
    exact ⟨actualU, actualZ, hURead, hZRead,
      (hURow.trans hUFixed).trans (hSame.trans (hZRow.trans hZFixed).symm)⟩
  · have hMoved : p.root.column ≤ parent.1.val := Nat.le_of_not_gt hFixed
    have hURight : p.root.column < u.1.val := hMoved.trans_lt (Frame.P_column_lt hNormal.toOrdered hUP)
    have hZRight : p.root.column < z.1.val := hMoved.trans_lt (Frame.P_column_lt hNormal.toOrdered hZP)
    by_cases hUFixed : uCopy.read.outputCell.row = F.height u
    · by_cases hZFixed : zCopy.read.outputCell.row = F.height z
      · apply hOfCommonLift 0 0 (Row.zero_le _) (Row.zero_le _)
        · rw [Row.lift_identity (Row.zero_le _)]; exact hUFixed
        · rw [Row.lift_identity (Row.zero_le _)]; exact hZFixed
      · have hZRaised : F.height z < zCopy.read.outputCell.row :=
          lt_of_le_of_ne zCopy.read.source_row_le_output (Ne.symm hZFixed)
        obtain ⟨index, a, hZInside, hUInside⟩ := zCopy.common_parent_interval_of_raised hLast
          hZP hUP hZUpper hUUpper hSame.symm hMoved hZRaised
        apply hOfCommonLift _ a.target.row
        · simpa only [a.root_row] using hUInside.2.1
        · simpa only [a.root_row] using hZInside.2.1
        · exact uCopy.interval_row a hUInside hURight
        · exact zCopy.interval_row a hZInside hZRight
    · have hURaised : F.height u < uCopy.read.outputCell.row :=
        lt_of_le_of_ne uCopy.read.source_row_le_output (Ne.symm hUFixed)
      obtain ⟨index, a, hUInside, hZInside⟩ := uCopy.common_parent_interval_of_raised hLast
        hUP hZP hUUpper hZUpper hSame hMoved hURaised
      apply hOfCommonLift _ a.target.row
      · simpa only [a.root_row] using hUInside.2.1
      · simpa only [a.root_row] using hZInside.2.1
      · exact uCopy.interval_row a hUInside hURight
      · exact zCopy.interval_row a hZInside hZRight

/-- The source last-blocker overlap gives the shared source upper row,
so the caller does not need a same-row premise at either source or target. -/
theorem common_parent_upper_rows_of_overlap (hLast : 1 < last)
    (hUUnmarked : u.2.val ∉ (p.marked[u.1.val]?.getD []).map Ref.index)
    (hZUnmarked : z.2.val ∉ (p.marked[z.1.val]?.getD []).map Ref.index)
    {parent zUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some zUpper)
    (hOrder : (Frame.ofMountain p.reduced).height z ≤ (Frame.ofMountain p.reduced).height u)
    (hBefore : (Frame.ofMountain p.reduced).height u < (Frame.ofMountain p.reduced).height zUpper) :
    ∃ actualUUpper actualZUpper,
      Canonical.cellAt result ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok actualUUpper ∧
      Canonical.cellAt result ⟨zCopy.outputRef.column, zCopy.outputRef.index + 1⟩ = .ok actualZUpper ∧
      actualUUpper.row = actualZUpper.row := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨uUpper, hUUpper⟩ := hNormal.upper_of_parent hUP
  exact uCopy.common_parent_upper_rows zCopy hLast hUUnmarked hZUnmarked hUP hZP hUUpper hZUpper
    (hNormal.common_parent_upper_rows hUP hZP hUUpper hZUpper hOrder hBefore)

/-- The actual copied rows select one actual finite global event, with
both effective lowers as its preceding frontiers and both immediate uppers
as its following frontiers. Validity is geometric only; no target numerical
parent recognition, depth word, or value comparison is an input. -/
theorem common_parent_upper_event (hValid : MountainValid result) (hLast : 1 < last)
    (hUUnmarked : u.2.val ∉ (p.marked[u.1.val]?.getD []).map Ref.index)
    (hZUnmarked : z.2.val ∉ (p.marked[z.1.val]?.getD []).map Ref.index)
    {parent zUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some zUpper)
    (hOrder : (Frame.ofMountain p.reduced).height z ≤ (Frame.ofMountain p.reduced).height u)
    (hBefore : (Frame.ofMountain p.reduced).height u < (Frame.ofMountain p.reduced).height zUpper) :
    let F := Frame.ofMountain result
    ∃ (actualU actualZ upperU upperZ : F.Node) (event : Nat),
      Frame.ref actualU = uCopy.outputRef ∧ Frame.ref actualZ = zCopy.outputRef ∧
      F.cell actualU = uCopy.read.outputCell ∧ F.cell actualZ = zCopy.read.outputCell ∧
      F.upper actualU = some upperU ∧ F.upper actualZ = some upperZ ∧
      F.height upperU = F.height upperZ ∧ event < F.lastEvent ∧
      F.eventCut (event + 1) = F.height upperU ∧
      Frame.eventFrontier hValid.toOrdered event actualU.1 = actualU ∧
      Frame.eventFrontier hValid.toOrdered event actualZ.1 = actualZ ∧
      Frame.eventFrontier hValid.toOrdered (event + 1) actualU.1 = upperU ∧
      Frame.eventFrontier hValid.toOrdered (event + 1) actualZ.1 = upperZ := by
  let F := Frame.ofMountain result
  obtain ⟨actualUCell, actualZCell, hURead, hZRead, hSame⟩ :=
    uCopy.common_parent_upper_rows_of_overlap zCopy hLast hUUnmarked hZUnmarked hUP hZP
      hZUpper hOrder hBefore
  obtain ⟨actualU, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt uCopy.output_read
  obtain ⟨actualZ, hZRef, hZCell⟩ := Canonical.frame_node_of_cellAt zCopy.output_read
  obtain ⟨upperU, hUpperURef, hUpperUCell⟩ := Canonical.frame_node_of_cellAt hURead
  obtain ⟨upperZ, hUpperZRef, hUpperZCell⟩ := Canonical.frame_node_of_cellAt hZRead
  have hUpperU : F.upper actualU = some upperU := frame_upper_of_refs hURef hUpperURef
  have hUpperZ : F.upper actualZ = some upperZ := frame_upper_of_refs hZRef hUpperZRef
  have hRows : F.height upperU = F.height upperZ := by
    change (F.cell upperU).row = (F.cell upperZ).row
    rw [hUpperUCell, hUpperZCell]
    exact hSame
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hUP).1.trans (Frame.P_value hNormal.toOrdered hUP).2)
  have hActualReal : Frame.Real actualU := by
    have hi : actualU.2.val = uCopy.read.outputIndex := congrArg Ref.index hURef
    change 0 < actualU.2.val
    rw [hi]
    exact uCopy.read.output_real hSourceReal
  obtain ⟨event, hEvent, hCut, hUFront, hUNext⟩ :=
    Frame.upper_at_positive_event hValid.toOrdered hActualReal hUpperU
  obtain ⟨hZFront, hZNext⟩ := Frame.eventFrontier_pair_of_upper_cut hValid.toOrdered
    hEvent hUpperZ (hCut.trans hRows)
  exact ⟨actualU, actualZ, upperU, upperZ, event, hURef, hZRef, hUCell, hZCell,
    hUpperU, hUpperZ, hRows, hEvent, hCut, hUFront, hZFront, hUNext, hZNext⟩

end EffectiveCopyOccurrence

/-- Construct both occurrences from the actual current copy run and its
earlier-column history, then derive immediate-upper synchrony. The earlier
source is explicitly in the copied bad part; a preserved good-part source
has an original occurrence instead and is not silently treated as copied. -/
theorem DynamicBlockState.actual_common_parent_upper
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {u z parent zUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUColumn : u.1.val = next) (hZRight : p.root.column < z.1.val) (hZEarlier : z.1.val < next)
    (hUUnmarked : u.2.val ∉ (p.marked[u.1.val]?.getD []).map Ref.index)
    (hZUnmarked : z.2.val ∉ (p.marked[z.1.val]?.getD []).map Ref.index)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some zUpper)
    (hOrder : (Frame.ofMountain p.reduced).height z ≤ (Frame.ofMountain p.reduced).height u)
    (hBefore : (Frame.ofMountain p.reduced).height u < (Frame.ofMountain p.reduced).height zUpper)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (uCopy : EffectiveCopyOccurrence p block start references u (ambient.push column))
      (zCopy : EffectiveCopyOccurrence p block start references z (ambient.push column))
      (actualUUpper actualZUpper : Cell),
      uCopy.before = ambient ∧ uCopy.column = column ∧
      Canonical.cellAt (ambient.push column) ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok actualUUpper ∧
      Canonical.cellAt (ambient.push column) ⟨zCopy.outputRef.column, zCopy.outputRef.index + 1⟩ = .ok actualZUpper ∧
      actualUUpper.row = actualZUpper.row := by
  subst next
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast u.1.isLt
  have hSource : p.reduced[u.1.val]? = some d.sources :=
    (s.base_ambient u.1.val u.1.isLt).symm.trans d.source_column
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun
    (d.frame_source_read hSource (rfl : u.1.val = u.1.val))
  let uCopy : EffectiveCopyOccurrence p block start references u (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  obtain ⟨oldZCopy⟩ := s.prior_effective_occurrence history hLast hZRight hZEarlier
  let zCopy := oldZCopy.extend (PreservesColumns.push ambient column)
  obtain ⟨actualU, actualZ, hURead, hZRead, hSame⟩ :=
    uCopy.common_parent_upper_rows_of_overlap zCopy hLast hUUnmarked hZUnmarked hUP hZP
      hZUpper hOrder hBefore
  exact ⟨uCopy, zCopy, actualU, actualZ, rfl, rfl, hURead, hZRead, hSame⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.upper_lift_read
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.upper_read_of_lower_lift
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.common_parent_interval_of_raised
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.common_parent_upper_rows
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.common_parent_upper_rows_of_overlap
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.common_parent_upper_event
#print axioms OmegaY.Expansion.DynamicBlockState.actual_common_parent_upper
