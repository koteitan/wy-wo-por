/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualContourEventOrder.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAllSourceDepth
import OmegaY.Expansion.ActualEffectiveOrder

/-!
# Ordered actual contour cuts in one source column

Independent effective occurrences use the same actual reference map.
When the source frontier stays at one node, their complete contour maps
agree. When the frontier changes, strict effective-row order and the
earlier output frontier's maximality force strict order of the two cuts.
Thus the real floor events are monotone, even across controlling markers.

This is within one source column. It does not align two distinct columns'
event samplings or establish a numerical comparison theorem.
-/

namespace OmegaY.Geometry.Frame

theorem frontierAt_lt_of_later_height {F : Frame} (hF : F.Ordered)
    {cut : Row} (hCut : (1 : Row) ≤ cut) {node later : F.Node}
    (hFront : frontierAt hF cut hCut node.1 = node)
    (hColumn : later.1 = node.1) (hHeight : F.height node < F.height later) :
    cut < F.height later := by
  rcases node with ⟨column, index⟩
  rcases later with ⟨laterColumn, laterIndex⟩
  dsimp only at hColumn
  subst laterColumn
  by_contra hn
  have hMax := (frontierAt_spec hF hCut column).2.2.2.1 laterIndex (le_of_not_gt hn)
  have hIndex := congrArg (fun n : F.Node => n.2.val) hFront
  have hBelow : laterIndex.val ≤ index.val := by
    change laterIndex.val ≤ (frontierAt hF cut hCut column).2.val at hMax
    exact hMax.trans_eq hIndex
  exact not_lt_of_ge ((hF.rows_strict column).monotone hBelow) hHeight

theorem event_index_le_of_cut_le {F : Frame} {first second : Nat}
    (hFirst : first ≤ F.lastEvent) (hSecond : second ≤ F.lastEvent)
    (hCuts : F.eventCut first ≤ F.eventCut second) : first ≤ second := by
  have hFirstBound := hFirst.trans_lt F.lastEvent_lt
  have hSecondBound := hSecond.trans_lt F.lastEvent_lt
  rw [F.eventCut_of_lt hFirstBound, F.eventCut_of_lt hSecondBound] at hCuts
  by_contra hn
  exact not_le_of_gt (F.eventCuts_sorted.getElem_lt_getElem_of_lt (Nat.lt_of_not_ge hn)) hCuts

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}

/-- Independent executed certificates for the same source node have the
same whole contour-cut function, not merely the same effective row. -/
theorem contourCut_unique {source : (Frame.ofMountain p.reduced).Node}
    (left right : EffectiveCopyOccurrence p block start references source result) (cut : Row) :
    left.contourCut cut = right.contourCut cut := by
  have hSources : left.data.sources = right.data.sources := by
    have hLeft : p.reduced[source.1.val]? = some left.data.sources :=
      (left.state.base_ambient source.1.val source.1.isLt).symm.trans left.data.source_column
    have hRight : p.reduced[source.1.val]? = some right.data.sources :=
      (right.state.base_ambient source.1.val source.1.isLt).symm.trans right.data.source_column
    exact Option.some.inj (hLeft.symm.trans hRight)
  let lm := left.data.marker_data left.read.marker left.read.marker_mem
  let rm := right.data.marker_data right.read.marker right.read.marker_mem
  have hCurrent : lm.current = rm.current := Option.some.inj
    (lm.current_at.symm.trans (by rw [hSources, left.marker_unique right]; exact rm.current_at))
  have hQueryL : referenceAt start references lm.current.row = .ok lm.targetCell.row :=
    (left.state.referenceAt_preserved lm.current.row).symm.trans lm.reference
  have hQueryR : referenceAt start references rm.current.row = .ok rm.targetCell.row :=
    (right.state.referenceAt_preserved rm.current.row).symm.trans rm.reference
  have hTarget : lm.targetCell.row = rm.targetCell.row := Except.ok.inj
    (hQueryL.symm.trans (by rw [hCurrent]; exact hQueryR))
  change Row.lift lm.current.row lm.targetCell.row cut = Row.lift rm.current.row rm.targetCell.row cut
  rw [hCurrent, hTarget]

/-- Actual effective order extends from reads sharing one data record to
arbitrary independently constructed occurrences in the same source column.
A common record is recovered from genuine execution, then uniqueness
identifies its later occurrence with the one supplied. -/
theorem same_column_output_row_lt
    {source later : (Frame.ofMountain p.reduced).Node}
    (left : EffectiveCopyOccurrence p block start references source result)
    (right : EffectiveCopyOccurrence p block start references later result)
    (hLast : 1 < last) (hColumn : source.1 = later.1) (hIndex : source.2.val < later.2.val) :
    left.read.outputCell.row < right.read.outputCell.row := by
  rcases source with ⟨column, index⟩
  rcases later with ⟨laterColumn, laterIndex⟩
  dsimp only at hColumn
  subst laterColumn
  obtain ⟨hNoPremature, hPP, hPL⟩ := left.state.column_data_parent_inputs hLast column.isLt left.data
  have hSource : p.reduced[column.val]? = some left.data.sources :=
    (left.state.base_ambient column.val column.isLt).symm.trans left.data.source_column
  have hLater : left.data.sources[laterIndex.val]? =
      some ((Frame.ofMountain p.reduced).cell ⟨column, laterIndex⟩) :=
    left.data.frame_source_read (u := ⟨column, laterIndex⟩) hSource rfl
  obtain ⟨read⟩ := left.data.effective_copy_read hPP hPL hNoPremature left.read.copy_run hLater
  let other : EffectiveCopyOccurrence p block start references ⟨column, laterIndex⟩ result :=
    ⟨left.before, left.column, left.state, left.data, read, left.preserved⟩
  exact (left.read.output_row_lt read hIndex).trans_eq (other.effective_row_unique right)

/-- The same actual source column has ordered lifted frontier cuts.
The controlling markers may differ, and markers themselves are included. -/
theorem contourCut_le_of_frontiers
    {source later : (Frame.ofMountain p.reduced).Node}
    (left : EffectiveCopyOccurrence p block start references source result)
    (right : EffectiveCopyOccurrence p block start references later result)
    (hLast : 1 < last) (hValid : MountainValid result)
    (hColumn : source.1 = later.1)
    {cut laterCut : Row} (hCut : (1 : Row) ≤ cut) (hLaterCut : (1 : Row) ≤ laterCut)
    (hOrder : cut ≤ laterCut)
    (hFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut source.1 = source)
    (hLaterFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      laterCut hLaterCut later.1 = later) :
    left.contourCut cut ≤ right.contourCut laterCut := by
  rcases source with ⟨column, index⟩
  rcases later with ⟨laterColumn, laterIndex⟩
  dsimp only at hColumn
  subst laterColumn
  have hSourceBelow : (Frame.ofMountain p.reduced).height ⟨column, index⟩ ≤ cut :=
    hFront ▸ (frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered hCut column).2.2.1
  have hMaximum := (frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered
    hLaterCut column).2.2.2.1 index (hSourceBelow.trans hOrder)
  have hFrontIndex := congrArg (fun n : (Frame.ofMountain p.reduced).Node => n.2.val) hLaterFront
  have hIndices : index.val ≤ laterIndex.val := by
    change index.val ≤ (frontierAt _ laterCut hLaterCut column).2.val at hMaximum
    exact hMaximum.trans_eq hFrontIndex
  rcases eq_or_lt_of_le hIndices with hSame | hStrict
  · have hIndexEq : index = laterIndex := Fin.ext hSame
    subst laterIndex
    rw [← left.contourCut_unique right laterCut]
    exact Row.lift_monotone (left.read.source_lower.trans hSourceBelow) hOrder
  · have hOutputRows := left.same_column_output_row_lt right hLast rfl hStrict
    obtain ⟨hLift, node, hRef, hCell, hAt⟩ := left.frontierAt_own_lift_all hLast hValid hCut hFront
    obtain ⟨hLaterLift, laterNode, hLaterRef, hLaterCell, hLaterAt⟩ :=
      right.frontierAt_own_lift_all hLast hValid hLaterCut hLaterFront
    have hOutputColumn : laterNode.1 = node.1 := Fin.ext
      ((congrArg Ref.column hLaterRef).trans right.source_column |>.trans
        (left.source_column.symm.trans (congrArg Ref.column hRef).symm))
    have hOutputHeight : (Frame.ofMountain result).height node < (Frame.ofMountain result).height laterNode := by
      simpa only [Frame.height, hCell, hLaterCell] using hOutputRows
    have hBetween := frontierAt_lt_of_later_height hValid.toOrdered hLift hAt hOutputColumn hOutputHeight
    have hLaterBelow : (Frame.ofMountain result).height laterNode ≤ right.contourCut laterCut :=
      hLaterAt ▸ (frontierAt_spec hValid.toOrdered hLaterLift laterNode.1).2.2.1
    exact (hBetween.trans_le hLaterBelow).le

end EffectiveCopyOccurrence

/-- Ordered original events induce ordered actual floor events for one
source column. Floor maximality and the finite event list's strict order
turn the proven contour-cut inequality into an index inequality. -/
theorem LowCopiedDepth.targetEvent_le_of_sourceEvent_le
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {source later : (Frame.ofMountain p.reduced).Node} {sourceEvent laterEvent : Nat}
    {leftCopy : EffectiveCopyOccurrence p block start references source ambient}
    {rightCopy : EffectiveCopyOccurrence p block start references later ambient}
    (left : LowCopiedDepth s source sourceEvent leftCopy)
    (right : LowCopiedDepth s later laterEvent rightCopy)
    (hLast : 1 < last) (hColumn : source.1 = later.1) (hOrder : sourceEvent ≤ laterEvent)
    (hFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent source.1 = source)
    (hLaterFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered laterEvent later.1 = later) :
    leftCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) ≤
        rightCopy.contourCut ((Frame.ofMountain p.reduced).eventCut laterEvent) ∧
      left.targetEvent ≤ right.targetEvent := by
  have hCuts := leftCopy.contourCut_le_of_frontiers rightCopy hLast s.ambient_valid hColumn
    ((Frame.ofMountain p.reduced).eventCut_one_le sourceEvent)
    ((Frame.ofMountain p.reduced).eventCut_one_le laterEvent)
    ((Frame.ofMountain p.reduced).eventCut_monotone hOrder) hFront hLaterFront
  have hFloorCuts : (Frame.ofMountain ambient).eventCut left.targetEvent ≤
      (Frame.ofMountain ambient).eventCut right.targetEvent :=
    right.target_event_maximal _ ((Frame.ofMountain ambient).eventCut_mem left.targetEvent)
      (left.target_event_below.trans hCuts)
  exact ⟨hCuts, event_index_le_of_cut_le left.target_event_end right.target_event_end hFloorCuts⟩

/-- Real history constructs both source-frontier occurrences, both depth
packets and their ordered floor events. No target occurrence, controlling
marker, copied cut, frontier or order certificate is an input. -/
theorem DynamicBlockState.actual_ordered_source_event_depths
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (column : Fin (Frame.ofMountain p.reduced).width)
    (hRight : p.root.column < column.val) (hBefore : column.val < next)
    {sourceEvent laterEvent : Nat} (hOrder : sourceEvent ≤ laterEvent)
    (hEnd : laterEvent ≤ (Frame.ofMountain p.reduced).lastEvent) :
    let source := eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent column
    let later := eventFrontier (build_normal_of_success p.reduced_build).toOrdered laterEvent column
    ∃ (leftCopy : EffectiveCopyOccurrence p block start references source ambient)
      (rightCopy : EffectiveCopyOccurrence p block start references later ambient)
      (left : LowCopiedDepth s source sourceEvent leftCopy)
      (right : LowCopiedDepth s later laterEvent rightCopy),
      leftCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) ≤
          rightCopy.contourCut ((Frame.ofMountain p.reduced).eventCut laterEvent) ∧
        left.targetEvent ≤ right.targetEvent := by
  dsimp only
  obtain ⟨leftCopy, ⟨left⟩⟩ := s.actual_all_source_copied_depth_exists history hLast hStartRun
    (source := eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent column)
    hRight hBefore (hOrder.trans hEnd) rfl
  obtain ⟨rightCopy, ⟨right⟩⟩ := s.actual_all_source_copied_depth_exists history hLast hStartRun
    (source := eventFrontier (build_normal_of_success p.reduced_build).toOrdered laterEvent column)
    hRight hBefore hEnd rfl
  exact ⟨leftCopy, rightCopy, left, right,
    left.targetEvent_le_of_sourceEvent_le right hLast rfl hOrder rfl rfl⟩

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.frontierAt_lt_of_later_height
#print axioms OmegaY.Geometry.Frame.event_index_le_of_cut_le
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.contourCut_unique
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.same_column_output_row_lt
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.contourCut_le_of_frontiers
#print axioms OmegaY.Expansion.LowCopiedDepth.targetEvent_le_of_sourceEvent_le
#print axioms OmegaY.Expansion.DynamicBlockState.actual_ordered_source_event_depths
