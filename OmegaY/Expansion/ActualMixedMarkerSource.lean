/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMixedMarkerSource.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSharedContourCutAll
import OmegaY.Geometry.PathBranch

/-!
# Source geometry for a mixed marker pair with one candidate

At a shared source row, a marked node and an unmarked node with the same
geometric candidate search one actual numerical record chain. Any numerical
parent of the unmarked node lies strictly left of the root column. The
actual root-prefix endpoint has a source path to that parent, which gives
the source upper-row barrier. Separately, an unmarked occurrence at any
actual marker row is stationary by the real reference partition.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem ActualRootInterval.mixed_candidate_parent_exit
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index : Nat} {row : Row}
    (a : ActualRootInterval p start ambient references index row)
    {marked other candidate parent : (Frame.ofMountain p.reduced).Node}
    (hMarked : BucketMem p.marked marked.1.val (Frame.ref marked))
    (hUnmarked : ¬ BucketMem p.marked other.1.val (Frame.ref other))
    (hMarkedRight : p.root.column < marked.1.val) (hOtherRight : p.root.column < other.1.val)
    (hMarkedRow : (Frame.ofMountain p.reduced).height marked = row)
    (hOtherRow : (Frame.ofMountain p.reduced).height other = row)
    (hMarkedQ : (Frame.ofMountain p.reduced).Q marked = some candidate)
    (hOtherQ : (Frame.ofMountain p.reduced).Q other = some candidate)
    (hParent : (Frame.ofMountain p.reduced).P other = some parent) :
    ParentPath (Frame.ofMountain p.reduced) a.root parent ∧ parent.1.val < p.root.column := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  obtain ⟨low, hLowReal, hLowColumn, hLowRow, hPath⟩ := a.rootCone_of_marker hMarked hMarkedRow
  have hLowEq : low = marked := node_eq_of_column_height hNormal.toOrdered hLowColumn
    (hLowRow.trans (a.root_row.trans hMarkedRow.symm))
  subst low
  have hMarkedReal := hLowReal
  have hCandidateReal := Q_real hNormal.toOrdered hMarkedReal hMarkedQ
  have hCandidatePositive := hNormal.real_positive candidate hCandidateReal
  have hToRoot : ParentPath F candidate a.root := by
    cases hPath with
    | refl => omega
    | @cons _ first _ hFirst tail =>
      obtain ⟨q, hQ, hit⟩ := (P_iff hNormal.toOrdered).mp hFirst
      have he : q = candidate := Option.some.inj (hQ.symm.trans hMarkedQ)
      subst q
      exact (hit.parentPath hNormal.toOrdered hCandidatePositive).trans tail
  obtain ⟨q, hQ, hit⟩ := (P_iff hNormal.toOrdered).mp hParent
  have he : q = candidate := Option.some.inj (hQ.symm.trans hOtherQ)
  subst q
  have hToParent := hit.parentPath hNormal.toOrdered hCandidatePositive
  have hOtherReal := real_of_value_pos hNormal.toOrdered
    ((P_value hNormal.toOrdered hParent).1.trans (P_value hNormal.toOrdered hParent).2)
  have hNotToRoot : ¬ ParentPath F parent a.root := by
    intro tail
    obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
    have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
      simpa only [hBadRef] using p.markers_built
    have hBadColumn : badRoot.1.val = p.root.column := congrArg Ref.column hBadRef
    have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
    have hRootIndex : a.root.2.val = index := congrArg Ref.index a.root_ref
    apply hUnmarked
    exact (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hOtherReal).mpr
      ⟨by rw [hBadColumn]; exact hOtherRight, a.root, a.root_real,
        Fin.ext (hRootColumn.trans hBadColumn.symm),
        by rw [hRootIndex, hBadIndex]; exact a.root_prefix,
        .cons hParent tail, hOtherRow.trans a.root_row.symm⟩
  have hFixed : parent.1.val < p.root.column := by
    by_contra hn
    apply hNotToRoot
    exact hToParent.suffix_of_column_le hNormal.toOrdered hToRoot
      (by rw [hRootColumn]; omega)
  exact ⟨(hToRoot.comparable hToParent).resolve_right hNotToRoot, hFixed⟩

/-- The root's actual source upper is no higher than the unmarked upper.
The source parent path, not the copied output's numerical P, supplies this
comparison. A terminal root makes the assumed nonterminal other impossible. -/
theorem ActualRootInterval.cap_le_mixed_upper
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index : Nat} {row : Row}
    (a : ActualRootInterval p start ambient references index row)
    {marked other candidate parent upper : (Frame.ofMountain p.reduced).Node}
    (hMarked : BucketMem p.marked marked.1.val (Frame.ref marked))
    (hUnmarked : ¬ BucketMem p.marked other.1.val (Frame.ref other))
    (hMarkedRight : p.root.column < marked.1.val) (hOtherRight : p.root.column < other.1.val)
    (hMarkedRow : (Frame.ofMountain p.reduced).height marked = row)
    (hOtherRow : (Frame.ofMountain p.reduced).height other = row)
    (hMarkedQ : (Frame.ofMountain p.reduced).Q marked = some candidate)
    (hOtherQ : (Frame.ofMountain p.reduced).Q other = some candidate)
    (hParent : (Frame.ofMountain p.reduced).P other = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper other = some upper) :
    Row.bump row a.degree ≤ (Frame.ofMountain p.reduced).height upper := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨path, hFixed⟩ := a.mixed_candidate_parent_exit hMarked hUnmarked hMarkedRight hOtherRight
    hMarkedRow hOtherRow hMarkedQ hOtherQ hParent
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  cases path with
  | refl => omega
  | @cons _ first _ hFirst tail =>
    obtain ⟨rootUpper, hRootUpper⟩ := hNormal.upper_of_parent hFirst
    have hRootB : F.height rootUpper = Row.B row (F.height first) := by
      rw [(aboveHeight_of_upper hRootUpper).symm.trans (hNormal.above_row hFirst), a.root_row]
    have hOtherB : F.height upper = Row.B row (F.height parent) := by
      rw [(aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent), hOtherRow]
    have hFirstBelow : F.height first ≤ row := a.root_row ▸ P_height_le hNormal.toOrdered hFirst
    have hParentBelow : F.height parent ≤ F.height first := tail.height_le hNormal.toOrdered
    have hB : Row.B row (F.height first) ≤ Row.B row (F.height parent) := by
      rw [Row.B_max hFirstBelow hParentBelow]
      exact le_max_left _ _
    exact (a.root_upper_barrier rootUpper hRootUpper).trans (by
      change F.height rootUpper ≤ F.height upper
      rw [hRootB, hOtherB]
      exact hB)

/-- A higher actual source root-prefix row bounds this reference cap,
even when no marker at that higher row is present in the copied column. -/
theorem ActualRootInterval.cap_le_of_higher_prefix_height
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index : Nat} {row : Row}
    (a : ActualRootInterval p start ambient references index row)
    {nodes : Column} {higherIndex : Nat} {higher : Cell}
    (hColumn : p.initial[p.root.column]? = some nodes)
    (hRead : nodes[higherIndex]? = some higher) (hPrefix : higherIndex ≤ p.root.index)
    (hHigher : row < higher.row) : Row.bump row a.degree ≤ higher.row := by
  have hRootRead : Canonical.cellAt p.initial ⟨p.root.column, index⟩ =
      .ok ((Frame.ofMountain p.reduced).cell a.root) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, index⟩)
      p.initial_build p.reduced_build p.root_before_last).trans
      (by simpa only [a.root_ref] using cellAt_of_frame_node p.reduced a.root)
  obtain ⟨rootNodes, hRootColumn, hRootAt⟩ := cellAt_ok_iff.mp hRootRead
  have he : rootNodes = nodes := Option.some.inj (hRootColumn.symm.trans hColumn)
  subst rootNodes
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hValid : ColumnValid p.initial p.root.column nodes := hNodes ▸ p.initial_valid _ hc
  have hIndex : index < higherIndex := by
    by_contra hn
    rcases eq_or_lt_of_le (Nat.le_of_not_gt hn) with he | hl
    · have hCell := Option.some.inj (hRead.symm.trans (by simpa only [he] using hRootAt))
      have hRow : higher.row = row := (congrArg Cell.row hCell).trans a.root_row
      exact (ne_of_lt hHigher) hRow.symm
    · have hRow := hValid.rows_strict _ _ _ _ hRead hRootAt hl
      change higher.row < (Frame.ofMountain p.reduced).height a.root at hRow
      rw [a.root_row] at hRow
      exact (not_lt_of_ge hHigher.le) hRow
  exact a.higher_prefix_barrier nodes higherIndex higher hColumn hIndex hPrefix hRead

/-- Missing a marker in this column cannot make a source root-prefix row
move: its previous controlling root has its cap below that very row. -/
theorem EffectiveCopyOccurrence.stationary_at_marker_row
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source marked : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    (hMarked : BucketMem p.marked marked.1.val (Frame.ref marked))
    (hRow : (Frame.ofMountain p.reduced).height source = (Frame.ofMountain p.reduced).height marked) :
    copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source := by
  let F := Frame.ofMountain p.reduced
  let md := copy.data.marker_data copy.read.marker copy.read.marker_mem
  have hAfter : copy.read.marker.index < source.2.val := by
    apply lt_of_le_of_ne copy.read.marker_before
    intro he
    exact hUnmarked (he ▸ List.mem_map.mpr ⟨copy.read.marker, copy.read.marker_mem, rfl⟩)
  have hAbove : md.current.row < F.height source :=
    copy.data.source_valid.rows_strict _ _ _ _ md.current_at copy.read.source_at hAfter
  obtain ⟨nodes, higherIndex, higher, hColumn, hRead, hPrefix, hMarkerRow⟩ :=
    p.marker_root_prefix_read hMarked (Canonical.cellAt_of_frame_node p.reduced marked)
  have hHigher : md.current.row < higher.row := by
    change higher.row = F.height marked at hMarkerRow
    rw [hMarkerRow, ← hRow]
    exact hAbove
  rcases copy.state.marker_source_transport hLast copy.data copy.read.marker_mem rfl copy.read.marker_before with
    ⟨_, hFixed⟩ | ⟨index, a, hTarget, _, hInside | ⟨_, hFixed⟩⟩
  · exact copy.read.output_row.trans hFixed
  · have hCap := a.cap_le_of_higher_prefix_height hColumn hRead hPrefix hHigher
    have hCapSource : Row.bump md.current.row a.degree ≤ F.height source := by
      have hHigherRow : higher.row = F.height marked := hMarkerRow
      change Row.bump md.current.row a.degree ≤ higher.row at hCap
      rw [hHigherRow, ← hRow] at hCap
      exact hCap
    exact False.elim ((not_lt_of_ge hCapSource) hInside.2.2)
  · exact copy.read.output_row.trans hFixed

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualRootInterval.mixed_candidate_parent_exit
#print axioms OmegaY.Expansion.ActualRootInterval.cap_le_mixed_upper
#print axioms OmegaY.Expansion.ActualRootInterval.cap_le_of_higher_prefix_height
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stationary_at_marker_row
