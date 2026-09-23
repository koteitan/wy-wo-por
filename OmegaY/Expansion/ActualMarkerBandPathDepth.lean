/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkerBandPathDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.MarkerBandParentColumn
import OmegaY.Expansion.ActualRootForkDepthComparison

/-!
# Equal path lengths throughout genuine marker bands

At a fixed source root row, every nonroot node on its numerical ancestor
path is an actual marker and queries the same block-start target. Thus the
raw event-parent column law applies at every target event inside the band.
The source and target paths have the same number of edges up to the root
column. The boundary depth is left explicit and cancels for two such paths.

This handles different numerical source parents in two marked bands. It
does not assert a lower bound on the boundary depth at arbitrary band cuts.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.marker_band_path_steps
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {child root : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child root)
    (hRootReal : Real root) (hRootColumn : root.1.val = p.root.column)
    (hRootIndex : root.2.val ≤ p.root.index)
    (hSameRow : (Frame.ofMountain p.reduced).height child = (Frame.ofMountain p.reduced).height root)
    (hBefore : child.1.val < next)
    {sourceEvent targetEvent : Nat}
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent child.1 = child)
    {target : Row}
    (hQuery : referenceAt start references ((Frame.ofMountain p.reduced).height root) = .ok target)
    (hLow : (Frame.ofMountain p.reduced).height root ≤ (Frame.ofMountain ambient).eventCut targetEvent)
    (hHigh : (Frame.ofMountain ambient).eventCut targetEvent < target) :
    ∃ length,
      Forests.ParentSteps (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) sourceEvent) child.1.val root.1.val length ∧
      Forests.ParentSteps (eventParentMap s.ambient_valid.toOrdered
        hTargetWidth (ambient.size - 1) targetEvent)
        (child.1.val + block * (p.reduced.size - 1 - p.root.column))
        (root.1.val + block * (p.reduced.size - 1 - p.root.column)) length := by
  have hNormal := build_normal_of_success p.reduced_build
  induction path with
  | refl root => exact ⟨0, .nil _, .nil _⟩
  | @cons child middle root hParent tail ih =>
    have hMiddleRow : (Frame.ofMountain p.reduced).height middle = (Frame.ofMountain p.reduced).height root :=
      le_antisymm ((P_height_le hNormal.toOrdered hParent).trans_eq hSameRow) (tail.height_le hNormal.toOrdered)
    have hMiddleBefore := (P_column_lt hNormal.toOrdered hParent).trans hBefore
    have hMiddleFront := hNormal.eventFrontier_parent sourceEvent child.1 (by rw [hSourceFront]; exact hParent)
    obtain ⟨length, hSourceSteps, hTargetSteps⟩ := ih hRootReal hRootColumn hRootIndex hMiddleRow
      hMiddleBefore hMiddleFront hQuery hLow
    have hChildRight : p.root.column < child.1.val := by
      have ht := tail.column_le hNormal.toOrdered
      have hp := P_column_lt hNormal.toOrdered hParent
      omega
    have hReal := real_of_value_pos hNormal.toOrdered
      ((P_value hNormal.toOrdered hParent).1.trans (P_value hNormal.toOrdered hParent).2)
    obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
    have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
      simpa only [hBadRef] using p.markers_built
    have hBadColumn : badRoot.1.val = p.root.column := congrArg Ref.column hBadRef
    have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
    have hMarked : BucketMem p.marked child.1.val (Frame.ref child) :=
      (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mpr
        ⟨by rw [hBadColumn]; exact hChildRight, root, hRootReal,
          Fin.ext (hRootColumn.trans hBadColumn.symm), by rw [hBadIndex]; exact hRootIndex,
          .cons hParent tail, hSameRow⟩
    obtain ⟨copy⟩ := s.prior_effective_occurrence history hLast hChildRight hBefore
    have hOwnQuery : referenceAt start references ((Frame.ofMountain p.reduced).height child) =
        .ok copy.read.outputCell.row :=
      (copy.state.referenceAt_preserved _).symm.trans (copy.read.marked_reference hMarked)
    have hTarget : copy.read.outputCell.row = target := Except.ok.inj
      (hOwnQuery.symm.trans (by rw [hSameRow]; exact hQuery))
    have hTargetEdge := copy.marker_band_event_parent_column hLast s.ambient_valid hTargetWidth hMarked hParent
      (by rw [hSameRow]; exact hLow) (hHigh.trans_eq hTarget.symm)
    rw [copy.source_column] at hTargetEdge
    have hChildBound : child.1.val ≤ p.reduced.size - 1 := by
      have hc : child.1.val < p.reduced.size := child.1.isLt
      omega
    have hSourceEdge : eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1)
        sourceEvent child.1.val = some middle.1.val := by
      rw [hNormal.eventParentMap_at hSourceWidth sourceEvent child.1 hChildBound, hSourceFront, hParent]
      rfl
    exact ⟨length + 1, .cons hSourceEdge hSourceSteps, .cons hTargetEdge hTargetSteps⟩

/-- The common boundary term is visible; this balance makes no claim
about whether that boundary term exceeds its source counterpart. -/
theorem DynamicBlockState.marker_band_path_depth_balance
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {child root : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child root)
    (hRootReal : Real root) (hRootColumn : root.1.val = p.root.column)
    (hRootIndex : root.2.val ≤ p.root.index)
    (hSameRow : (Frame.ofMountain p.reduced).height child = (Frame.ofMountain p.reduced).height root)
    (hBefore : child.1.val < next)
    {sourceEvent targetEvent : Nat}
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent child.1 = child)
    {target : Row}
    (hQuery : referenceAt start references ((Frame.ofMountain p.reduced).height root) = .ok target)
    (hLow : (Frame.ofMountain p.reduced).height root ≤ (Frame.ofMountain ambient).eventCut targetEvent)
    (hHigh : (Frame.ofMountain ambient).eventCut targetEvent < target) :
    let sourceMap := eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent
    let targetMap := eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent
    parentDepth targetMap (child.1.val + block * (p.reduced.size - 1 - p.root.column)) +
        parentDepth sourceMap root.1.val =
      parentDepth sourceMap child.1.val +
        parentDepth targetMap (root.1.val + block * (p.reduced.size - 1 - p.root.column)) := by
  obtain ⟨length, hs, ht⟩ := s.marker_band_path_steps history hLast hSourceWidth hTargetWidth path
    hRootReal hRootColumn hRootIndex hSameRow hBefore hSourceFront hQuery hLow hHigh
  have hSourceBound : p.reduced.size - 1 < p.reduced.size := by omega
  have hTargetBound : ambient.size - 1 < ambient.size := by omega
  have hSource := hs.depth (eventParentMap_leftward (build_normal_of_success p.reduced_build).toOrdered
    hSourceWidth hSourceBound sourceEvent)
  have hTarget := ht.depth (eventParentMap_leftward s.ambient_valid.toOrdered hTargetWidth hTargetBound targetEvent)
  change parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent) child.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent) root.1.val + length at hSource
  change parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth
      (ambient.size - 1) targetEvent) (child.1.val + block * (p.reduced.size - 1 - p.root.column)) =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth
      (ambient.size - 1) targetEvent) (root.1.val + block * (p.reduced.size - 1 - p.root.column)) + length at hTarget
  dsimp only at hSource hTarget ⊢
  omega

/-- Two current markers may have different source numerical parents.
Their exact relative depth is nevertheless retained throughout the entire
physical/effective band, including events supplied by unrelated columns. -/
theorem DynamicBlockState.marked_band_depth_comparison
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {left right : (Frame.ofMountain p.reduced).Node}
    (hLeftBefore : left.1.val < next) (hRightBefore : right.1.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references left ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references right ambient)
    (hLeftMarked : BucketMem p.marked left.1.val (Frame.ref left))
    (hRightMarked : BucketMem p.marked right.1.val (Frame.ref right))
    {sourceEvent targetEvent : Nat}
    (hSourceLeft : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left.1 = left)
    (hSourceRight : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right.1 = right)
    (hLow : (Frame.ofMountain p.reduced).eventCut sourceEvent ≤ (Frame.ofMountain ambient).eventCut targetEvent)
    (hHigh : (Frame.ofMountain ambient).eventCut targetEvent < leftCopy.read.outputCell.row) :
    let sourceMap := eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent
    let targetMap := eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent
    parentDepth targetMap leftCopy.outputRef.column + parentDepth sourceMap right.1.val =
      parentDepth sourceMap left.1.val + parentDepth targetMap rightCopy.outputRef.column ∧
    (parentDepth sourceMap left.1.val ≤ parentDepth sourceMap right.1.val ↔
      parentDepth targetMap leftCopy.outputRef.column ≤ parentDepth targetMap rightCopy.outputRef.column) ∧
    (parentDepth sourceMap left.1.val < parentDepth sourceMap right.1.val ↔
      parentDepth targetMap leftCopy.outputRef.column < parentDepth targetMap rightCopy.outputRef.column) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hLeftReal : Real left := hSourceLeft ▸ (eventFrontier_spec hNormal.toOrdered sourceEvent left.1).2.1
  have hRightReal : Real right := hSourceRight ▸ (eventFrontier_spec hNormal.toOrdered sourceEvent right.1).2.1
  have hLeftRow := leftCopy.marked_frontier_cut_eq hLeftMarked
    ((Frame.ofMountain p.reduced).eventCut_one_le sourceEvent) hSourceLeft
  have hRightRow := rightCopy.marked_frontier_cut_eq hRightMarked
    ((Frame.ofMountain p.reduced).eventCut_one_le sourceEvent) hSourceRight
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  have hBadColumn : badRoot.1.val = p.root.column := congrArg Ref.column hBadRef
  have hBadIndex : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
  obtain ⟨_, root, hRootReal, hRootColumn, hRootIndex, leftPath, hLeftRootRow⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hLeftReal).mp hLeftMarked
  obtain ⟨_, otherRoot, _, hOtherColumn, _, rightPath, hRightRootRow⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hRightReal).mp hRightMarked
  have hRootSame : otherRoot = root := node_eq_of_column_height hNormal.toOrdered
    (hOtherColumn.trans hRootColumn.symm)
    (hRightRootRow.symm.trans (hRightRow.symm.trans (hLeftRow.trans hLeftRootRow)))
  subst otherRoot
  have hColumn : root.1.val = p.root.column := (congrArg Fin.val hRootColumn).trans hBadColumn
  have hIndex : root.2.val ≤ p.root.index := hBadIndex ▸ hRootIndex
  have hQuery : referenceAt start references ((Frame.ofMountain p.reduced).height root) =
      .ok leftCopy.read.outputCell.row := by
    rw [← hLeftRootRow]
    exact (leftCopy.state.referenceAt_preserved _).symm.trans (leftCopy.read.marked_reference hLeftMarked)
  have hRootLow : (Frame.ofMountain p.reduced).height root ≤ (Frame.ofMountain ambient).eventCut targetEvent :=
    (hLeftRootRow.symm.trans hLeftRow.symm).trans_le hLow
  have hLeft := s.marker_band_path_depth_balance history hLast hSourceWidth hTargetWidth leftPath
    hRootReal hColumn hIndex hLeftRootRow hLeftBefore hSourceLeft hQuery hRootLow hHigh
  have hRight := s.marker_band_path_depth_balance history hLast hSourceWidth hTargetWidth rightPath
    hRootReal hColumn hIndex hRightRootRow hRightBefore hSourceRight hQuery hRootLow hHigh
  dsimp only at hLeft hRight ⊢
  rw [leftCopy.source_column, rightCopy.source_column]
  omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.marker_band_path_steps
#print axioms OmegaY.Expansion.DynamicBlockState.marker_band_path_depth_balance
#print axioms OmegaY.Expansion.DynamicBlockState.marked_band_depth_comparison
