/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualPhysicalMarkerRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualPhysicalMarkerSearch
import OmegaY.Expansion.ActualBlockerRecognition
import OmegaY.Expansion.ActualHighDirectParent

/-!
# Numerical parent recognition of physical marker copies

The source search supplies its last rejected record. Every source record
on that path is marked, and actual copy history constructs each physical
occurrence and raw edge. Numerical recognition is used only strictly left
of the current physical marker. Its last-blocker value comparison remains
explicit; no copied comparison or global numerical correctness is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace PhysicalMarkerRead

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  {copy : EffectiveCopyOccurrence p block start references source result}
  (physical : PhysicalMarkerRead copy)

theorem unique_ref {otherCopy : EffectiveCopyOccurrence p block start references source result}
    (other : PhysicalMarkerRead otherCopy) (hValid : MountainValid result) :
    physical.outputRef = other.outputRef := by
  obtain ⟨u, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt physical.output_read
  obtain ⟨v, hVRef, hVCell⟩ := Canonical.frame_node_of_cellAt other.output_read
  have hColumn := physical.source_column.trans other.source_column.symm
  have hRow := physical.source_row.trans other.source_row.symm
  have he : u = v := Frame.node_eq_of_column_height hValid.toOrdered
    (Fin.ext ((congrArg Ref.column hURef).trans (hColumn.trans (congrArg Ref.column hVRef).symm)))
    (by simpa only [Frame.height, hUCell, hVCell] using hRow)
  exact hURef.symm.trans ((congrArg Frame.ref he).trans hVRef)

theorem index_positive (hReal : Frame.Real source) : 0 < physical.index := by
  have hNormal := build_normal_of_success p.reduced_build
  have hPositive : (0 : Row) < physical.cell.row := by
    rw [physical.source_row]
    exact Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hReal)
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := copy.data.copyColumn_valid
  have he : actual = copy.column := Except.ok.inj (hActual.symm.trans copy.read.copy_run)
  subst actual
  by_contra hn
  have hi : physical.index = 0 := by omega
  have hPhantom : physical.cell = phantom :=
    Option.some.inj ((hi ▸ physical.output_at).symm.trans hValid.phantom)
  rw [hPhantom] at hPositive
  exact (lt_irrefl (0 : Row)) hPositive

theorem frame_real (hReal : Frame.Real source) {u : (Frame.ofMountain result).Node}
    (hRef : Frame.ref u = physical.outputRef) : Frame.Real u := by
  have hIndex := congrArg Ref.index hRef
  change u.2.val = physical.index at hIndex
  change 0 < u.2.val
  rw [hIndex]
  exact physical.index_positive hReal

/-- A source direct hit stays a direct hit at the physical copied marker.
Positive actual backfill supplies strict smallness, so no blocker comparison
or numerical-recognition induction hypothesis is needed. -/
theorem recognize_direct (hLast : 1 < last) (hValid : MountainValid result)
    (hSums : MountainSums result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent : (Frame.ofMountain p.reduced).Node}
    {parentCopy : EffectiveCopyOccurrence p block start references parent result}
    (parentPhysical : PhysicalMarkerRead parentCopy)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hDirect : (Frame.ofMountain p.reduced).Q source = some parent)
    (hRight : p.root.column < parent.1.val) :
    findParent result physical.outputRef = .ok parentPhysical.outputRef := by
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨u, father, hURef, hFatherRef, hQ, _⟩ :=
    physical.candidate_eq hValid hMarked parentPhysical hParent hDirect hRight
  have hRaw := (physical.raw_parent hLast hValid hMarked parentPhysical hParent hRight).1.rawParent hURef hFatherRef
  have hP := hSums.P_of_Q_rawParent hValid (physical.frame_real hReal hURef) hQ hRaw
  simpa only [hURef, hFatherRef] using (Executable.findParent_ref_iff hValid.toOrdered u father).mpr hP

end PhysicalMarkerRead

/-- A marked source record path gives an actual physical raw path. Marker
membership propagates along each source edge; every intermediate occurrence
comes from the real recorded copy history. -/
theorem DynamicBlockState.recorded_physical_path
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (path : Frame.ParentPath (Frame.ofMountain p.reduced) child parent)
    (hMarked : BucketMem p.marked child.1.val (Frame.ref child))
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    {childCopy : EffectiveCopyOccurrence p block start references child ambient}
    {parentCopy : EffectiveCopyOccurrence p block start references parent ambient}
    (childPhysical : PhysicalMarkerRead childCopy) (parentPhysical : PhysicalMarkerRead parentCopy) :
    RawRefPath ambient childPhysical.outputRef parentPhysical.outputRef := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  induction path with
  | refl source =>
      have he := childPhysical.unique_ref parentPhysical s.ambient_valid
      exact he ▸ RawRefPath.refl childPhysical.outputRef
  | @cons child middle parent hEdge tail ih =>
      have hMiddleRight := hRight.trans_le (tail.column_le hNormal.toOrdered)
      have hMiddleBefore := (Frame.P_column_lt hNormal.toOrdered hEdge).trans hBefore
      have hMiddleMarked := (build_marked_parent p.reduced_build hMarkers hEdge hMarked
        ((congrArg Ref.column hRootRef).trans_lt hMiddleRight)).1
      obtain ⟨middleCopy⟩ := s.prior_effective_occurrence history hLast hMiddleRight hMiddleBefore
      obtain ⟨middlePhysical⟩ := middleCopy.physical_marker_read hMiddleMarked
      exact .cons (childPhysical.raw_parent hLast s.ambient_valid hMarked middlePhysical hEdge hMiddleRight).1
        (ih hMiddleMarked hRight hMiddleBefore middlePhysical parentPhysical)

/-- The actual source search chooses either an unconditional physical direct
hit or an actual copied last blocker whose one value inequality suffices.
No target candidate, target path, or target edge is supplied by the caller.
The original source blocker inequality is reported separately from its
still-needed copied counterpart. -/
theorem DynamicBlockState.physical_marker_recognition
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hSums : MountainSums ambient)
    {source parent : (Frame.ofMountain p.reduced).Node}
    {sourceCopy : EffectiveCopyOccurrence p block start references source ambient}
    (physical : PhysicalMarkerRead sourceCopy)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    (hRight : p.root.column < parent.1.val) (hBefore : source.1.val < next)
    (hLeft : ∀ (node father : (Frame.ofMountain ambient).Node),
      node.1.val < physical.outputRef.column → Frame.Real node →
      (Frame.ofMountain ambient).rawParent node = some father →
      (Frame.ofMountain ambient).P node = some father) :
    ∃ (parentCopy : EffectiveCopyOccurrence p block start references parent ambient)
      (parentPhysical : PhysicalMarkerRead parentCopy),
      ((Frame.ofMountain p.reduced).Q source = some parent ∧
        findParent ambient physical.outputRef = .ok parentPhysical.outputRef) ∨
      ∃ (blocker : (Frame.ofMountain p.reduced).Node)
        (blockerCopy : EffectiveCopyOccurrence p block start references blocker ambient)
        (blockerPhysical : PhysicalMarkerRead blockerCopy),
        (Frame.ofMountain p.reduced).P blocker = some parent ∧
        BucketMem p.marked blocker.1.val (Frame.ref blocker) ∧
        (Frame.ofMountain p.reduced).value source ≤ (Frame.ofMountain p.reduced).value blocker ∧
        (physical.cell.value ≤ blockerPhysical.cell.value →
          findParent ambient physical.outputRef = .ok parentPhysical.outputRef) := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  have hRootRight := (congrArg Ref.column hRootRef).trans_lt hRight
  have hParentMarked := (build_marked_parent p.reduced_build hMarkers hParent hMarked hRootRight).1
  obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hRight
    ((Frame.P_column_lt hNormal.toOrdered hParent).trans hBefore)
  obtain ⟨parentPhysical⟩ := parentCopy.physical_marker_read hParentMarked
  refine ⟨parentCopy, parentPhysical, ?_⟩
  obtain ⟨q, hQ, hDirect | ⟨z, uUpper, zUpper, sourcePath, hLastParent, hZRightParent, hZBefore,
      hUUpper, hZUpper, hLower, hOverlap, _, hSourceBarrier, _⟩⟩ :=
    build_source_last_blocker p.reduced_build hParent
  · have hDirectQ : F.Q source = some parent := hDirect ▸ hQ
    exact Or.inl ⟨hDirectQ, physical.recognize_direct hLast s.ambient_valid hSums
      hMarked parentPhysical hParent hDirectQ hRight⟩
  · have hQMarked := (build_marked_candidate p.reduced_build hMarkers hParent hQ hMarked hRootRight).1
    have hZMarked := (build_common_parent_marker_iff p.reduced_build hMarkers hParent hLastParent
      hZUpper hLower hOverlap hRootRight.le).mp hMarked
    have hZRight := hRight.trans hZRightParent
    have hQRight := hZRight.trans_le (sourcePath.column_le hNormal.toOrdered)
    have hQBefore := (Frame.Q_column_lt hNormal.toOrdered hQ).trans hBefore
    obtain ⟨candidateCopy⟩ := s.prior_effective_occurrence history hLast hQRight hQBefore
    obtain ⟨candidatePhysical⟩ := candidateCopy.physical_marker_read hQMarked
    obtain ⟨blockerCopy⟩ := s.prior_effective_occurrence history hLast hZRight (hZBefore.trans hBefore)
    obtain ⟨blockerPhysical⟩ := blockerCopy.physical_marker_read hZMarked
    have rawPath := s.recorded_physical_path history hLast sourcePath hQMarked hZRight hQBefore
      candidatePhysical blockerPhysical
    obtain ⟨u, candidate, hURef, hCandidateRef, hActualQ, _⟩ := physical.candidate_eq
      s.ambient_valid hMarked candidatePhysical hParent hQ hRight
    obtain ⟨actualParent, hParentRef, _⟩ := Canonical.frame_node_of_cellAt parentPhysical.output_read
    obtain ⟨actualZ, hZRef, hZCell⟩ := Canonical.frame_node_of_cellAt blockerPhysical.output_read
    have hUReal := physical.frame_real hReal hURef
    have hUCell : G.cell u = physical.cell := by
      have hRead := Canonical.cellAt_of_frame_node ambient u
      rw [hURef] at hRead
      exact Except.ok.inj (hRead.symm.trans physical.output_read)
    have hUColumn : u.1.val = physical.outputRef.column := congrArg Ref.column hURef
    have hLeftAtU : ∀ (node father : G.Node), node.1.val < u.1.val → Frame.Real node →
        G.rawParent node = some father → G.P node = some father := by
      intro node father hCol hNodeReal hRaw
      exact hLeft node father (hCol.trans_eq hUColumn) hNodeReal hRaw
    have path := rawPath.toParentPath_of_recognition s.ambient_valid.toOrdered hLeftAtU
      hCandidateRef hZRef (Frame.Q_real s.ambient_valid.toOrdered hUReal hActualQ)
      (Frame.Q_column_lt s.ambient_valid.toOrdered hActualQ)
    have hZRealSource := Frame.real_of_value_pos hNormal.toOrdered
      ((Frame.P_value hNormal.toOrdered hLastParent).1.trans (Frame.P_value hNormal.toOrdered hLastParent).2)
    have hZReal := blockerPhysical.frame_real hZRealSource hZRef
    have hRawZ := (blockerPhysical.raw_parent hLast s.ambient_valid hZMarked parentPhysical
      hLastParent hRight).1.rawParent hZRef hParentRef
    have hZParent := hLeftAtU actualZ actualParent
      ((path.column_le s.ambient_valid.toOrdered).trans_lt (Frame.Q_column_lt s.ambient_valid.toOrdered hActualQ))
      hZReal hRawZ
    have hRawU := (physical.raw_parent hLast s.ambient_valid hMarked parentPhysical hParent hRight).1.rawParent
      hURef hParentRef
    obtain ⟨actualUpper, hActualUpper, _⟩ := Frame.rawParent_spec hRawU
    obtain ⟨actual, hActual, _, _, hSmall, _⟩ := hSums.rawParent_upper s.ambient_valid hUReal hActualUpper
    have he : actual = actualParent := Option.some.inj (hActual.symm.trans hRawU)
    subst actual
    refine Or.inr ⟨z, blockerCopy, blockerPhysical, hLastParent, hZMarked, hSourceBarrier, ?_⟩
    intro hBarrier
    have hValues : G.value u ≤ G.value actualZ := by
      have hZCell' : G.cell actualZ = blockerPhysical.cell := hZCell
      change (G.cell u).value ≤ (G.cell actualZ).value
      rw [hUCell, hZCell']
      exact hBarrier
    have hP := Frame.P_of_record_barrier s.ambient_valid.toOrdered hActualQ path hZParent hValues hSmall
    simpa only [hURef, hParentRef] using (Executable.findParent_ref_iff s.ambient_valid.toOrdered u actualParent).mpr hP

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PhysicalMarkerRead.unique_ref
#print axioms OmegaY.Expansion.PhysicalMarkerRead.frame_real
#print axioms OmegaY.Expansion.PhysicalMarkerRead.recognize_direct
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_physical_path
#print axioms OmegaY.Expansion.DynamicBlockState.physical_marker_recognition
