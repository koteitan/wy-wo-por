/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighSourceRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighCurrentRecognition
import OmegaY.Expansion.ActualAnyHighDirectParent
import OmegaY.Expansion.PreservedAnyLastBlocker

/-!
# High-source recognition from actual execution, without a blocker packet

The real source P and Q queries determine the branch. Actual history
constructs any required last-blocker packet, and complete-column preservation
places it in the final output. The source-parentless case is also covered:
its copied occurrence is a true top and cannot have a raw parent.
Only strictly left/strictly higher target recognition is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem high_source_real {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last) (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source) :
    Real source := by
  have hUnmarked := copy.state.high_source_not_marked hLast source.1.isLt
    copy.data copy.read.source_at hHigh
  by_contra hNot
  have hi : source.2.val = 0 := by unfold Real at hNot; omega
  exact hUnmarked (List.mem_map.mpr ⟨⟨source.1.val, 0⟩, copy.data.phantom_marker, hi.symm⟩)

/-- Main high-source entrance for raw-search induction. No source parent,
source candidate, last-blocker packet, target path or target comparison
is supplied. `before` is the real prefix of this particular block; it is
not identified with the final expansion mountain. -/
theorem DynamicBlockState.recognize_high_source
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies startCopies next : Nat} {start before result : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next before)
    (history : CopyRunHistory p block start references next before)
    (hPreserved : PreservesColumns before result)
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    (hCopies : 0 < copies) (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hBefore : source.1.val < next)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source)
    {current father : (Frame.ofMountain result).Node}
    (hCurrentRef : Frame.ref current = copy.outputRef)
    (hRaw : (Frame.ofMountain result).rawParent current = some father)
    (hLeft : ∀ (node parent : (Frame.ofMountain result).Node),
      node.1.val < current.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent)
    (hHigher : ∀ (node parent : (Frame.ofMountain result).Node), node.1 = current.1 →
      (Frame.ofMountain result).height current < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent) :
    (Frame.ofMountain result).P current = some father := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hSourceReal := high_source_real copy hLast hHigh
  cases hSourceP : F.P source with
  | none =>
    have hSourceTop : F.upper source = none := by
      cases hUpper : F.upper source with
      | none => rfl
      | some upper =>
        obtain ⟨parent, hParent, _⟩ := hNormal.upper_step source upper hSourceReal hUpper
        rw [hSourceP] at hParent
        cases hParent
    have hTargetTop := copy.top_upper_none hLast hSourceTop hCurrentRef
    rw [Frame.rawParent_none_of_upper_none hTargetTop] at hRaw
    cases hRaw
  | some parent =>
    rcases s.recorded_any_last_blocker history hLast hStartRun hSourceP
        copy.state.next_lower hBefore with hDirect | hPacket
    · obtain ⟨oldCopy⟩ := s.prior_effective_occurrence history hLast copy.state.next_lower hBefore
      obtain ⟨oldCurrent, oldFather, hOldRef, _, _, hOldRaw, hOldP, _⟩ :=
        s.recorded_any_high_direct_parent history hLast hStartRun oldCopy hSourceP hDirect hBefore hHigh
      have hCopyRef := ((oldCopy.extend hPreserved).unique copy).1
      have hMappedRef : Frame.ref (hPreserved.mapNode oldCurrent) = Frame.ref current :=
        (hPreserved.mapNode_ref oldCurrent).trans (hOldRef.trans (hCopyRef.trans hCurrentRef.symm))
      have heCurrent : hPreserved.mapNode oldCurrent = current := Executable.ref_injective G hMappedRef
      have hMappedP := hPreserved.mapNode_P s.ambient_valid.toOrdered hValid.toOrdered hOldP
      have hMappedRaw := hPreserved.mapNode_rawParent hOldRaw
      rw [heCurrent] at hMappedP hMappedRaw
      have heFather : hPreserved.mapNode oldFather = father :=
        Option.some.inj (hMappedRaw.symm.trans hRaw)
      exact heFather ▸ hMappedP
    · obtain ⟨packet⟩ := hPacket
      let finalPacket := packet.extend hPreserved
      have hCopyRef := (finalPacket.pair.uCopy.unique copy).1
      have heCurrent : finalPacket.pair.u = current := Executable.ref_injective G
        (finalPacket.pair.u_ref.trans (hCopyRef.trans hCurrentRef.symm))
      have hP := finalPacket.recognize_high_current s history hPreserved hLast hLegal
        hCopies hRun hStartRun hBefore hHigh
        (by simpa only [heCurrent] using hLeft)
        (by simpa only [heCurrent] using hHigher)
      have hRawPacket := finalPacket.pair.u_parent
      rw [heCurrent] at hP hRawPacket
      have heFather : finalPacket.pair.parent = father := Option.some.inj (hRawPacket.symm.trans hRaw)
      exact heFather ▸ hP

/-- The same entrance yields full raw/numerical agreement, including
missing raw parents, using the independently verified output sums and tops. -/
theorem DynamicBlockState.high_source_rawParent_eq_P
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies startCopies next : Nat} {start before result : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next before)
    (history : CopyRunHistory p block start references next before)
    (hPreserved : PreservesColumns before result)
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    (hCopies : 0 < copies) (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hBefore : source.1.val < next)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source)
    {current : (Frame.ofMountain result).Node}
    (hCurrentRef : Frame.ref current = copy.outputRef)
    (hLeft : ∀ (node parent : (Frame.ofMountain result).Node),
      node.1.val < current.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent)
    (hHigher : ∀ (node parent : (Frame.ofMountain result).Node), node.1 = current.1 →
      (Frame.ofMountain result).height current < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent) :
    (Frame.ofMountain result).rawParent current = (Frame.ofMountain result).P current := by
  have hSourceReal := high_source_real copy hLast hHigh
  have hCurrentReal : Real current := by
    have hIndex := congrArg Ref.index hCurrentRef
    change current.2.val = copy.read.outputIndex at hIndex
    change 0 < current.2.val
    rw [hIndex]
    exact copy.read.output_real hSourceReal
  obtain ⟨hSums, hTops⟩ := expandDiagram_equations hLegal hRun
  exact hSums.rawParent_eq_P_of_recognition (expandDiagram_valid_of_success hLegal hRun)
    hTops hCurrentReal (fun father hRaw => s.recognize_high_source history hPreserved
      hLast hLegal hCopies hRun hStartRun copy hBefore hHigh hCurrentRef hRaw hLeft hHigher)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recognize_high_source
#print axioms OmegaY.Expansion.DynamicBlockState.high_source_rawParent_eq_P
