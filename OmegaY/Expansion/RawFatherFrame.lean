/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawFatherFrame.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawFatherBound

/-! Array certificates for raw father-upper bounds, their exact typed bridge,
and transport under append/restriction of complete columns. -/

namespace OmegaY.Expansion

open Canonical Geometry

def ColumnRawFatherBound (mountain : Mountain) (column : Column) : Prop :=
  ∀ index lower upper, column[index]? = some lower →
    column[index + 1]? = some upper → 0 < index → CellRawFatherBound mountain upper

def MountainRawFatherBound (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), ColumnRawFatherBound mountain mountain[c]

theorem ColumnRawFatherBound.transport {before after : Mountain} {c : Nat} {column : Column}
    (hBound : ColumnRawFatherBound before column) (hValid : ColumnValid before c column)
    (hRead : ∀ ref, ref.column < c →
      Canonical.cellAt after ref = Canonical.cellAt before ref) :
    ColumnRawFatherBound after column := by
  intro index lower upper hLower hUpper hReal ref parentUpper hLeft hParentUpper
  have hColumn := (hValid.stored_valid _ _ _ hUpper hLeft).1
  exact hBound index lower upper hLower hUpper hReal ref parentUpper hLeft
    ((hRead ⟨ref.column, ref.index + 1⟩ hColumn).symm.trans hParentUpper)

theorem MountainRawFatherBound.push {mountain : Mountain} {column : Column}
    (hBound : MountainRawFatherBound mountain) (hValid : MountainValid mountain)
    (hColumn : ColumnRawFatherBound (mountain.push column) column) :
    MountainRawFatherBound (mountain.push column) := by
  intro c hc
  by_cases he : c = mountain.size
  · subst c
    simpa only [Array.getElem_push_eq] using hColumn
  · have hOld : c < mountain.size := by simp only [Array.size_push] at hc; omega
    rw [Array.getElem_push_lt hOld]
    exact (hBound c hOld).transport (hValid c hOld)
      (fun ref hr => cellAt_push_left (hr.trans hOld))

theorem MountainRawFatherBound.prefix {before after : Mountain}
    (hBound : MountainRawFatherBound after) (hValid : MountainValid after)
    (hPrefix : PreservesColumns before after) : MountainRawFatherBound before := by
  intro c hc
  have hcAfter : c < after.size := hc.trans_le hPrefix.size_le
  have hColumn : after[c] = before[c] := Option.some.inj
    ((Array.getElem?_eq_getElem hcAfter).symm.trans
      ((hPrefix c hc).trans (Array.getElem?_eq_getElem hc)))
  rw [← hColumn]
  exact (hBound c hcAfter).transport (hValid c hcAfter)
    (fun ref hr => (hPrefix.cellAt (hr.trans hc)).symm)

theorem MountainRawFatherBound.pop {mountain : Mountain}
    (hBound : MountainRawFatherBound mountain) (hValid : MountainValid mountain) :
    MountainRawFatherBound mountain.pop := by
  apply hBound.prefix hValid
  intro c hc
  have hBeforeCut : c < mountain.size - 1 := by simpa only [Array.size_pop] using hc
  simp only [Array.getElem?_pop, hBeforeCut, ↓reduceIte]

/-- The array condition is strong enough for the typed raw-parent property
without any validity premise or numerical-parent identification. -/
theorem MountainRawFatherBound.rawFatherUpperBound {mountain : Mountain}
    (hBound : MountainRawFatherBound mountain) :
    (Frame.ofMountain mountain).RawFatherUpperBound := by
  apply rawFatherUpperBound_of_cells
  intro u upper hReal hUpper
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    rename_i hNext
    exact hBound c.val c.isLt i.val _ _ (Array.getElem?_eq_getElem i.isLt)
      (Array.getElem?_eq_getElem hNext) hReal
  · cases hUpper

private theorem rawBound_upper_of_ref {F : Frame} {before after : F.Node}
    (hRef : Frame.ref after = ⟨before.1.val, before.2.val + 1⟩) :
    F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hRef
  have hc : d = c := Fin.ext hRef.1
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, hRef.2.symm⟩

/-- Validity supplies the actual stored parent's node, not a numerical P fact. -/
theorem mountainRawFatherBound_of_rawFatherUpperBound {mountain : Mountain}
    (hValid : MountainValid mountain)
    (hBound : (Frame.ofMountain mountain).RawFatherUpperBound) :
    MountainRawFatherBound mountain := by
  intro c hc index lower upper hLower hUpper hReal ref parentUpper hLeft hParentUpper
  obtain ⟨hi, hLowerEq⟩ := Array.getElem?_eq_some_iff.mp hLower
  obtain ⟨hj, hUpperEq⟩ := Array.getElem?_eq_some_iff.mp hUpper
  let u : (Frame.ofMountain mountain).Node := ⟨⟨c, hc⟩, ⟨index, hi⟩⟩
  let v : (Frame.ofMountain mountain).Node := ⟨⟨c, hc⟩, ⟨index + 1, hj⟩⟩
  have hUV : (Frame.ofMountain mountain).upper u = some v := by
    simp [Frame.upper, u, v, Frame.ofMountain, hj]
  have hVCell : (Frame.ofMountain mountain).cell v = upper := hUpperEq
  obtain ⟨_, parent, hParent, _⟩ := (hValid c hc).stored_valid _ _ _ hUpper hLeft
  obtain ⟨p, hPRef, _⟩ := Canonical.frame_node_of_cellAt hParent
  obtain ⟨pUpper, hPURef, hPUCell⟩ := Canonical.frame_node_of_cellAt hParentUpper
  have hRaw : (Frame.ofMountain mountain).rawParent u = some p := by
    apply Frame.rawParent_eq_of_upper_left hUV
    simpa only [hVCell, hPRef] using hLeft
  have hPUpper : (Frame.ofMountain mountain).upper p = some pUpper := by
    apply rawBound_upper_of_ref
    rw [hPURef]
    have hcRef := congrArg Ref.column hPRef
    have hiRef := congrArg Ref.index hPRef
    change p.1.val = ref.column at hcRef
    change p.2.val = ref.index at hiRef
    rw [← hcRef, ← hiRef]
  have hResult := hBound u p v pUpper hReal hRaw hUV hPUpper
  simpa only [Frame.height, hVCell, hPUCell] using hResult

theorem mountainRawFatherBound_iff {mountain : Mountain} (hValid : MountainValid mountain) :
    MountainRawFatherBound mountain ↔ (Frame.ofMountain mountain).RawFatherUpperBound :=
  ⟨MountainRawFatherBound.rawFatherUpperBound,
    mountainRawFatherBound_of_rawFatherUpperBound hValid⟩

theorem mountainRawFatherBound_of_normal {mountain : Mountain}
    (hValid : MountainValid mountain) (hNormal : (Frame.ofMountain mountain).Normal) :
    MountainRawFatherBound mountain :=
  mountainRawFatherBound_of_rawFatherUpperBound hValid hNormal.rawFatherUpperBound

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnRawFatherBound.transport
#print axioms OmegaY.Expansion.MountainRawFatherBound.push
#print axioms OmegaY.Expansion.MountainRawFatherBound.prefix
#print axioms OmegaY.Expansion.MountainRawFatherBound.pop
#print axioms OmegaY.Expansion.MountainRawFatherBound.rawFatherUpperBound
#print axioms OmegaY.Expansion.mountainRawFatherBound_iff
#print axioms OmegaY.Expansion.mountainRawFatherBound_of_normal
