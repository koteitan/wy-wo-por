/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawSearchReconstruction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.TotalRawGeometry
import OmegaY.Expansion.ReconstructionCertificate

/-!
# Canonical reconstruction after numerical parent-search recovery

The actual expansion already has the complete stored-parent B row law.
The remaining search condition compares only the stored parent with the
numerical ancestor search. It does not repeat the row equation, assume
output Normal, or assert that the search condition has been proved for
all actual expansions.
-/

namespace OmegaY.Geometry.Frame

/-- Every existing real stored parent is recovered by numerical P.
The equality is deliberately an explicit remaining condition. -/
def RawParentSearch (F : Frame) : Prop :=
  ∀ u parent, Real u → F.rawParent u = some parent → F.P u = some parent

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- Search agreement for the actual stored reference on each real adjacent
pair. No ordinal row formula is included in this predicate. -/
def ColumnParentSearch (mountain : Mountain) (c : Nat) (column : Column) : Prop :=
  ∀ index lower upper ref, column[index]? = some lower →
    column[index + 1]? = some upper → 0 < index → upper.left = some ref →
    findParent mountain ⟨c, index⟩ = .ok ref

def MountainParentSearch (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), ColumnParentSearch mountain c mountain[c]

/-- Under the independently proved raw row law, the old geometry packet
contains exactly the remaining search condition. -/
theorem mountainParentGeometry_iff_parentSearch {mountain : Mountain}
    (hRaw : MountainRawGeometry mountain) :
    MountainParentGeometry mountain ↔ MountainParentSearch mountain := by
  constructor
  · intro hGeometry c hc index lower upper ref hLower hUpper hReal hLeft
    obtain ⟨actualRef, parent, hActualLeft, _, hFind, _⟩ :=
      hGeometry c hc index lower upper hLower hUpper hReal
    have he : actualRef = ref := Option.some.inj (hActualLeft.symm.trans hLeft)
    exact he ▸ hFind
  · intro hSearch c hc index lower upper hLower hUpper hReal
    obtain ⟨ref, parent, hLeft, hRead, _, _, hB⟩ :=
      hRaw c hc index lower upper hLower hUpper hReal
    exact ⟨ref, parent, hLeft, hRead,
      hSearch c hc index lower upper ref hLower hUpper hReal hLeft, hB⟩

/-- Typed search recovery implies the actual array search equation.
Ordered stored-reference validity supplies the real parent lookup; no
numeric Normal or raw B equation is used. -/
theorem mountainParentSearch_of_rawParentSearch {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    (hSearch : (Frame.ofMountain mountain).RawParentSearch) :
    MountainParentSearch mountain := by
  intro c hc index lower upper ref hLower hUpper hReal hLeft
  obtain ⟨hi, hLowerEq⟩ := Array.getElem?_eq_some_iff.mp hLower
  obtain ⟨hj, hUpperEq⟩ := Array.getElem?_eq_some_iff.mp hUpper
  let u : (Frame.ofMountain mountain).Node := ⟨⟨c, hc⟩, ⟨index, hi⟩⟩
  let v : (Frame.ofMountain mountain).Node := ⟨⟨c, hc⟩, ⟨index + 1, hj⟩⟩
  have hUV : (Frame.ofMountain mountain).upper u = some v := by
    simp [Frame.upper, u, v, Frame.ofMountain, hj]
  have hVCell : (Frame.ofMountain mountain).cell v = upper := hUpperEq
  have hStored : ((Frame.ofMountain mountain).cell v).left = some ref := by
    rw [hVCell]
    exact hLeft
  obtain ⟨parent, hLookup, _, _⟩ := hOrdered.stored_valid v ref hStored
  have hRef : Frame.ref parent = ref := Frame.lookup_spec hLookup
  have hRaw : (Frame.ofMountain mountain).rawParent u = some parent :=
    Frame.rawParent_eq_of_upper_left hUV (by rw [hRef]; exact hStored)
  have hFind := (Executable.findParent_ref_iff hOrdered u parent).mpr (hSearch u parent hReal hRaw)
  exact hRef ▸ hFind

/-- Array search agreement recovers typed numerical P for every actual
real stored edge. -/
theorem rawParentSearch_of_mountainParentSearch {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    (hSearch : MountainParentSearch mountain) :
    (Frame.ofMountain mountain).RawParentSearch := by
  intro u parent hReal hRaw
  obtain ⟨upper, hUpper, hLeft⟩ := Frame.rawParent_spec hRaw
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    rename_i hNext
    have hFind := hSearch c.val c.isLt i.val _ _ (Frame.ref parent)
      (Array.getElem?_eq_getElem i.isLt) (Array.getElem?_eq_getElem hNext) hReal hLeft
    exact (Executable.findParent_ref_iff hOrdered ⟨c, i⟩ parent).mp hFind
  · cases hUpper

theorem mountainParentSearch_iff_rawParentSearch {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered) :
    MountainParentSearch mountain ↔ (Frame.ofMountain mountain).RawParentSearch :=
  ⟨rawParentSearch_of_mountainParentSearch hOrdered,
    mountainParentSearch_of_rawParentSearch hOrdered⟩

/-- Sums, tops, and the raw row law reduce numerical Normal to the
remaining parent-search condition. The search premise is not discharged. -/
theorem normal_of_raw_geometry_parent_search {mountain : Mountain}
    (hValid : MountainValid mountain) (hSums : MountainSums mountain)
    (hTops : MountainTops mountain) (hRaw : MountainRawGeometry mountain)
    (hSearch : MountainParentSearch mountain) : (Frame.ofMountain mountain).Normal :=
  normal_of_sums_geometry hValid hSums hTops
    ((mountainParentGeometry_iff_parentSearch hRaw).mpr hSearch)

/-- On an actual expanded diagram, every old parent-geometry obligation
is equivalent to search agreement alone. The B law is supplied by the
unconditional execution theorem. -/
theorem expansion_parent_geometry_iff_search {input : List Nat} (hLegal : Legal input)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram input copies = .ok mountain) :
    MountainParentGeometry mountain ↔ MountainParentSearch mountain :=
  mountainParentGeometry_iff_parentSearch (expandDiagram_raw_geometry hLegal hRun)

/-- Exact reconstruction of every row, value, and stored reference from
the actual returned values, conditional solely on numerical parent-search
agreement. Bottom legs and raw row geometry are supplied by execution. -/
theorem reconstruct_expansion_of_parent_search {input : List Nat} (hLegal : Legal input)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram input copies = .ok mountain)
    (hSearch : MountainParentSearch mountain)
    {values : List Nat} (hValues : valuesOf mountain = .ok values) :
    Canonical.build values = .ok mountain :=
  reconstruct_expansion_of_parent_geometry hLegal hRun
    (expandDiagram_bottom_legs hLegal hRun)
    ((expansion_parent_geometry_iff_search hLegal hRun).mpr hSearch) hValues

/-- Typed event/record proofs can use the same reconstruction theorem
without constructing an additional array-level certificate. -/
theorem reconstruct_expansion_of_raw_parent_search {input : List Nat} (hLegal : Legal input)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram input copies = .ok mountain)
    (hSearch : (Frame.ofMountain mountain).RawParentSearch)
    {values : List Nat} (hValues : valuesOf mountain = .ok values) :
    Canonical.build values = .ok mountain := by
  obtain ⟨actual, hActual, hValid⟩ := expandDiagram_total hLegal copies
  have he : actual = mountain := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  exact reconstruct_expansion_of_parent_search hLegal hRun
    (mountainParentSearch_of_rawParentSearch hValid.toOrdered hSearch) hValues

end OmegaY.Expansion

#print axioms OmegaY.Expansion.mountainParentGeometry_iff_parentSearch
#print axioms OmegaY.Expansion.mountainParentSearch_of_rawParentSearch
#print axioms OmegaY.Expansion.rawParentSearch_of_mountainParentSearch
#print axioms OmegaY.Expansion.mountainParentSearch_iff_rawParentSearch
#print axioms OmegaY.Expansion.normal_of_raw_geometry_parent_search
#print axioms OmegaY.Expansion.expansion_parent_geometry_iff_search
#print axioms OmegaY.Expansion.reconstruct_expansion_of_parent_search
#print axioms OmegaY.Expansion.reconstruct_expansion_of_raw_parent_search
