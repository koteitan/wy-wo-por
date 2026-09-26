/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualPhysicalStationaryIdentity.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighMarkerStationary

/-!
# Physical and stationary effective marker occurrences are identical

Strict row order in the actual finished column identifies both complete
reads. This is equality of references and cells, independent of numerical
parent recognition. A high source upper supplies stationarity automatically.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace PhysicalMarkerRead

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  {copy : EffectiveCopyOccurrence p block start references source result}
  (physical : PhysicalMarkerRead copy)

theorem eq_effective_of_stationary
    (hStationary : copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source) :
    physical.outputRef = copy.outputRef ∧ physical.cell = copy.read.outputCell := by
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := copy.data.copyColumn_valid
  have he : actual = copy.column := Except.ok.inj (hActual.symm.trans copy.read.copy_run)
  subst actual
  have hIndex := column_read_index_eq_of_row hValid physical.output_at copy.read.output_at
    (physical.source_row.trans hStationary.symm)
  have hRef : physical.outputRef = copy.outputRef := by
    change (⟨copy.before.size, physical.index⟩ : Ref) = ⟨copy.before.size, copy.read.outputIndex⟩
    rw [hIndex]
  exact ⟨hRef, Option.some.inj (physical.output_at.symm.trans (hIndex ▸ copy.read.output_at))⟩

theorem high_upper_eq_effective (hLast : 1 < last)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hSourceUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height sourceUpper) :
    physical.outputRef = copy.outputRef ∧ physical.cell = copy.read.outputCell :=
  physical.eq_effective_of_stationary
    (copy.stationary_of_marked_high_upper hLast hMarked hSourceUpper hHigh)

end PhysicalMarkerRead
end OmegaY.Expansion

#print axioms OmegaY.Expansion.PhysicalMarkerRead.eq_effective_of_stationary
#print axioms OmegaY.Expansion.PhysicalMarkerRead.high_upper_eq_effective
