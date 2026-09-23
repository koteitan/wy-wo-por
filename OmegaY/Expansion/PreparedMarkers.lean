/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedMarkers.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Canonical.Domain
import OmegaY.Expansion.Preparation
import OmegaY.Expansion.CanonicalMarkers
import OmegaY.Expansion.MarkerCompleteness
import OmegaY.Expansion.MarkerOrder

/-! Readiness facts for the actual prepared marker array. No additional
legality, successful enumeration, or phantom-chain hypothesis is needed:
the Preparation record already contains the two actual build equations.
These facts concern the initial reduced mountain, not arbitrary copies. -/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.reduced_normal {front : List Nat} {last : Nat}
    (p : Preparation front last) : (Geometry.Frame.ofMountain p.reduced).Normal :=
  build_normal_of_success p.reduced_build

theorem Preparation.root_valid {front : List Nat} {last : Nat}
    (p : Preparation front last) : ValidRef p.reduced p.root :=
  ⟨p.rootCell, cellAt_ok_iff.mp p.restored_root⟩

theorem Preparation.marker_iff {front : List Nat} {last : Nat}
    (p : Preparation front last) {bucket : Nat} {entry : Ref} :
    BucketMem p.marked bucket entry ↔ MarkerSpec p.reduced p.root bucket entry :=
  markers_member_iff
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    p.root_valid p.markers_built

theorem Preparation.phantom_marker {front : List Nat} {last : Nat}
    (p : Preparation front last) {column : Nat}
    (hright : p.root.column < column) (hc : column < p.reduced.size) :
    BucketMem p.marked column ⟨column, 0⟩ :=
  markers_phantom_mem
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    p.root_valid p.markers_built
    (build_phantomChain (build_success_legal p.reduced_build) p.reduced_build) hright hc

theorem Preparation.markers_ordered {front : List Nat} {last : Nat}
    (p : Preparation front last) (bucket : Nat) :
    (p.marked[bucket]?.getD []).Pairwise (fun a b => b.index < a.index) ∧
      (p.marked[bucket]?.getD []).Nodup := by
  have hlocal := weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources
  exact ⟨markers_bucket_strict_index p.reduced_valid.toOrdered hlocal
      p.root_valid p.markers_built bucket,
    markers_bucket_nodup p.reduced_valid.toOrdered hlocal
      p.root_valid p.markers_built bucket⟩

/-- The marker traversal in every right-hand source column ends at its
phantom. This includes order, not only the phantom's membership. -/
theorem Preparation.markers_last_phantom {front : List Nat} {last : Nat}
    (p : Preparation front last) {column : Nat}
    (hright : p.root.column < column) (hc : column < p.reduced.size) :
    (p.marked[column]?.getD []).getLast? = some ⟨column, 0⟩ := by
  have hmem := p.phantom_marker hright hc
  have horder := (p.markers_ordered column).1
  change (⟨column, 0⟩ : Ref) ∈ p.marked[column]?.getD [] at hmem
  obtain ⟨frontRefs, tailRefs, he, _⟩ := List.eq_append_cons_of_mem hmem
  rw [he] at horder ⊢
  have htail : tailRefs = [] := by
    have hrest := (List.pairwise_append.mp horder).2.1
    have hsmall := (List.pairwise_cons.mp hrest).1
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry hentry
    have hneg := hsmall entry hentry
    exact Nat.not_lt_zero entry.index hneg
  simp [htail]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.marker_iff
#print axioms OmegaY.Expansion.Preparation.phantom_marker
#print axioms OmegaY.Expansion.Preparation.markers_last_phantom
