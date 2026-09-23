/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFixedBlockerValue.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFixedSourceValue
import OmegaY.Expansion.ActualAnyLastBlocker

/-!
# Exact blocker comparisons when the common source father is fixed

The source blocker may remain in the old prefix or have its own effective
copy. In both cases its complete numerical value is retained, as is the
current source's value. Thus weak, strict and equality comparisons are
preserved by actual copying without target numerical induction or a depth
word transport. A blocker in or left of the root column automatically has
such a good-part father. Identification of the current target Q record
path remains a separate obligation.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace AnyCommonParentPair

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node}
  (pair : AnyCommonParentPair p block start references sourceU sourceZ sourceParent result)

theorem values_of_fixed_parent (hLast : 1 < last)
    {input : List Nat} (hLegal : Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    (hUParent : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZParent : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hFixed : sourceParent.1.val < p.root.column) :
    (Frame.ofMountain result).value pair.u = (Frame.ofMountain p.reduced).value sourceU ∧
      (Frame.ofMountain result).value pair.z = (Frame.ofMountain p.reduced).value sourceZ := by
  constructor
  · exact (congrArg Cell.value pair.u_cell).trans
      (pair.uCopy.value_of_fixed_parent_expansion hLast hLegal hRun hUParent hFixed)
  · rcases pair.z_origin with ⟨_, _, hCell⟩ | ⟨_, zCopy, _, hCell⟩
    · exact congrArg Cell.value hCell
    · exact (congrArg Cell.value hCell).trans
        (zCopy.value_of_fixed_parent_expansion hLast hLegal hRun hZParent hFixed)

/-- Exact comparison includes a genuinely unchanged good/root-column
blocker and a newly copied current node. No target comparison is a premise. -/
theorem comparison_of_fixed_parent (hLast : 1 < last)
    {input : List Nat} (hLegal : Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    (hUParent : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZParent : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hFixed : sourceParent.1.val < p.root.column) :
    ((Frame.ofMountain result).value pair.u ≤ (Frame.ofMountain result).value pair.z ↔
      (Frame.ofMountain p.reduced).value sourceU ≤ (Frame.ofMountain p.reduced).value sourceZ) ∧
    ((Frame.ofMountain result).value pair.u < (Frame.ofMountain result).value pair.z ↔
      (Frame.ofMountain p.reduced).value sourceU < (Frame.ofMountain p.reduced).value sourceZ) ∧
    ((Frame.ofMountain result).value pair.u = (Frame.ofMountain result).value pair.z ↔
      (Frame.ofMountain p.reduced).value sourceU = (Frame.ofMountain p.reduced).value sourceZ) := by
  obtain ⟨hu, hz⟩ := pair.values_of_fixed_parent hLast hLegal hRun hUParent hZParent hFixed
  rw [hu, hz]
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

end AnyCommonParentPair

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

theorem fixed_parent_barrier (hLast : 1 < last)
    {input : List Nat} (hLegal : Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    (hFixed : sourceParent.1.val < p.root.column) :
    (Frame.ofMountain result).value packet.pair.u ≤ (Frame.ofMountain result).value packet.pair.z := by
  obtain ⟨hu, hz⟩ := packet.pair.values_of_fixed_parent hLast hLegal hRun
    packet.source_parent packet.source_last_parent hFixed
  rw [hu, hz]
  exact packet.source_value

/-- If the actual source last blocker lies in or left of the root column,
the common father is automatically in the strictly fixed good part. -/
theorem unchanged_blocker_barrier (hLast : 1 < last)
    {input : List Nat} (hLegal : Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    (hBlocker : packet.blocker.1.val ≤ p.root.column) :
    (Frame.ofMountain result).value packet.pair.u ≤ (Frame.ofMountain result).value packet.pair.z := by
  exact packet.fixed_parent_barrier hLast hLegal hRun
    ((P_column_lt (build_normal_of_success p.reduced_build).toOrdered packet.source_last_parent).trans_le hBlocker)

end AnySourceBlockerPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.AnyCommonParentPair.values_of_fixed_parent
#print axioms OmegaY.Expansion.AnyCommonParentPair.comparison_of_fixed_parent
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.fixed_parent_barrier
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.unchanged_blocker_barrier
