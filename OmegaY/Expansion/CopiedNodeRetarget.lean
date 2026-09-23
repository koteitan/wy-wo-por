/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CopiedNodeRetarget.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedNodeOrigin

/-! A completed-column execution supplies provenance for every node in
that same column, not only the node used when the packet was first found. -/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem CopiedNodeOrigin.read_same_column
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    (other : (Frame.ofMountain result).Node) (hColumn : other.1 = node.1) :
    packet.column[other.2.val]? = some ((Frame.ofMountain result).cell other) := by
  obtain ⟨nodes, hNodes, hRead⟩ := Canonical.cellAt_ok_iff.mp
    (Canonical.cellAt_of_frame_node result other)
  have hColumnRead : result[other.1.val]? = some packet.column := by
    rw [hColumn]
    exact packet.column_read
  have hSame : nodes = packet.column := Option.some.inj (hNodes.symm.trans hColumnRead)
  exact hSame ▸ hRead

/-- The node classification is rebuilt from the same actual copy run.
All block data, histories and complete-column preservation are unchanged. -/
noncomputable def CopiedNodeOrigin.retarget
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    (other : (Frame.ofMountain result).Node) (hColumn : other.1 = node.1) :
    CopiedNodeOrigin p result other := by
  have hRead := packet.read_same_column other hColumn
  exact { packet with
    target_column := packet.target_column.trans (congrArg Fin.val hColumn).symm
    column_read := by rw [hColumn]; exact packet.column_read
    node_read := hRead
    origin := Classical.choice (packet.data.copyColumn_cell_origin packet.copy_run hRead) }

@[simp] theorem CopiedNodeOrigin.retarget_data
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    (other : (Frame.ofMountain result).Node) (hColumn : other.1 = node.1) :
    (packet.retarget other hColumn).data = packet.data := rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.CopiedNodeOrigin.read_same_column
#print axioms OmegaY.Expansion.CopiedNodeOrigin.retarget
