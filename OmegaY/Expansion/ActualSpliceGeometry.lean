/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSpliceGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualOrdinarySplice
import OmegaY.Expansion.ActualBoundarySplice

/-! The complete finite splice geometry of every actual block graph.
Actual retained, boundary and ordinary classifications exhaust each real
edge by its physical child column. All virtual lower reserves are used
as demands; there is no output-classification hypothesis. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem Preparation.actual_splice_edge_classified
    {front : List Nat} {last : Nat} (p : Preparation front last)
    (g : RootGeometry p) (hLast : 1 < last) (D : Nat)
    (hDimension : MountainKeyDimension p.initial D) (block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1)))) :
    Splice.ReservoirClassified (Splice.blockCut p.root_before_last block)
      (p.spliceGraph hLast D block) (p.spliceFacts D block) (g.spliceVirtualFacts D block)
      (p.spliceLocalEdgeAtom hLast D block edge) := by
  rcases lt_trichotomy edge.lower.1.val (p.spliceMountain hLast block).size with hBefore | hAt | hAfter
  · exact p.retained_splice_classified hLast D block (g.spliceVirtualFacts D block) edge hBefore
  · exact p.boundary_splice_classified g hLast D block hDimension edge hAt
  · exact p.ordinary_splice_classified hLast D block hDimension (g.spliceVirtualFacts D block) edge hAfter

theorem Preparation.actual_splice_geometry
    {front : List Nat} {last : Nat} (p : Preparation front last)
    (g : RootGeometry p) (hLast : 1 < last) (D : Nat)
    (hDimension : MountainKeyDimension p.initial D) (block : Nat) :
    Splice.BlockReservoirGeometry p.root_before_last block
      (p.spliceGraph hLast D block) (p.spliceFacts D block)
      (g.spliceVirtualFacts D block) (p.spliceGraph hLast D (block + 1)) := by
  intro atom hAtom
  obtain ⟨next, hNext, rfl⟩ := List.mem_map.mp hAtom
  obtain ⟨edge, _hEdge, rfl⟩ := List.mem_map.mp hNext
  change Splice.ReservoirClassified (Splice.blockCut p.root_before_last block)
    (p.spliceGraph hLast D block) (p.spliceFacts D block) (g.spliceVirtualFacts D block)
    (p.spliceLocalEdgeAtom hLast D block edge)
  exact p.actual_splice_edge_classified g hLast D hDimension block edge

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.actual_splice_geometry
#print axioms OmegaY.Expansion.Preparation.actual_splice_edge_classified
