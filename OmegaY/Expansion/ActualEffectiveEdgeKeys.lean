/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveEdgeKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAllScaleRoots
import OmegaY.Expansion.TotalRawGeometry

/-!
# Actual ordinary/effective copied-edge keys do not increase

Only the actual effective lower's reference must be identified with the
target edge. Its father, upper, degree and scale roots are then recovered
from execution and raw geometry. All finite key coordinates obey the
literal column map (fixed good part, shifted root/bad part), while both
keys have exactly the same infinity suffix.

Natural column names avoid pretending that a deleted terminal source
column has a surviving shifted `Fin` index. Arbitrary monotone labels of
natural columns are supported as well as the literal natural-key result.
-/

namespace OmegaY.Expansion

universe u

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start ambient result : Mountain} {references : List Ref}

theorem keyNode_extend {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    (preserved : PreservesColumns ambient result) :
    (copy.extend preserved).keyNode = preserved.mapNode copy.keyNode := by
  apply Executable.ref_injective
  exact (copy.extend preserved).keyNode_ref.trans
    (copy.keyNode_ref.symm.trans (preserved.mapNode_ref copy.keyNode).symm)

/-- No target father correspondence or copied degree is supplied. The
actual target edge and its effective lower determine both. -/
theorem stored_edge_degree
    (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (copy : EffectiveCopyOccurrence p block start references source.lower result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hLower : Frame.ref edge.lower = copy.outputRef) : edge.degree = source.degree := by
  have hNormal := build_normal_of_success p.reduced_build
  have hParent := (hNormal.rawParent_eq_P source.lower_real).symm.trans source.parent_eq
  have hSame : edge.lower = copy.keyNode := Executable.ref_injective _
    (hLower.trans copy.keyNode_ref.symm)
  have hActualParent : (Frame.ofMountain result).rawParent copy.keyNode = some edge.parent := by
    rw [← hSame]
    exact edge.parent_eq
  have hJump := copy.raw_parent_jump hLast
    (expandDiagram_raw_geometry (build_success_legal p.initial_build) hRun).rawRowGeometry hParent hActualParent
  simpa only [RealStoredEdge.degree, hSame] using hJump

end EffectiveCopyOccurrence

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient result : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)

include s history hLast hStartRun

/-- Complete-column retention transports the computed root bound into
any real final expansion which contains the recorded copied prefix. -/
theorem DynamicBlockState.preserved_all_scale_root_bound
    {source : (Frame.ofMountain p.reduced).Node}
    (hReal : Real source) (hBefore : source.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    (preserved : PreservesColumns ambient result) {totalCopies : Nat}
    (hRun : expandDiagram (front ++ [last]) totalCopies = .ok result) (k : Nat) :
    (scaleRoot (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered
      k (copy.extend preserved).keyNode).1.val ≤
      copiedKeyColumn p.root.column (block * (p.reduced.size - 1 - p.root.column))
        (scaleRoot p.reduced_valid.toOrdered k source).1.val := by
  rw [copy.keyNode_extend preserved, preserved.mapNode_scaleRoot s.ambient_valid.toOrdered,
    preserved.mapNode_column]
  exact s.recorded_all_scale_root_bound history hLast hStartRun hReal hBefore copy k

/-- Arbitrary monotone interpretations of actual column names preserve
the key bound. Every root/good crossing is discharged internally. -/
theorem DynamicBlockState.preserved_effective_edge_key_le
    (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (hBefore : source.lower.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source.lower ambient)
    (preserved : PreservesColumns ambient result) {totalCopies : Nat}
    (hRun : expandDiagram (front ++ [last]) totalCopies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hLower : Frame.ref edge.lower = (copy.extend preserved).outputRef)
    (D : Nat) {Label : Type u} [LinearOrder Label]
    (labels : Nat → Label) (hLabels : Monotone labels) :
    Keys.eval (edge.keyTemplate
        (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered D)
        (fun column => labels column.val) ≤
      Keys.eval (source.keyTemplate p.reduced_valid.toOrdered D)
        (fun column => labels (copiedKeyColumn p.root.column
          (block * (p.reduced.size - 1 - p.root.column)) column.val)) := by
  have hDegree := (copy.extend preserved).stored_edge_degree source edge hLast hRun hLower
  have hSame : edge.lower = (copy.extend preserved).keyNode := Executable.ref_injective _
    (hLower.trans (copy.extend preserved).keyNode_ref.symm)
  apply Pi.toLex_monotone
  intro i
  by_cases hi : source.degree ≤ D - i.val
  · have hTarget : edge.degree ≤ D - i.val := by rw [hDegree]; exact hi
    simp only [source.keyTemplate_lower_root p.reduced_valid.toOrdered i hi,
      edge.keyTemplate_lower_root
        (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered i hTarget]
    apply WithTop.coe_le_coe.mpr
    apply hLabels
    rw [hSame]
    exact s.preserved_all_scale_root_bound history hLast hStartRun source.lower_real hBefore copy preserved hRun _
  · have hTarget : ¬ edge.degree ≤ D - i.val := by rw [hDegree]; exact hi
    simp only [RealStoredEdge.keyTemplate, if_neg hi, if_neg hTarget, le_refl]

/-- Literal combinatorial keys under the actual fixed/shifted column map. -/
theorem DynamicBlockState.preserved_effective_edge_nat_key_le
    (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (hBefore : source.lower.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source.lower ambient)
    (preserved : PreservesColumns ambient result) {totalCopies : Nat}
    (hRun : expandDiagram (front ++ [last]) totalCopies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hLower : Frame.ref edge.lower = (copy.extend preserved).outputRef) (D : Nat) :
    Keys.eval (edge.keyTemplate
        (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered D)
        (fun column => column.val) ≤
      Keys.eval (source.keyTemplate p.reduced_valid.toOrdered D)
        (fun column => copiedKeyColumn p.root.column
          (block * (p.reduced.size - 1 - p.root.column)) column.val) :=
  s.preserved_effective_edge_key_le history hLast hStartRun source hBefore copy preserved hRun edge hLower D
    id (fun _ _ h => h)

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stored_edge_degree
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_all_scale_root_bound
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_effective_edge_key_le
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_effective_edge_nat_key_le
