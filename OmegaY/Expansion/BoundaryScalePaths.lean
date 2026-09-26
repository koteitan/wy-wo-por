/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BoundaryScalePaths.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualScaleRootTransport
import OmegaY.Expansion.ActualLowHighRootCorrection
import OmegaY.Expansion.PreservedMountainKeys

/-!
# Scale forests along real stored boundary paths

Real positive backfill keeps every vertex of a stored path real. The raw
B law makes its heights nonincreasing. Consequently a path whose actual
endpoints agree at and above scale k has every edge in that scale forest.
This lemma is used below with bounds derived from real root selectors.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem raw_height_le {mountain : Mountain}
    (hRaw : (Frame.ofMountain mountain).RawRowGeometry)
    {u parent : (Frame.ofMountain mountain).Node} (hReal : Real u)
    (hParent : (Frame.ofMountain mountain).rawParent u = some parent) :
    (Frame.ofMountain mountain).height parent ≤ (Frame.ofMountain mountain).height u := by
  obtain ⟨upper, hUpper, _⟩ := Frame.rawParent_spec hParent
  obtain ⟨p, hp, _, hRow, _⟩ := hRaw u upper hReal hUpper
  have he : p = parent := Option.some.inj (hp.symm.trans hParent)
  exact he ▸ hRow

theorem RawRefPath.height_le_of_sums {mountain : Mountain}
    (hValid : MountainValid mountain) (hSums : MountainSums mountain)
    (hRaw : (Frame.ofMountain mountain).RawRowGeometry)
    {child parent : Ref} (path : RawRefPath mountain child parent)
    {u p : (Frame.ofMountain mountain).Node}
    (hU : Frame.ref u = child) (hP : Frame.ref p = parent) (hReal : Real u) :
    (Frame.ofMountain mountain).height p ≤ (Frame.ofMountain mountain).height u := by
  induction path generalizing u with
  | refl ref =>
    have he : u = p := Executable.ref_injective _ (hU.trans hP.symm)
    exact he ▸ le_rfl
  | @cons child next parent edge tail ih =>
    have edgeRead := edge
    obtain ⟨_, _, _, _, _, _, hRead⟩ := edgeRead
    obtain ⟨q, hQRef, _⟩ := Canonical.frame_node_of_cellAt hRead
    have hParent := edge.rawParent hU hQRef
    have hQReal := (hSums.rawParent_value_lt hValid hReal hParent).1
    exact (ih hQRef hP hQReal).trans (raw_height_le hRaw hReal hParent)

theorem RawRefPath.scale_path {mountain : Mountain}
    (hValid : MountainValid mountain) (hSums : MountainSums mountain)
    (hRaw : (Frame.ofMountain mountain).RawRowGeometry)
    {child parent : Ref} (path : RawRefPath mountain child parent)
    {u p : (Frame.ofMountain mountain).Node} {k : Nat}
    (hU : Frame.ref u = child) (hP : Frame.ref p = parent) (hReal : Real u)
    (hBlock : Row.jump ((Frame.ofMountain mountain).height u)
      ((Frame.ofMountain mountain).height p) ≤ k) :
    Relation.ReflTransGen (fun a b => (Frame.ofMountain mountain).scaleParent k a = some b) u p := by
  induction path generalizing u with
  | refl ref =>
    have he : u = p := Executable.ref_injective _ (hU.trans hP.symm)
    rw [he]
  | @cons child next parent edge tail ih =>
    have edgeRead := edge
    obtain ⟨_, _, _, _, _, _, hRead⟩ := edgeRead
    obtain ⟨q, hQRef, _⟩ := Canonical.frame_node_of_cellAt hRead
    have hParent := edge.rawParent hU hQRef
    have hQReal := (hSums.rawParent_value_lt hValid hReal hParent).1
    have hBetween := Row.jump_le_between
      (tail.height_le_of_sums hValid hSums hRaw hQRef hP hQReal)
      (raw_height_le hRaw hReal hParent) (by simpa only [Row.jump_comm] using hBlock)
    have hUQ : Row.jump ((Frame.ofMountain mountain).height u)
        ((Frame.ofMountain mountain).height q) ≤ k := by simpa only [Row.jump_comm] using hBetween.2
    have hQP : Row.jump ((Frame.ofMountain mountain).height q)
        ((Frame.ofMountain mountain).height p) ≤ k := by simpa only [Row.jump_comm] using hBetween.1
    exact (Relation.ReflTransGen.single
      (r := fun a b => (Frame.ofMountain mountain).scaleParent k a = some b)
      (scaleParent_some_iff.mpr ⟨hParent, hUQ⟩)).trans (ih hQRef hP hQReal hQP)

namespace EffectiveRootEndpoint

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (endpoint : EffectiveRootEndpoint p start references source result)

theorem target_lower : (Frame.ofMountain p.reduced).height source ≤ endpoint.target.row := by
  cases endpoint with
  | selected copy => exact copy.target_lower
  | highTail copy => exact copy.target_row.symm.le

noncomputable def keyNode : (Frame.ofMountain result).Node :=
  Classical.choose (Canonical.frame_node_of_cellAt endpoint.result_read)

theorem keyNode_ref : Frame.ref endpoint.keyNode = endpoint.reference :=
  (Classical.choose_spec (Canonical.frame_node_of_cellAt endpoint.result_read)).1

theorem keyNode_cell : (Frame.ofMountain result).cell endpoint.keyNode = endpoint.target :=
  (Classical.choose_spec (Canonical.frame_node_of_cellAt endpoint.result_read)).2

theorem keyNode_height : (Frame.ofMountain result).height endpoint.keyNode = endpoint.target.row :=
  congrArg Cell.row endpoint.keyNode_cell

theorem keyNode_real (hValid : MountainValid result) (hReal : Real source) : Real endpoint.keyNode := by
  have hOne := (Frame.one_le_height p.reduced_valid.toOrdered hReal).trans endpoint.target_lower
  by_contra hn
  have hZero : endpoint.keyNode.2.val = 0 := by unfold Real at hn; omega
  have hi : endpoint.keyNode.2 = ⟨0, by have := endpoint.keyNode.2.isLt; omega⟩ := Fin.ext hZero
  have hPhantom := hValid.toOrdered.phantom endpoint.keyNode.1 (by have := endpoint.keyNode.2.isLt; omega)
  have hRowZero : (Frame.ofMountain result).height endpoint.keyNode = 0 := by
    change ((Frame.ofMountain result).cells endpoint.keyNode.1 endpoint.keyNode.2).row = 0
    rw [hi, hPhantom]
    rfl
  have hBad := hOne.trans_eq endpoint.keyNode_height.symm
  rw [hRowZero] at hBad
  exact (not_le_of_gt Row.zero_lt_one) hBad

end EffectiveRootEndpoint
end OmegaY.Expansion

#print axioms OmegaY.Expansion.RawRefPath.scale_path
#print axioms OmegaY.Expansion.EffectiveRootEndpoint.keyNode_real
