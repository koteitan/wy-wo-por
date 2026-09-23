/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualScaleParentTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.MountainKeys
import OmegaY.Expansion.ActualAllUpperLift
import OmegaY.Expansion.ActualEffectivePaths
import OmegaY.Expansion.HistoryRawInvariants

/-!
# Actual scale-parent transport inside a copied block

The jump exponent is recovered from the actual immediate upper, whose row
is the source upper's contour lift. Together with the independently proved
raw B equation, this forces the effective parent edge to have exactly the
old jump. There is no target same-block or target-root comparison premise,
and no numerical normality of the copied mountain is used.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- A typed node obtained from this occurrence's actual successful read. -/
noncomputable def keyNode : (Frame.ofMountain result).Node :=
  Classical.choose (Canonical.frame_node_of_cellAt copy.output_read)

theorem keyNode_ref : Frame.ref copy.keyNode = copy.outputRef :=
  (Classical.choose_spec (Canonical.frame_node_of_cellAt copy.output_read)).1

theorem keyNode_cell : (Frame.ofMountain result).cell copy.keyNode = copy.read.outputCell :=
  (Classical.choose_spec (Canonical.frame_node_of_cellAt copy.output_read)).2

theorem keyNode_height : (Frame.ofMountain result).height copy.keyNode = copy.read.outputCell.row :=
  congrArg Cell.row copy.keyNode_cell

theorem keyNode_real (hReal : Real source) : Real copy.keyNode := by
  have hi := congrArg Ref.index copy.keyNode_ref
  change copy.keyNode.2.val = copy.read.outputIndex at hi
  simpa only [Real, hi] using copy.read.output_real hReal

theorem keyNode_column : copy.keyNode.1.val =
    source.1.val + block * (p.reduced.size - 1 - p.root.column) :=
  (congrArg Ref.column copy.keyNode_ref).trans copy.source_column

theorem keyNode_eq (other : EffectiveCopyOccurrence p block start references source result) :
    copy.keyNode = other.keyNode :=
  Executable.ref_injective _ (copy.keyNode_ref.trans ((copy.unique other).1.trans other.keyNode_ref.symm))

/-- The executable lifted upper and raw B recover the source degree.
The stored parent here may be any genuine target node; in the actual
transport theorem below it is supplied by the recorded copied edge. -/
theorem raw_parent_jump (hLast : 1 < last) (hRaw : (Frame.ofMountain result).RawRowGeometry)
    {sourceParent : (Frame.ofMountain p.reduced).Node}
    (hSourceParent : (Frame.ofMountain p.reduced).P source = some sourceParent)
    {targetParent : (Frame.ofMountain result).Node}
    (hParent : (Frame.ofMountain result).rawParent copy.keyNode = some targetParent) :
    Row.jump ((Frame.ofMountain result).height copy.keyNode)
        ((Frame.ofMountain result).height targetParent) =
      Row.jump ((Frame.ofMountain p.reduced).height source)
        ((Frame.ofMountain p.reduced).height sourceParent) := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  let md := copy.data.marker_data copy.read.marker copy.read.marker_mem
  have hNormal := build_normal_of_success p.reduced_build
  have hReal : Real source := real_of_value_pos hNormal.toOrdered
    ((P_value hNormal.toOrdered hSourceParent).1.trans (P_value hNormal.toOrdered hSourceParent).2)
  obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hSourceParent
  obtain ⟨upperCell, hUpperRead, hUpperRow⟩ := copy.upper_lift_read_all hLast hReal hSourceUpper
  obtain ⟨targetUpper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hUpper : G.upper copy.keyNode = some targetUpper := Frame.upper_of_refs copy.keyNode_ref hUpperRef
  obtain ⟨actualParent, hActualParent, _, _, hB⟩ := hRaw copy.keyNode targetUpper (copy.keyNode_real hReal) hUpper
  have he : actualParent = targetParent := Option.some.inj (hActualParent.symm.trans hParent)
  subst actualParent
  have hOldB : F.height sourceUpper = Row.B (F.height source) (F.height sourceParent) :=
    (Frame.aboveHeight_of_upper hSourceUpper).symm.trans (hNormal.above_row hSourceParent)
  have hLower : G.height copy.keyNode = Row.lift md.current.row md.targetCell.row (F.height source) :=
    copy.keyNode_height.trans copy.read.output_row
  have hLiftUpper : G.height targetUpper = Row.lift md.current.row md.targetCell.row (F.height sourceUpper) :=
    (congrArg Cell.row hUpperCell).trans hUpperRow
  have hRootUpper : md.current.row ≤ F.height sourceUpper :=
    copy.read.source_lower.trans ((Row.lt_B _ _).trans_eq hOldB.symm).le
  have hJump : Row.jump (Row.lift md.current.row md.targetCell.row (F.height source))
      (Row.lift md.current.row md.targetCell.row (F.height sourceUpper)) =
      Row.jump (F.height source) (F.height sourceUpper) :=
    Row.jump_lift copy.read.source_lower hRootUpper
  rw [← hLower, ← hLiftUpper, hB, hOldB] at hJump
  simp only [G, F, Row.B, Row.jump_bump] at hJump
  exact Nat.add_right_cancel hJump

end EffectiveCopyOccurrence

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)

include s history hLast hStartRun

/-- Every ordinary effective edge in the actual recorded block preserves
its full highest-difference exponent, including physical marker seams. -/
theorem DynamicBlockState.recorded_parent_jump
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient) :
    Row.jump ((Frame.ofMountain ambient).height childCopy.keyNode)
        ((Frame.ofMountain ambient).height parentCopy.keyNode) =
      Row.jump ((Frame.ofMountain p.reduced).height child)
        ((Frame.ofMountain p.reduced).height parent) :=
  childCopy.raw_parent_jump hLast (s.mountainRawGeometry_of_start_run history hLast hStartRun).rawRowGeometry
    hParent ((s.recorded_effective_parent history hLast hParent hRight hBefore childCopy parentCopy).rawParent
      childCopy.keyNode_ref parentCopy.keyNode_ref)

/-- A retained source edge really is retained in the copied scale forest. -/
theorem DynamicBlockState.recorded_scale_parent
    {child parent : (Frame.ofMountain p.reduced).Node} {k : Nat}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hScale : Row.jump ((Frame.ofMountain p.reduced).height child)
      ((Frame.ofMountain p.reduced).height parent) ≤ k)
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient) :
    (Frame.ofMountain ambient).scaleParent k childCopy.keyNode = some parentCopy.keyNode := by
  apply scaleParent_some_iff.mpr
  exact ⟨(s.recorded_effective_parent history hLast hParent hRight hBefore childCopy parentCopy).rawParent
      childCopy.keyNode_ref parentCopy.keyNode_ref,
    (s.recorded_parent_jump history hLast hStartRun hParent hRight hBefore childCopy parentCopy).le.trans hScale⟩

/-- Convexity is checked in the source: a same-block ancestor path maps
to a path all of whose actual copied edges belong to the same scale forest.
Neither a target path nor target row comparison is a premise. -/
theorem DynamicBlockState.recorded_scale_path
    {child ancestor : (Frame.ofMountain p.reduced).Node} {k : Nat}
    (path : ParentPath (Frame.ofMountain p.reduced) child ancestor)
    (hBlock : Row.jump ((Frame.ofMountain p.reduced).height child)
      ((Frame.ofMountain p.reduced).height ancestor) ≤ k)
    (hRight : p.root.column < ancestor.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (ancestorCopy : EffectiveCopyOccurrence p block start references ancestor ambient) :
    Relation.ReflTransGen (fun u v => (Frame.ofMountain ambient).scaleParent k u = some v)
      childCopy.keyNode ancestorCopy.keyNode := by
  have hNormal := build_normal_of_success p.reduced_build
  induction path with
  | refl source =>
    rw [childCopy.keyNode_eq ancestorCopy]
  | @cons child middle ancestor hParent tail ih =>
    have hMiddleRight : p.root.column < middle.1.val := hRight.trans_le (tail.column_le hNormal.toOrdered)
    have hMiddleBefore : middle.1.val < next := (P_column_lt hNormal.toOrdered hParent).trans hBefore
    obtain ⟨middleCopy⟩ := s.prior_effective_occurrence history hLast hMiddleRight hMiddleBefore
    have hBetween := Row.jump_le_between (tail.height_le hNormal.toOrdered)
      (P_height_le hNormal.toOrdered hParent) (by simpa only [Row.jump_comm] using hBlock)
    have hFirst : Row.jump ((Frame.ofMountain p.reduced).height child)
        ((Frame.ofMountain p.reduced).height middle) ≤ k := by
      simpa only [Row.jump_comm] using hBetween.2
    have hRest : Row.jump ((Frame.ofMountain p.reduced).height middle)
        ((Frame.ofMountain p.reduced).height ancestor) ≤ k := by
      simpa only [Row.jump_comm] using hBetween.1
    exact (Relation.ReflTransGen.single
      (r := fun u v => (Frame.ofMountain ambient).scaleParent k u = some v)
      (s.recorded_scale_parent history hLast hStartRun
      hParent hFirst hMiddleRight hBefore childCopy middleCopy)).trans
        (ih hRest hRight hMiddleBefore middleCopy ancestorCopy)

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.raw_parent_jump
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_parent_jump
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_scale_parent
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_scale_path
