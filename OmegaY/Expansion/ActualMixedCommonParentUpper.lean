/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMixedCommonParentUpper.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentUpper
import OmegaY.Expansion.RecordedEffectiveEdges

/-!
# Common upper rows with an unchanged left-side blocker

Only the right-hand source receives an effective copy. A blocker in or left
of the root column keeps its original reference and entire source cell.
Its numerical parent is strictly left of the root, so the copied child's
actual immediate upper has its original source row, even across a marker
seam. Source overlap therefore supplies the shared actual upper height.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref} {result : Mountain}
  {u : (Frame.ofMountain p.reduced).Node}
  (uCopy : EffectiveCopyOccurrence p block start references u result)

/-- A source father in the fixed good part makes the actual immediate
copied upper retain its original row. Source nonmembership in the marker
bucket is proved here, including when the upper itself is a marker. -/
theorem fixed_parent_upper_read (hLast : 1 < last)
    {parent sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P u = some parent)
    (hFixed : parent.1.val < p.root.column)
    (hUpper : (Frame.ofMountain p.reduced).upper u = some sourceUpper) :
    ∃ upper, Canonical.cellAt result
        ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok upper ∧
      upper.row = (Frame.ofMountain p.reduced).height sourceUpper := by
  have hUnmarked : u.2.val ∉ (p.marked[u.1.val]?.getD []).map Ref.index := by
    intro hMem
    obtain ⟨marker, hm, hIndex⟩ := List.mem_map.mp hMem
    have hColumn := uCopy.data.marker_columns marker hm
    have hRef : marker = Frame.ref u := by
      cases marker
      simp only [Frame.ref, Ref.mk.injEq]
      exact ⟨hColumn, hIndex⟩
    exact p.fixed_parent_not_marked hParent hFixed (hRef ▸ hm)
  obtain ⟨upper, hRead, hRow⟩ := uCopy.upper_lift_read hLast hUnmarked hUpper
  have hFixedRow := uCopy.state.fixed_parent_marker_lift_upper hLast uCopy.data
    uCopy.read.marker_mem hParent rfl uCopy.read.marker_before hUpper hFixed
  exact ⟨upper, hRead, hRow.trans hFixedRow⟩

/-- The unchanged blocker and its source upper are actual complete-cell
reads. Their common source father is also the actual stored father of the
effective child. Neither a copied occurrence for the blocker nor a target
same-height or numerical-parent hypothesis is required. -/
theorem mixed_common_parent_upper_read (hLast : 1 < last)
    {z parent zUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hZLeft : z.1.val ≤ p.root.column)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some zUpper)
    (hOrder : (Frame.ofMountain p.reduced).height z ≤ (Frame.ofMountain p.reduced).height u)
    (hOverlap : (Frame.ofMountain p.reduced).height u < (Frame.ofMountain p.reduced).height zUpper) :
    ∃ upper,
      Canonical.cellAt result ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok upper ∧
      Canonical.cellAt result (Frame.ref z) = .ok ((Frame.ofMountain p.reduced).cell z) ∧
      Canonical.cellAt result (Frame.ref zUpper) = .ok ((Frame.ofMountain p.reduced).cell zUpper) ∧
      Canonical.cellAt result (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent) ∧
      upper.row = (Frame.ofMountain p.reduced).height zUpper ∧
      RawRefEdge result uCopy.outputRef (Frame.ref parent) ∧
      RawRefEdge result (Frame.ref z) (Frame.ref parent) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hFixed : parent.1.val < p.root.column :=
    (Frame.P_column_lt hNormal.toOrdered hZP).trans_le hZLeft
  obtain ⟨uUpper, hUUpper⟩ := hNormal.upper_of_parent hUP
  obtain ⟨upper, hRead, hRow⟩ := uCopy.fixed_parent_upper_read hLast hUP hFixed hUUpper
  have hRows := hNormal.common_parent_upper_rows hUP hZP hUUpper hZUpper hOrder hOverlap
  have hBase : PreservesColumns p.reduced result :=
    uCopy.state.base_ambient.trans ((PreservesColumns.push uCopy.before uCopy.column).trans uCopy.preserved)
  have hZRead := p.cell_read_preserved hBase (Canonical.cellAt_of_frame_node p.reduced z)
  have hZURead := p.cell_read_preserved hBase (Canonical.cellAt_of_frame_node p.reduced zUpper)
  have hPRead := p.cell_read_preserved hBase (Canonical.cellAt_of_frame_node p.reduced parent)
  obtain ⟨actualCopy, _, _, hUEdge, _⟩ :=
    uCopy.state.actual_fixed_parent hLast hUP rfl hFixed uCopy.read.copy_run
  have hCopyRef : actualCopy.outputRef = uCopy.outputRef :=
    ((actualCopy.extend uCopy.preserved).unique uCopy).1
  have hZReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hZP).1.trans (Frame.P_value hNormal.toOrdered hZP).2)
  have hZEdge := (RawRefEdge.of_rawParent ((hNormal.rawParent_eq_P hZReal).trans hZP)).preserve hBase
  exact ⟨upper, hRead, hZRead, hZURead, hPRead, hRow.trans hRows,
    by simpa only [hCopyRef] using hUEdge.preserve uCopy.preserved, hZEdge⟩

end EffectiveCopyOccurrence

/-- A comparison packet with one genuine effective occurrence and an
unchanged source blocker. The original references and full cells are kept
explicitly, rather than represented by fictitious copied occurrences. -/
structure MixedCommonParentPair {front : List Nat} {last : Nat}
    (p : Preparation front last) (block : Nat) (start : Mountain) (references : List Ref)
    (sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node)
    (result : Mountain) where
  uCopy : EffectiveCopyOccurrence p block start references sourceU result
  u : (Frame.ofMountain result).Node
  z : (Frame.ofMountain result).Node
  parent : (Frame.ofMountain result).Node
  uUpper : (Frame.ofMountain result).Node
  zUpper : (Frame.ofMountain result).Node
  u_ref : Frame.ref u = uCopy.outputRef
  z_ref : Frame.ref z = Frame.ref sourceZ
  parent_ref : Frame.ref parent = Frame.ref sourceParent
  z_upper_ref : Frame.ref zUpper = Frame.ref sourceZUpper
  u_cell : (Frame.ofMountain result).cell u = uCopy.read.outputCell
  z_cell : (Frame.ofMountain result).cell z = (Frame.ofMountain p.reduced).cell sourceZ
  parent_cell : (Frame.ofMountain result).cell parent = (Frame.ofMountain p.reduced).cell sourceParent
  z_upper_cell : (Frame.ofMountain result).cell zUpper = (Frame.ofMountain p.reduced).cell sourceZUpper
  u_real : Frame.Real u
  z_real : Frame.Real z
  z_column : z.1.val ≤ u.1.val
  u_parent : (Frame.ofMountain result).rawParent u = some parent
  z_parent : (Frame.ofMountain result).rawParent z = some parent
  u_upper : (Frame.ofMountain result).upper u = some uUpper
  z_upper : (Frame.ofMountain result).upper z = some zUpper
  upper_height : (Frame.ofMountain result).height uUpper = (Frame.ofMountain result).height zUpper

/-- Build the mixed comparison packet from an actual within-block history.
The overlap concerns source rows only; all target adjacency, common stored
father and upper-row coincidence are derived from executed copying. -/
theorem DynamicBlockState.recorded_mixed_common_parent_pair
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZP : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hURight : p.root.column < sourceU.1.val) (hUBefore : sourceU.1.val < next)
    (hZLeft : sourceZ.1.val ≤ p.root.column)
    (hZUpper : (Frame.ofMountain p.reduced).upper sourceZ = some sourceZUpper)
    (hOrder : (Frame.ofMountain p.reduced).height sourceZ ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hOverlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper) :
    Nonempty (MixedCommonParentPair p block start references
      sourceU sourceZ sourceParent sourceZUpper ambient) := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨uCopy⟩ := s.prior_effective_occurrence history hLast hURight hUBefore
  obtain ⟨upperCell, hUpperRead, hZRead, hZURead, hPRead, hRows, hUEdge, hZEdge⟩ :=
    uCopy.mixed_common_parent_upper_read hLast hUP hZP hZLeft hZUpper hOrder hOverlap
  obtain ⟨u, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt uCopy.output_read
  obtain ⟨z, hZRef, hZCell⟩ := Canonical.frame_node_of_cellAt hZRead
  obtain ⟨parent, hPRef, hPCell⟩ := Canonical.frame_node_of_cellAt hPRead
  obtain ⟨uUpper, hUURef, hUUCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  obtain ⟨zUpper, hZURef, hZUCell⟩ := Canonical.frame_node_of_cellAt hZURead
  have hSourceZURef : Frame.ref sourceZUpper =
      ⟨(Frame.ref sourceZ).column, (Frame.ref sourceZ).index + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hZUpper).1, (Frame.upper_spec hZUpper).2⟩
  have hUSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hUP).1.trans (Frame.P_value hNormal.toOrdered hUP).2)
  have hZSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hZP).1.trans (Frame.P_value hNormal.toOrdered hZP).2)
  refine ⟨{
    uCopy := uCopy, u := u, z := z, parent := parent, uUpper := uUpper, zUpper := zUpper
    u_ref := hURef, z_ref := hZRef, parent_ref := hPRef, z_upper_ref := hZURef
    u_cell := hUCell, z_cell := hZCell, parent_cell := hPCell, z_upper_cell := hZUCell
    u_real := ?_, z_real := ?_, z_column := ?_
    u_parent := hUEdge.rawParent hURef hPRef, z_parent := hZEdge.rawParent hZRef hPRef
    u_upper := Frame.upper_of_refs hURef hUURef
    z_upper := Frame.upper_of_refs hZRef (hZURef.trans hSourceZURef)
    upper_height := (congrArg Cell.row hUUCell).trans
      (hRows.trans (congrArg Cell.row hZUCell).symm) }⟩
  · have hi : u.2.val = uCopy.read.outputIndex := congrArg Ref.index hURef
    change 0 < u.2.val
    rw [hi]
    exact uCopy.read.output_real hUSourceReal
  · have hi : z.2.val = sourceZ.2.val := congrArg Ref.index hZRef
    change 0 < z.2.val
    rw [hi]
    exact hZSourceReal
  · have hUColumn := (congrArg Ref.column hURef).trans uCopy.source_column
    have hZColumn : z.1.val = sourceZ.1.val := congrArg Ref.column hZRef
    change u.1.val = _ at hUColumn
    omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.fixed_parent_upper_read
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.mixed_common_parent_upper_read
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_mixed_common_parent_pair
