/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicActiveParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DynamicParentInterval
import OmegaY.Expansion.PreparedActiveParent
import OmegaY.Expansion.ActualRootInterval

/-!
# Active copied-parent selection in the actual dynamic mountain

Only the source parent must be in the root interval. The child may already
be above its cap. The actual copy history supplies the earlier parent
column and the precise reference query used when that column was copied.
All results concern actual strict-below selection and cell reads; copied
normality is neither assumed nor concluded.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A strict-above-root active parent is selected in the current dynamic
mountain, without a child-interval premise or any parent-upper premise.
The required earlier-copy certificates are recovered from actual history. -/
theorem DynamicBlockState.below_active_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient)
    (hLast : 1 < last)
    {root child parent childUpper : (Frame.ofMountain p.reduced).Node}
    {degree : Nat} (hRootReal : Frame.Real root) (hDegree : 0 < degree)
    (hRootColumn : root.1.val = p.root.column) (hRootIndex : root.2.val ≤ p.root.index)
    (hRootBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height root) degree ≤
        (Frame.ofMountain p.reduced).height upper)
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hParentInside : Frame.RootInterval (Frame.ofMountain p.reduced) root
      (Row.bump ((Frame.ofMountain p.reduced).height root) degree) parent)
    (hParentAbove : (Frame.ofMountain p.reduced).height root <
      (Frame.ofMountain p.reduced).height parent)
    (hChildColumn : child.1.val = next)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    {target : Row}
    (hTarget : referenceAt start references ((Frame.ofMountain p.reduced).height root) = .ok target)
    (hTargetCap : target < Row.bump ((Frame.ofMountain p.reduced).height root) degree) :
    ∃ (index : Nat) (actualParent : Cell),
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        (Row.lift ((Frame.ofMountain p.reduced).height root) target
          ((Frame.ofMountain p.reduced).height childUpper)) =
        .ok ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ ∧
      Canonical.cellAt ambient
        ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift ((Frame.ofMountain p.reduced).height root) target
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hp : F.P child = some parent :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hRight : p.root.column < parent.1.val := by
    rw [← hRootColumn]
    exact hParentInside.column_lt_of_height_lt hNormal.toOrdered hRootBarrier hParentAbove
  have hBeforeNext : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt hNormal.toOrdered hp
  obtain ⟨before, column, d, hRun, hPreserve, hSource, _, hParentPower,
    hParentLow, hQueries, _⟩ := s.prior_column_data history hLast hRight hBeforeNext
  have hCurrentTarget : referenceAt ambient references (F.height root) = .ok target :=
    (s.referenceAt_preserved (F.height root)).trans hTarget
  have hBeforeTarget : referenceAt before references (F.height root) = .ok target :=
    (hQueries (F.height root)).trans hCurrentTarget
  obtain ⟨index, actualParent, hBelow, hCell, hRow⟩ :=
    d.prepared_below_active_parent hSource hRootReal hRootColumn hRootIndex
      hParentInside rfl hRight hBeforeTarget hRootBarrier hParent hChildUpper
      hParentPower hParentLow hRun hDegree hParentAbove hTargetCap
  have hCurrentBelow : below ambient before.size
      (Row.lift (F.height root) target (F.height childUpper)) = .ok ⟨before.size, index⟩ :=
    (hPreserve.below (by simp) _).trans hBelow
  obtain ⟨actualNodes, hNodes, hRead⟩ := cellAt_ok_iff.mp hCell
  have hCurrentCell : Canonical.cellAt ambient ⟨before.size, index⟩ = .ok actualParent :=
    cellAt_ok_iff.mpr ⟨actualNodes, hPreserve.column_read hNodes, hRead⟩
  rw [← d.destination] at hCurrentBelow hCurrentCell
  exact ⟨index, actualParent, hCurrentBelow, hCurrentCell, hRow⟩

/-- An actual reference-interval certificate supplies all root and target
controls. Positive interval degree follows from the existence of the
strictly higher interior parent, even if the target itself did not rise.
The source child need not lie inside the certificate's interval. -/
theorem DynamicBlockState.actual_active_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceIndex : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references sourceIndex sourceRow)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hParentInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) parent)
    (hParentAbove : sourceRow < (Frame.ofMountain p.reduced).height parent)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildUpper : (Frame.ofMountain p.reduced).upper child = some childUpper) :
    ∃ (index : Nat) (actualParent : Cell),
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height childUpper)) =
        .ok ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ ∧
      Canonical.cellAt ambient
        ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ = .ok actualParent ∧
      actualParent.row = Row.lift sourceRow a.target.row
        ((Frame.ofMountain p.reduced).height parent) := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hRootIndex : a.root.2.val ≤ p.root.index :=
    (congrArg Ref.index a.root_ref).trans_le a.root_prefix
  have hRootRow : F.height a.root = sourceRow := a.root_row
  have hInside : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) parent := by
    simpa only [hRootRow] using hParentInside
  have hAbove : F.height a.root < F.height parent := by
    simpa only [hRootRow] using hParentAbove
  have hDegree : 0 < a.degree := by
    by_contra hn
    have hZero : a.degree = 0 := by omega
    have hBelow : F.height parent < Row.bump (F.height a.root) 0 := by
      simpa only [hZero] using hInside.2.2
    have hJump : Row.jump (F.height a.root) (F.height parent) = 0 :=
      Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hInside.2.1 hBelow)
    exact (ne_of_lt hAbove) (Row.jump_eq_zero.mp hJump)
  have hBarrier : ∀ upper, F.upper a.root = some upper →
      Row.bump (F.height a.root) a.degree ≤ F.height upper := by
    simpa only [hRootRow] using a.root_upper_barrier
  have hTarget : referenceAt start references (F.height a.root) = .ok a.target.row := by
    simpa only [hRootRow] using a.start_query
  have hTargetCap : a.target.row < Row.bump (F.height a.root) a.degree := by
    simpa only [hRootRow] using a.target_below
  have hExecutable := (Executable.findParent_ref_iff hNormal.toOrdered child parent).mpr hParent
  obtain ⟨index, actualParent, hBelow, hRead, hRow⟩ :=
    s.below_active_parent history hLast a.root_real hDegree hRootColumn hRootIndex hBarrier
      hExecutable hInside hAbove hChildColumn hChildUpper hTarget hTargetCap
  exact ⟨index, actualParent, by simpa only [a.root_row] using hBelow, hRead,
    by simpa only [a.root_row] using hRow⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.below_active_parent
#print axioms OmegaY.Expansion.DynamicBlockState.actual_active_parent
