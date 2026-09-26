/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TrivialSearchRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FinalSourceRecognition
import OmegaY.Canonical.Values

/-!
# Numerical recognition for the program's actual deletion branch

The executable condition is empty input, final value one, or zero copies.
Its result is the original canonical mountain with its last column removed.
Raw edges are mapped back to that original mountain, whose numerical
normality is proved by construction; search locality reflects the answer
back into the returned prefix. No normality of the returned graph is an
input. A parentless final bottom node is reduced to final value one.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

/-- Removing the final column of an actually built mountain preserves
numerical recognition on every surviving real node. -/
theorem build_pop_rawParent_eq_P {input : List Nat} {initial : Mountain}
    (hBuild : Canonical.build input = .ok initial)
    {node : (Frame.ofMountain initial.pop).Node} (hReal : Real node) :
    (Frame.ofMountain initial.pop).rawParent node = (Frame.ofMountain initial.pop).P node := by
  have hValid := build_valid_of_success hBuild
  have hNormal := build_normal_of_success hBuild
  obtain ⟨built, hBuilt, _, hTops⟩ := build_total (build_success_legal hBuild)
  have he : built = initial := Except.ok.inj (hBuilt.symm.trans hBuild)
  subst built
  have hPreserved := PreservesColumns.pop_prefix initial
  apply ((build_mountain_sums hBuild).pop hValid).rawParent_eq_P_of_recognition
    hValid.pop (MountainTops.pop hTops) hReal
  intro parent hRaw
  have hMappedRaw := hPreserved.mapNode_rawParent hRaw
  have hMappedP := (hNormal.rawParent_eq_P (hPreserved.mapNode_real hReal)).symm.trans hMappedRaw
  apply (Executable.findParent_ref_iff hValid.pop.toOrdered node parent).mp
  rw [← hPreserved.findParent node.1.isLt]
  have hSearch := (Executable.findParent_ref_iff hNormal.toOrdered _ _).mpr hMappedP
  simpa only [hPreserved.mapNode_ref] using hSearch

/-- The condition is exactly the condition in `expandDiagram`, including
the zero-copy branch's original (not decremented) canonical input. -/
theorem expandDiagram_trivial_rawParent_eq_P {input : List Nat} (hLegal : Legal input)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram input copies = .ok result)
    (hTrivial : input.isEmpty ∨ input.getLast? = some 1 ∨ copies = 0)
    {node : (Frame.ofMountain result).Node} (hReal : Real node) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  obtain ⟨initial, hBuild, _, _⟩ := build_total hLegal
  have hActual : expandDiagram input copies = .ok initial.pop := by
    simp only [List.isEmpty_iff] at hTrivial
    simp [expandDiagram, hBuild, Except.mapError, hTrivial]
  have he : initial.pop = result := Except.ok.inj (hActual.symm.trans hRun)
  subst result
  exact build_pop_rawParent_eq_P hBuild hReal

/-- All real nodes in an actual trivial return satisfy the reconstruction
search certificate, without any left-column or higher-node assumption. -/
theorem expandDiagram_trivial_rawParentSearch {input : List Nat} (hLegal : Legal input)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram input copies = .ok result)
    (hTrivial : input.isEmpty ∨ input.getLast? = some 1 ∨ copies = 0) :
    (Frame.ofMountain result).RawParentSearch := by
  intro node parent hReal hRaw
  exact (expandDiagram_trivial_rawParent_eq_P hLegal hRun hTrivial hReal).symm.trans hRaw

/-- On the legal canonical domain, a parentless last sequence entry means
its actual bottom value is one. The source node is explicitly index one,
not the value-one top of a nonterminal column. -/
theorem last_bottom_value_one_of_parent_none
    {front : List Nat} {last : Nat} {initial : Mountain}
    (hBuild : Canonical.build (front ++ [last]) = .ok initial)
    {lastBottom : (Frame.ofMountain initial).Node}
    (hRef : Frame.ref lastBottom = ⟨front.length, 1⟩)
    (hParent : (Frame.ofMountain initial).P lastBottom = none) : last = 1 := by
  have hNormal := build_normal_of_success hBuild
  have hIndex := congrArg Ref.index hRef
  have hReal : Real lastBottom := by change 0 < lastBottom.2.val; change lastBottom.2.val = 1 at hIndex; omega
  have hPositive := hNormal.real_positive lastBottom hReal
  have hOne : (Frame.ofMountain initial).value lastBottom = 1 := by
    by_contra hNot
    obtain ⟨upper, hUpper⟩ := hNormal.upper_exists lastBottom hReal (by omega)
    obtain ⟨parent, hP, _⟩ := hNormal.upper_step lastBottom upper hReal hUpper
    rw [hParent] at hP
    cases hP
  obtain ⟨column, hColumn, hValue⟩ := build_bottom_at hBuild
    (show (front ++ [last])[front.length]? = some last by simp)
  have hCellRead := Canonical.cellAt_of_frame_node initial lastBottom
  rw [hRef] at hCellRead
  obtain ⟨nodes, hNodes, hBottom⟩ := cellAt_ok_iff.mp hCellRead
  have he : nodes = column := Option.some.inj (hNodes.symm.trans hColumn)
  subst nodes
  have hBottomValue : (Frame.ofMountain initial).value lastBottom = last := by
    change ((Frame.ofMountain initial).cell lastBottom).value = last
    simpa only [Canonical.bottomValue, hBottom, Option.map_some, Option.some.injEq] using hValue
  exact hBottomValue.symm.trans hOne

/-- The parentless-final-entry formulation is discharged through the
program's actual terminal-one condition, rather than adding a new branch. -/
theorem expandDiagram_parentless_last_rawParentSearch
    {front : List Nat} {last : Nat} {initial : Mountain}
    (hBuild : Canonical.build (front ++ [last]) = .ok initial)
    {lastBottom : (Frame.ofMountain initial).Node}
    (hRef : Frame.ref lastBottom = ⟨front.length, 1⟩)
    (hParent : (Frame.ofMountain initial).P lastBottom = none)
    {copies : Nat} {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    (Frame.ofMountain result).RawParentSearch := by
  have hOne := last_bottom_value_one_of_parent_none hBuild hRef hParent
  exact expandDiagram_trivial_rawParentSearch (build_success_legal hBuild) hRun
    (Or.inr (Or.inl (by simp [hOne])))

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_pop_rawParent_eq_P
#print axioms OmegaY.Expansion.expandDiagram_trivial_rawParent_eq_P
#print axioms OmegaY.Expansion.expandDiagram_trivial_rawParentSearch
#print axioms OmegaY.Expansion.last_bottom_value_one_of_parent_none
#print axioms OmegaY.Expansion.expandDiagram_parentless_last_rawParentSearch
