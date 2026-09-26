/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinalSourceRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FinalHighEventSampling
import OmegaY.Expansion.PreservedSearchNodes
import OmegaY.Expansion.RawSearchInduction

/-!
# Numerical parent recognition on the actual retained source prefix

Positive-copy expansion retains the entire reduced source even after the
final pop. Complete-cell preservation and search locality prove numerical
recognition on every real node in that prefix, with no induction hypothesis
about copied columns. New columns still require the separate copy argument.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem PreservesColumns.build_rawParent_eq_P
    {input : List Nat} {source result : Mountain}
    (h : PreservesColumns source result) (hBuild : Canonical.build input = .ok source)
    (hValid : MountainValid result) (hSums : MountainSums result) (hTops : MountainTops result)
    {node : (Frame.ofMountain result).Node} (hColumn : node.1.val < source.size) (hReal : Real node) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  have hSourceRead : Canonical.cellAt source (Frame.ref node) = .ok ((Frame.ofMountain result).cell node) :=
    (h.cellAt hColumn).symm.trans (Canonical.cellAt_of_frame_node result node)
  obtain ⟨original, hOriginalRef, _⟩ := Canonical.frame_node_of_cellAt hSourceRead
  have hMapped : h.mapNode original = node := Executable.ref_injective _
    ((h.mapNode_ref original).trans hOriginalRef)
  have hOriginalReal : Real original := by
    have hIndex := congrArg Ref.index hOriginalRef
    change original.2.val = node.2.val at hIndex
    change 0 < original.2.val
    rw [hIndex]
    exact hReal
  have hNormal := build_normal_of_success hBuild
  cases hP : (Frame.ofMountain source).P original with
  | some parent =>
      have hSourceRaw := (hNormal.rawParent_eq_P hOriginalReal).trans hP
      have hRaw := h.mapNode_rawParent hSourceRaw
      have hNumerical := h.mapNode_P hNormal.toOrdered hValid.toOrdered hP
      rw [hMapped] at hRaw hNumerical
      exact hRaw.trans hNumerical.symm
  | none =>
      have hOne : (Frame.ofMountain source).value original = 1 := by
        have hPositive := hNormal.real_positive original hOriginalReal
        by_contra hNot
        obtain ⟨upper, hUpper⟩ := hNormal.upper_exists original hOriginalReal (by omega)
        obtain ⟨parent, hParent, _⟩ := hNormal.upper_step original upper hOriginalReal hUpper
        rw [hP] at hParent
        cases hParent
      have hNodeOne : (Frame.ofMountain result).value node = 1 := by
        rw [← hMapped]
        exact (congrArg Cell.value (h.mapNode_cell original)).trans hOne
      have hRawNone := (hSums.rawParent_none_iff_value_one hValid hTops hReal).mpr hNodeOne
      have hPNone : (Frame.ofMountain result).P node = none := by
        cases hFound : (Frame.ofMountain result).P node with
        | none => rfl
        | some parent =>
            obtain ⟨hPositive, hSmall⟩ := Frame.P_value hValid.toOrdered hFound
            rw [hNodeOne] at hSmall
            omega
      exact hRawNone.trans hPNone.symm

theorem Preparation.expandDiagram_source_rawParent_eq_P
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {node : (Frame.ofMountain result).Node} (hColumn : node.1.val < p.reduced.size) (hReal : Real node) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  have hLegal := build_success_legal p.initial_build
  have hEquations := OmegaY.Expansion.expandDiagram_equations hLegal hRun
  exact (p.expandDiagram_reduced_preserved hLast hCopies hRun).build_rawParent_eq_P p.reduced_build
    (expandDiagram_valid_of_success hLegal hRun) hEquations.1 hEquations.2 hColumn hReal

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.build_rawParent_eq_P
#print axioms OmegaY.Expansion.Preparation.expandDiagram_source_rawParent_eq_P
