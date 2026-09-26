/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFiniteEdgeKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveEdgeKeys

/-!
# Finite supported keys for actual effective copies

The copied source template is defined directly in the finite output width.
Only columns actually named by the template are mapped. Each such column
lies strictly before the effective lower, so its literal fixed/shifted
image is a genuine output column even when the unused terminal source
column would move beyond the final pop. No label extension is used.
-/

namespace OmegaY.Keys

universe u

def mapSupported {m n n' : Nat} (key : Template m n) (mu : Fin n → Nat)
    (hSupport : ∀ i column, key i = some column → mu column < n') : Template m n' :=
  fun i => match h : key i with
    | none => none
    | some column => some ⟨mu column, hSupport i column h⟩

theorem mapSupported_some {m n n' : Nat} (key : Template m n) (mu : Fin n → Nat)
    (hSupport : ∀ i column, key i = some column → mu column < n')
    {i : Fin m} {column : Fin n} (h : key i = some column) :
    mapSupported key mu hSupport i = some ⟨mu column, hSupport i column h⟩ := by
  unfold mapSupported
  split
  · rename_i hNone
    cases hNone.symm.trans h
  · rename_i other hOther
    have he : other = column := Option.some.inj (hOther.symm.trans h)
    subst other
    rfl

theorem mapSupported_none {m n n' : Nat} (key : Template m n) (mu : Fin n → Nat)
    (hSupport : ∀ i column, key i = some column → mu column < n')
    {i : Fin m} (h : key i = none) : mapSupported key mu hSupport i = none := by
  unfold mapSupported
  split
  · rfl
  · rename_i other hOther
    cases hOther.symm.trans h

/-- A total splice map need only agree on the actual finite support. -/
theorem mapSupported_eq_relabel {m n n' : Nat} (key : Template m n)
    (mu : Fin n → Nat)
    (hSupport : ∀ i column, key i = some column → mu column < n')
    (nu : Fin n → Fin n')
    (hAgree : ∀ i column, key i = some column → (nu column).val = mu column) :
    mapSupported key mu hSupport = relabel key nu := by
  funext i
  cases h : key i with
  | none => rw [mapSupported_none key mu hSupport h]; simp only [relabel, h, Option.map_none]
  | some column =>
    rw [mapSupported_some key mu hSupport h]
    simp only [relabel, h, Option.map_some]
    congr 1
    exact Fin.ext (hAgree i column h).symm

/-- Label matching is required only where the source template reads it. -/
theorem eval_mapSupported_of_labels {m n n' : Nat} (key : Template m n)
    (mu : Fin n → Nat)
    (hSupport : ∀ i column, key i = some column → mu column < n')
    {Label : Type u} [LinearOrder Label] (old : Fin n → Label) (fresh : Fin n' → Label)
    (hLabels : ∀ i column (h : key i = some column),
      fresh ⟨mu column, hSupport i column h⟩ = old column) :
    eval (mapSupported key mu hSupport) fresh = eval key old := by
  funext i
  simp only [eval, Pi.toLex_apply]
  cases h : key i with
  | none => simp only [mapSupported_none key mu hSupport h]
  | some column =>
    simp only [mapSupported_some key mu hSupport h, hLabels i column h]

end OmegaY.Keys

namespace OmegaY.Expansion

universe u

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}

/-- Every literal image before an actual effective source lower exists in
the output. The source's unused terminal column is never involved. -/
theorem mapped_column_lt {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    {column : Nat} (hColumn : column < source.1.val) :
    copiedKeyColumn p.root.column (block * (p.reduced.size - 1 - p.root.column)) column < result.size := by
  have hSource : ¬source.1.val < p.root.column := not_lt_of_ge copy.state.next_lower.le
  have hLower : copiedKeyColumn p.root.column
      (block * (p.reduced.size - 1 - p.root.column)) source.1.val = copy.keyNode.1.val := by
    rw [copiedKeyColumn, if_neg hSource, copy.keyNode_column]
  exact ((copiedKeyColumn_strictMono p.root.column _ hColumn).trans_eq hLower).trans
    copy.keyNode.1.isLt

theorem key_support_bound (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (copy : EffectiveCopyOccurrence p block start references source.lower result)
    {D : Nat} (i : Fin (D + 1)) (column : Fin (Frame.ofMountain p.reduced).width)
    (h : source.keyTemplate p.reduced_valid.toOrdered D i = some column) :
    copiedKeyColumn p.root.column (block * (p.reduced.size - 1 - p.root.column)) column.val < (Frame.ofMountain result).width :=
  copy.mapped_column_lt (source.keyTemplate_column_bound p.reduced_valid.toOrdered h).2

def mappedKey (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (copy : EffectiveCopyOccurrence p block start references source.lower result)
    (D : Nat) : Keys.Template (D + 1) (Frame.ofMountain result).width :=
  Keys.mapSupported (source.keyTemplate p.reduced_valid.toOrdered D)
    (fun column => copiedKeyColumn p.root.column
      (block * (p.reduced.size - 1 - p.root.column)) column.val)
    (copy.key_support_bound source)

theorem mappedKey_eq_relabel (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (copy : EffectiveCopyOccurrence p block start references source.lower result)
    (D : Nat) (mu : Fin (Frame.ofMountain p.reduced).width → Fin (Frame.ofMountain result).width)
    (hAgree : ∀ i column, source.keyTemplate p.reduced_valid.toOrdered D i = some column →
      (mu column).val = copiedKeyColumn p.root.column
        (block * (p.reduced.size - 1 - p.root.column)) column.val) :
    copy.mappedKey source D = Keys.relabel (source.keyTemplate p.reduced_valid.toOrdered D) mu :=
  Keys.mapSupported_eq_relabel _ _ _ mu hAgree

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

/-- The complete key inequality is already a finite combinatorial one;
the right-hand template has only actual output column indices. -/
theorem DynamicBlockState.preserved_effective_edge_template_le
    (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (hBefore : source.lower.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source.lower ambient)
    (preserved : PreservesColumns ambient result) {totalCopies : Nat}
    (hRun : expandDiagram (front ++ [last]) totalCopies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hLower : Frame.ref edge.lower = (copy.extend preserved).outputRef) (D : Nat) :
    Keys.templateKey (edge.keyTemplate
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered D) ≤
    Keys.templateKey ((copy.extend preserved).mappedKey source D) := by
  have hDegree := (copy.extend preserved).stored_edge_degree source edge hLast hRun hLower
  have hSame : edge.lower = (copy.extend preserved).keyNode := Executable.ref_injective _
    (hLower.trans (copy.extend preserved).keyNode_ref.symm)
  apply Pi.toLex_monotone
  intro i
  dsimp only
  by_cases hi : source.degree ≤ D - i.val
  · have hTarget : edge.degree ≤ D - i.val := by rw [hDegree]; exact hi
    have hSourceKey := source.keyTemplate_lower_root p.reduced_valid.toOrdered i hi
    erw [edge.keyTemplate_lower_root
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered i hTarget]
    dsimp only [EffectiveCopyOccurrence.mappedKey]
    erw [Keys.mapSupported_some _ _ _ hSourceKey]
    apply WithTop.coe_le_coe.mpr
    change (scaleRoot _ (D - i.val) edge.lower).1.val ≤ _
    rw [hSame]
    exact s.preserved_all_scale_root_bound history hLast hStartRun source.lower_real hBefore copy preserved hRun _
  · have hTarget : ¬edge.degree ≤ D - i.val := by rw [hDegree]; exact hi
    have hSourceKey : source.keyTemplate p.reduced_valid.toOrdered D i = none := by
      simp only [RealStoredEdge.keyTemplate, if_neg hi]
    dsimp only [EffectiveCopyOccurrence.mappedKey]
    erw [Keys.mapSupported_none _ _ _ hSourceKey]
    simp only [RealStoredEdge.keyTemplate, if_neg hTarget]
    exact le_rfl

theorem DynamicBlockState.preserved_effective_edge_finite_key_le
    (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (hBefore : source.lower.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source.lower ambient)
    (preserved : PreservesColumns ambient result) {totalCopies : Nat}
    (hRun : expandDiagram (front ++ [last]) totalCopies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hLower : Frame.ref edge.lower = (copy.extend preserved).outputRef)
    (D : Nat) {Label : Type u} [LinearOrder Label]
    (labels : Fin (Frame.ofMountain result).width → Label) (hLabels : StrictMono labels) :
    Keys.eval (edge.keyTemplate
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered D) labels ≤
    Keys.eval ((copy.extend preserved).mappedKey source D) labels :=
  Keys.eval_le_of_template_le _ _ labels hLabels
    (s.preserved_effective_edge_template_le history hLast hStartRun source hBefore copy preserved hRun edge hLower D)

/-- Finite splice labels need agree with the old labels only on roots
actually named by this source edge. No unused terminal label is read. -/
theorem DynamicBlockState.preserved_effective_edge_source_labels_le
    (source : RealStoredEdge (Frame.ofMountain p.reduced))
    (hBefore : source.lower.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source.lower ambient)
    (preserved : PreservesColumns ambient result) {totalCopies : Nat}
    (hRun : expandDiagram (front ++ [last]) totalCopies = .ok result)
    (edge : RealStoredEdge (Frame.ofMountain result))
    (hLower : Frame.ref edge.lower = (copy.extend preserved).outputRef)
    (D : Nat) {Label : Type u} [LinearOrder Label]
    (old : Fin (Frame.ofMountain p.reduced).width → Label)
    (fresh : Fin (Frame.ofMountain result).width → Label)
    (hFresh : StrictMono fresh)
    (hLabels : ∀ i column (h : source.keyTemplate p.reduced_valid.toOrdered D i = some column),
      fresh ⟨copiedKeyColumn p.root.column (block * (p.reduced.size - 1 - p.root.column)) column.val,
        (copy.extend preserved).key_support_bound source i column h⟩ = old column) :
    Keys.eval (edge.keyTemplate
      (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered D) fresh ≤
    Keys.eval (source.keyTemplate p.reduced_valid.toOrdered D) old := by
  have h := s.preserved_effective_edge_finite_key_le history hLast hStartRun source hBefore copy preserved hRun edge hLower D fresh hFresh
  exact h.trans_eq (Keys.eval_mapSupported_of_labels _ _ _ old fresh hLabels)

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.key_support_bound
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_effective_edge_template_le
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_effective_edge_finite_key_le
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_effective_edge_source_labels_le
