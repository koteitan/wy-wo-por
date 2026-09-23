/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSpliceReservoirs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSpliceFacts
import OmegaY.Expansion.SupportedDimension

/-!
The real lower last-column edges are strictly below the real deleted
control edge. Strictly increasing casts and block transports preserve
that full finite-key comparison, including every infinity coordinate.
The demands are the complete virtual reserve itself, so coverage is
proved rather than supplied by the caller.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem templateKey_relabel_lt {m n k : Nat} (left right : Keys.Template m n)
    (transport : Fin n → Fin k) (hTransport : StrictMono transport)
    (hKey : Keys.templateKey left < Keys.templateKey right) :
    Keys.templateKey (Keys.relabel left transport) <
      Keys.templateKey (Keys.relabel right transport) := by
  simpa only [Keys.templateKey, Keys.eval_relabel, Function.id_comp] using
    Keys.eval_lt_of_template_lt left right transport hTransport hKey

namespace RootGeometry

variable {front : List Nat} {last : Nat} {p : Preparation front last}

theorem initialSpliceVirtualAtom_key_strict (g : RootGeometry p) {D : Nat}
    (hDimension : MountainKeyDimension p.initial D) (edge : g.LowerEdge) :
    Keys.templateKey (g.initialSpliceVirtualAtom D edge).key <
      Keys.templateKey (g.initialSpliceControl D).key := by
  exact templateKey_relabel_lt (g.lowerAtom D edge).key (g.controlAtom D).key
    (Fin.cast p.initial_pop_size) (Splice.fin_cast_strictMono _) (g.lower_key_strict hDimension edge)

theorem spliceVirtualFacts_key_strict (g : RootGeometry p) {D : Nat}
    (hDimension : MountainKeyDimension p.initial D) (block : Nat)
    (d : Model.TopAtom (D + 1) (Splice.blockWidth front.length p.root.column block))
    (hd : d ∈ g.spliceVirtualFacts D block) :
    Keys.templateKey d.key < Keys.templateKey (g.spliceControl D block).key := by
  obtain ⟨initial, hInitial, rfl⟩ := List.mem_map.mp hd
  obtain ⟨edge, rfl⟩ := (g.mem_initialSpliceVirtualFacts_iff D initial).mp hInitial
  exact templateKey_relabel_lt (g.initialSpliceVirtualAtom D edge).key (g.initialSpliceControl D).key
    (Splice.blockSource p.root_before_last block) (Splice.blockSource_strictMono _ _)
    (g.initialSpliceVirtualAtom_key_strict hDimension edge)

/-- We select `N_b = T_b`; no virtual fact is dropped or assumed to be
re-created by a later reflection. -/
theorem spliceVirtualFacts_self_covered (g : RootGeometry p) (D block : Nat) :
    Splice.DemandCovered (g.spliceVirtualFacts D block) (g.spliceVirtualFacts D block) := by
  intro d hd
  exact ⟨d, hd, rfl, le_rfl⟩

end RootGeometry
end OmegaY.Expansion

#print axioms OmegaY.Expansion.RootGeometry.initialSpliceVirtualAtom_key_strict
#print axioms OmegaY.Expansion.RootGeometry.spliceVirtualFacts_key_strict
#print axioms OmegaY.Expansion.RootGeometry.spliceVirtualFacts_self_covered
