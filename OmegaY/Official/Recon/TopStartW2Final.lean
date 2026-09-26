import OmegaY.Official.Recon.TopStartW2NoEnd
import OmegaY.Official.Classification.Proofs.TopStartW2Key
import OmegaY.Official.Recon.SCXMain
import OmegaY.Official.Recon.CrossUpperQHiCut

set_option autoImplicit false

/-!
# Stage F: the assembly with `TopStart''`

`TopStart''` (`TopStartW2.lean`, **proved**) replaces the false `TopStart'` in every consumer:

| consumer | clause of the start it needs | rebuilt as |
|---|---|---|
| `KeyLeRest` (`keyLeRest_pkg3'`) | `StandW` only | `TopStartW2Key.keyLeRest_pkg3''` |
| `CrossLexFor IsPlain`, `IsClean` (`QStand K`) | strong clause (`Cp`: the top copy right of `c_r`) | `TopStartW2R.crossLexFor_plain''`, `crossLexFor_clean''` over `CpW`, with `NonTopPass` (proved, `TopStartW2Recon.lean`) and `NoEndRight` (proved, `TopStartW2NoEnd.lean`) |
| `RootPass IsPlain` (`CCL.rootPass_plain_of`) | strong clause (through `QStand IsPlain`) | `TopStartW2R.rootPass_plain''` (proved) |
| `CrossLexFor IsUpper` (`copyQLowerW_of_new`) | `StandW` only | `copyQLowerW_of_new''`, `crossLexFor_upper_of_chain''` (still needs the false `PaONoGapHi`) |
| `FinalStageE` | all of the above | `wellFounded_of_stageF` |

`QStand IsPlain` itself is false (`(1,4,18,56,18)[1]`, see `TopStartW2Recon.lean`), so the
plain and clean chains start from the weak relation `CpW`.

Results:

* **`crossLexFor_plain_final'' : CrossLexFor IsPlain`**, **`crossLexFor_clean_final'' :
  CrossLexFor IsClean`** (no hypothesis);
* `reconstructionHolds_of_stageF`, `blockReconstruction_of_stageF`, `keyLeRest_of_stageF`:
  from `CrossLexFor IsUpper` alone;
* **`wellFounded_of_stageF : CrossLexFor IsUpper → WellFounded Descent.Step`**;
* `copyQLowerW_of_new'' : TopStart'' → QRootSeam → PaONoGapHi → CutRightTopHi → CopyQLowerW`,
  `crossLexFor_upper_of_chain'' : TopStep → TopStart'' → SeamChainX → QRootRowGe → PaONoGapHi →
  CutRightTopHi → CrossLexFor IsUpper` (the old route of `CrossLexFor IsUpper` with the new
  start; `PaONoGapHi` and `CopyQLowerW` are false, so this route stays empty);
  `wellFounded_of_paONoGapHi : PaONoGapHi → WellFounded Descent.Step` records that the old route
  would close the proof (`TopStep`, `TopStart''`, `SeamChainX`, `QRootRowGe`, `CutRightTopHi`
  proved), but its hypothesis is false.

What remains open for the well-foundedness: `CrossLexFor IsUpper` (a separate rebuild).
-/

namespace OmegaY.Official.Recon.CrossUpperQ.W2

open Canonical Expansion Geometry Frame Classification
open CrossUpper CrossUpperSim LowerChainRecon CrossUpperW
open Classification.Proofs.ChainCorr.TopStartFix (StandW)
open TopStartW2 (TopStart'')
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt TopNode CopyOf above)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## `CrossLexFor IsUpper` with `TopStart''` (the weak part suffices) -/

/-- **`CopyQLowerW` from `TopStart''` and the three statements** (only `StandW` is used). -/
theorem copyQLowerW_of_new'' (hTSt : TopStart'') (hRS : QRootSeam) (hPG : PaONoGapHi)
    (hCR : CutRightTopHi) : CopyQLowerW := by
  intro s n R M t root i y hrun hTop hi1 hy U z z' hU1 hz1 hz hzτ hzu hθ hTC
  have hTC0 := hTC
  have hcr := hTop.lt
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hy
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have E := env_of hrun hTop U.1.isLt (by rw [hU1]; omega)
  have hG := E.G
  have hF := E.FR
  have hin : i ≤ n := block_le E hyg hyl (by rw [← hU1]; exact U.1.isLt) (by rw [← hU1, hU1]; omega)
  obtain ⟨⟨hU0, o, ho, hsrc⟩, hTop'⟩ := hTC
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := originAt_unpack2 hTop hy hU1 ho
  have hjl : U.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hej : es[U.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hjo
    exact Option.some.inj hjo
  have hsrcj : es[U.2.val - 1].2.src = Frame.ref z := by rw [hej]; exact hsrc
  -- the emit of `U` is the top copy of its source
  have hsize : colX.size = es.length + 1 := by
    have := (assemble_spec hasm).1
    simpa using this
  have hRXe : R[U.1.val] = colX := by
    rcases Array.getElem?_eq_some_iff.mp hRX with ⟨_, h⟩
    exact h
  have hIT : IsTopAt es (U.2.val - 1) := by
    intro j' hj' _ hlt heq
    have hlen : j' + 1 < (Frame.ofMountain R).length U.1 := by
      change j' + 1 < R[U.1.val].size
      rw [hRXe, hsize]
      omega
    let Z' : (Frame.ofMountain R).Node := ⟨U.1, ⟨j' + 1, hlen⟩⟩
    have hZ'c : Z'.1.val = y + (M.size - 1 - root.column) * i := hU1
    have hes' : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
        Z'.1.val) (Official.official t.row) = .ok es := hes
    obtain ⟨_, hoZ⟩ := originAt_of_emits E hi1 hy hZ'c (by show 0 < j' + 1; omega) hes'
    apply hTop' Z' rfl (by show U.2.val < j' + 1; omega)
    refine ⟨by show 1 ≤ j' + 1; omega, es[j'].2, hoZ, ?_⟩
    rw [heq, hsrcj]
  -- the cells, the leg and the candidates
  have hcz := cell?_ref z
  rw [← hsrcj] at hcz
  obtain ⟨_, _, cv', hcv', hleft⟩ := emitsT_good hes es[U.2.val - 1] (List.getElem_mem hjl)
  have hcvv : cv' = (Frame.ofMountain M).cell z := Option.some.inj (hcv'.symm.trans hcz)
  subst hcvv
  obtain ⟨l, hl⟩ : ∃ l, ((Frame.ofMountain M).cell z).left = some l := by
    rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, _⟩
    · exact ⟨l, hl⟩
    · have hV := build_valid_of_success hTop.build
      have hi1' := index_one_of_official_zero hV hcv' (by rw [hsrcj]; exact hz) h0
      exact ⟨_, bottom_left hTop.build hcv' hi1' (by rw [hsrcj]; simp [Frame.ref]; omega)⟩
  obtain ⟨cu, ref, hcu, href, hrefc⟩ :=
    leg_image_run hTop hi1 hy hU1 hes hRX hasm hjl hcv' hl
  have hcuU : Reserve.cell? R ⟨U.1.val, U.2.val - 1 + 1⟩ = some ((Frame.ofMountain R).cell U) := by
    have := cell?_ref U
    rwa [show (Frame.ref U : Ref) = ⟨U.1.val, U.2.val - 1 + 1⟩ by
      simp only [Frame.ref]; congr 1; omega] at this
  have hcuu : cu = (Frame.ofMountain R).cell U := Option.some.inj (hcu.symm.trans hcuU)
  subst hcuu
  obtain ⟨a, ha⟩ := Frame.Q_exists_of_left hG ⟨l, hl⟩
  obtain ⟨A, hA⟩ := Frame.Q_exists_of_left hF ⟨ref, href⟩
  have hpa := Q_eq_highestAtMost hG hz ha hl
  have hUr : Real U := by unfold Real; omega
  have hpe := Q_eq_highestAtMost hF hUr hA href
  rw [hrefc] at hpe
  have hS := (hTSt s n R M t root i y hrun hTop (by omega) hin hy es (by rw [← hU1]; exact hes)
    (U.2.val - 1) hjl hIT ((Frame.ofMountain R).cell U) ((Frame.ofMountain M).cell z) l
    (Frame.ref A) (Frame.ref a) (by rw [← hU1]; exact hcuU) hcv' hl hpa hpe).1
  have hax : a.1.val < M.size - 1 := by
    obtain ⟨left, hleft', hlc, _, hql, _, _, _⟩ := Frame.Q_spec hG ha
    rw [hql]
    omega
  refine ⟨a, A, ha, hA, ?_⟩
  obtain ⟨hSl, hSe, _⟩ := hS
  -- the columns of `a` and `A`
  obtain ⟨leftM, hleftM, _, _, hqlM, _, hhaz, _⟩ := Frame.Q_spec hG ha
  obtain ⟨leftR, hleftR, _, _, hqlR, _, _, _⟩ := Frame.Q_spec hF hA
  have hlM : l = Frame.ref leftM := Option.some.inj (hl.symm.trans hleftM)
  have hlR : ref = Frame.ref leftR := Option.some.inj (href.symm.trans hleftR)
  have hac : a.1.val = l.column := by rw [hqlM, hlM]; rfl
  have hAc : A.1.val = Reserve.mapColumn root.column ((M.size - 1 - root.column) * i)
      l.column := by rw [hqlR, ← hrefc, hlR]; rfl
  rcases Nat.lt_trichotomy a.1.val root.column with hlt | heq | hgt
  · have hAa : Frame.ref A = Frame.ref a := hSl hlt
    have hc : A.1.val = a.1.val := congrArg Ref.column hAa
    refine Or.inl ⟨hlt, hc, ?_⟩
    have h1 := cell?_ref A
    rw [hAa, cell_agree E.agree (by show a.1.val < M.size - 1; exact hax), cell?_ref a] at h1
    unfold Frame.height
    rw [Option.some.inj h1]
  · obtain ⟨hcol, hch⟩ := hSe heq
    refine Or.inr (Or.inl ⟨heq, hcol, fun b hb => ?_, fun a' ha' hθa => ?_⟩)
    · have hbr := reserve_rawParent_of_frame hb
      obtain ⟨B, hB, hch'⟩ := rawChain_of_scaleReach
        (hch (Frame.ref b) _ _ hbr (cell?_ref a) (cell?_ref b)) A rfl
      have hbc : b.1.val < root.column := by
        have := Frame.rawParent_column_lt E.G hb
        omega
      refine ⟨B, hch', congrArg Ref.column hB, ?_⟩
      have h1 := cell?_ref B
      rw [hB, cell_agree E.agree (by show b.1.val < M.size - 1; omega), cell?_ref b] at h1
      unfold Frame.height
      rw [Option.some.inj h1]
    · exact rootUp_of_seam hRS hrun hTop hi1 hy E hU1 hz1 hz hzτ hzu hθ hTC0 ha hA heq ha' hθa
        hcol
  · refine Or.inr (Or.inr ⟨hgt, hax, ?_, fun hθa => ?_, fun _ => ?_⟩)
    · rw [hAc, Classification.Proofs.ChainCorr.mapColumn_of_ge (by omega), ← hac]
    · exact absurd (lt_of_le_of_lt (hθa.trans hhaz) hzτ) (lt_irrefl _)
    · apply topCopy_of_topNode E hi1
      have hlr : root.column < l.column := by rw [← hac]; exact hgt
      have hHi : HasAboveHi M t.row es[U.2.val - 1].2.src := by
        rw [hsrcj]
        refine ⟨(Frame.ofMountain M).cell z', ?_, hθ⟩
        have h1 := cell?_ref z'
        obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
        rwa [show (Frame.ref z' : Ref) = above (Frame.ref z) by
          simp only [Frame.ref, above, hz'1, hz'2]] at h1
      have hesX : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
          (y + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es := by
        rw [← hU1]; exact hes
      have hcuX : Reserve.cell? R ⟨y + (M.size - 1 - root.column) * i, U.2.val - 1 + 1⟩ =
          some ((Frame.ofMountain R).cell U) := by rw [← hU1]; exact hcuU
      cases hcut : Classification.Proofs.ChainCorr.cutOrigin es[U.2.val - 1].2
      · by_cases hpao : ∃ cp, Reserve.cell? M (Frame.ref a) = some cp ∧
            cp.row = ((Frame.ofMountain M).cell z).row
        · exact TopStartFixParts.topNode_paO hrun hTop (by omega) hin hy hesX hjl hcuX hcv' hl hpa
            hpe hzτ hlr hcut hpao
            (hPG s n R M t root i y hrun hTop (by omega) hin hy es hesX (U.2.val - 1) hjl hIT _ _ l
              (Frame.ref A) (Frame.ref a) hcuX hcv' hl hpa hpe hzτ hlr hcut hpao hHi)
        · have hS := TopChain.topStartLoRightNC hrun hTop (by omega) hin hy hesX hjl hcuX hcv' hl hpa
            hpe hzτ hlr hcut (fun cp hcp => by
              rw [cell?_ref a] at hcp
              obtain rfl := Option.some.inj hcp
              rcases lt_or_eq_of_le hhaz with h | h
              · exact h
              · exact absurd ⟨_, cell?_ref a, h⟩ hpao)
          exact hS.2.2 hgt
      · exact hCR s n R M t root i y hrun hTop (by omega) hin hy es hesX (U.2.val - 1) hjl hIT _ _ l
          (Frame.ref A) (Frame.ref a) hcuX hcv' hl hpa hpe hzτ hlr hcut hHi

/-- **`CrossLexFor IsUpper` from `TopStep`, `TopStart'` and the three new statements.** -/
theorem crossLexFor_upper_of_new'' (hTS : Classification.Proofs.ChainCorr.LowerChain.TopStep)
    (hTSt : TopStart'') (hRS : QRootSeam) (hPG : PaONoGapHi) (hCR : CutRightTopHi) :
    CrossLexFor IsUpper :=
  crossLexFor_upper_of_W hTS (copyQLowerW_of_new'' hTSt hRS hPG hCR)

/-- **`CrossLexFor IsUpper` through `SeamChainX` and `QRootRowGe`, with `TopStart''`.** -/
theorem crossLexFor_upper_of_chain'' (hTS : Classification.Proofs.ChainCorr.LowerChain.TopStep)
    (hTSt : TopStart'') (hSC : SeamChainX) (hRG : QRootRowGe) (hPG : PaONoGapHi)
    (hCR : CutRightTopHi) : CrossLexFor IsUpper :=
  crossLexFor_upper_of_new'' hTS hTSt (qRootSeam_of_chain hSC hRG) hPG hCR

end OmegaY.Official.Recon.CrossUpperQ.W2

namespace OmegaY.Official.Recon.TopStartW2F

open TopStartW2R

/-- **`CrossLexFor IsPlain` holds.** -/
theorem crossLexFor_plain_final'' : CrossLexFor IsPlain :=
  crossLexFor_plain'' TSQ.W2.noEndRight_plain

/-- **`CrossLexFor IsClean` holds.** -/
theorem crossLexFor_clean_final'' : CrossLexFor IsClean :=
  crossLexFor_clean'' TSQ.W2.noEndRight_clean

/-- **`ReconstructionHolds` from `CrossLexFor IsUpper`.** -/
theorem reconstructionHolds_of_stageF (hU : CrossLexFor IsUpper) :
    Reconstruction.ReconstructionHolds := by
  have hCh : ChainHolds :=
    chainHolds_of_three LowerPB.StageB.parentBelowHolds crossLexFor_plain_final''
      crossLexFor_clean_final'' CutPredMD.cutPredHolds hU
  exact reconstructionHolds_of_rowLaw_chain (RowLaw.rowLawHolds_of_jumpLaw LRC.jumpLawHolds) hCh

/-- **`BlockReconstruction` from `CrossLexFor IsUpper`.** -/
theorem blockReconstruction_of_stageF (hU : CrossLexFor IsUpper) :
    Dimension.BlockReconstruction :=
  blockReconstruction_of_reconstructionHolds (reconstructionHolds_of_stageF hU)

/-- **`KeyLeRest` from `CrossLexFor IsUpper`** (`TopStart''` proved). -/
theorem keyLeRest_of_stageF (hU : CrossLexFor IsUpper) : Classification.KeyLeRest :=
  Classification.Proofs.ChainCorr.TopStartW2Key.keyLeRest_pkg3'' FinalStageE.topStep_final
    TopStartW2.topStart''_holds
    (Classification.Proofs.ChainCorr.NonTop.nonTopStep_of_reconstruction
      (blockReconstruction_of_stageF hU))
    Classification.Proofs.ChainCorr.NonTop.startRelNT
    Classification.Proofs.ChainCorr.NonTop.startRootNT TopChain.Seam.CPN.boundaryChain
    Classification.Proofs.P3T.cutJumpRootRow Classification.Proofs.P3T.cutRunTop

/-- **Well-foundedness of the official ω-Y expansion from `CrossLexFor IsUpper`.** -/
theorem wellFounded_of_stageF (hU : CrossLexFor IsUpper) : WellFounded Descent.Step :=
  Classification.ControlProof.wellFounded_of_block_keys (blockReconstruction_of_stageF hU)
    (keyLeRest_of_stageF hU)

/-- The old route of `CrossLexFor IsUpper` with `TopStart''` would close the proof; its
hypothesis `PaONoGapHi` is false (`CrossUpperQHiFalse.lean`). -/
theorem wellFounded_of_paONoGapHi (hPG : CrossUpperQ.PaONoGapHi) : WellFounded Descent.Step :=
  wellFounded_of_stageF (CrossUpperQ.W2.crossLexFor_upper_of_chain'' FinalStageE.topStep_final
    TopStartW2.topStart''_holds SCX.seamChainX SCX.qRootRowGe hPG CrossUpperQ.QHi.cutRightTopHi)

end OmegaY.Official.Recon.TopStartW2F

#print axioms OmegaY.Official.Recon.CrossUpperQ.W2.copyQLowerW_of_new''
#print axioms OmegaY.Official.Recon.CrossUpperQ.W2.crossLexFor_upper_of_chain''
#print axioms OmegaY.Official.Recon.TopStartW2F.crossLexFor_plain_final''
#print axioms OmegaY.Official.Recon.TopStartW2F.crossLexFor_clean_final''
#print axioms OmegaY.Official.Recon.TopStartW2F.reconstructionHolds_of_stageF
#print axioms OmegaY.Official.Recon.TopStartW2F.blockReconstruction_of_stageF
#print axioms OmegaY.Official.Recon.TopStartW2F.keyLeRest_of_stageF
#print axioms OmegaY.Official.Recon.TopStartW2F.wellFounded_of_stageF
#print axioms OmegaY.Official.Recon.TopStartW2F.wellFounded_of_paONoGapHi
