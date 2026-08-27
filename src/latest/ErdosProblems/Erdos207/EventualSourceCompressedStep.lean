/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCompressedCoverAssembly
import ErdosProblems.Erdos207.EventualSourceSparseStageBudget
import ErdosProblems.Erdos207.EventualSourceReserveBudget
import ErdosProblems.Erdos207.EventualSourceLinkStageBudget
import ErdosProblems.Erdos207.SourceOrdinaryParameters

/-! # A uniform genuine compressed transition with a freely chosen late error exponent -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem eventually_source_compressed_step
    (q h b ell R rootExp step v D : ℕ) (i : Fin ell) (E : SourceOrdinaryParameters q h b)
    (C B0 eta0 : ℝ≥0) (hb : 2 ≤ b) (hh : 4 ≤ h) (hv : 1 ≤ v) (hD : E.K*v ≤ D)
    (hstep : 4*b+2 ≤ step) (hroot : b*(h+1)+2 ≤ rootExp)
    (hC : 1 ≤ C) (heta0 : 0 < eta0) (heta01 : eta0 ≤ 1) :
    ∃ minimum : ℕ, 1 ≤ minimum ∧ ∀ m : ℕ, minimum ≤ m →
      ∃ Tphysical Tanalytic : ℕ, 2 ≤ Tphysical ∧ 1 ≤ Tanalytic ∧
      ∀ t analytic : ℕ, Tphysical ≤ t → Tanalytic ≤ analytic → analytic ≤ t →
        t^(E.P*v) ≤ analytic^(D+1) →
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (W : Vortex V ell)
        (bank ambient : TripleSystemOn V) (Gamma : SimpleGraph V),
      Fintype.card V ≤ t^R → t^D ≤ (W.U i.castSucc).card → t^(D-v) ≤ (W.U i.succ).card →
      (W.U i.castSucc).card ≤ t^v*(W.U i.succ).card → t^step*(W.U i.succ).card ≤ 2*(W.U i.castSucc).card →
      analytic ^ ksssPowerDenominatorExponent q (2*(D+1)) E.B ((26*q+12)*(D+1)) (D+1) ≤
        (W.U i.castSucc).card →
      (∀ j ∈ Icc 4 q, sourcePrefixZ q bank i.val j ≤ (t : ℝ≥0)^v) →
      (∀ a ∈ futureLevelPairs i.succ, t^rootExp ≤ (W.U a.2).card) →
      (∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ Icc 4 q, sourcePrefixZ q bank a.1.val j ≤ t) →
      ∀ (p eta xi xi' beta : ℝ≥0) (incoming : ℕ),
      1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b → eta0 ≤ eta → eta ≤ 1 →
      xi ≤ (17+ell : ℕ)/(t : ℝ≥0) → xi+1/t ≤ xi' → 6/t ≤ xi' →
      m ≤ incoming → sourceStageRequiredError q (D+1) ((D+1)*R) m ≤ incoming →
      beta ≤ B0/(t : ℝ≥0)^incoming →
      (∀ a, (W.U a).Nonempty) → HasAbsorberSourcePrefixBounds q bank W →
      ∀ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W i.castSucc (absorberErdosForbiddenConfigurationsOn q bank)
        Gamma ambient p eta xi C beta h →
      ∃ law' : FiniteLaw (MasterStateOn V),
        IsResidualCompressedMasterLaw law' W i.succ (absorberErdosForbiddenConfigurationsOn q bank)
          Gamma ambient p eta xi'
          (sourceMasterConstantStep (152*sourceOrdinaryProductConstant q/eta0)
            (2*sourceOrdinaryProductConstant q) C) (beta+1/(analytic : ℝ≥0)^((D+1)*m)) h := by
  let c := D+1
  let S := E.S*v
  let d := E.P*v
  let Ran := c*R
  let constant := sourceOrdinaryProductConstant q
  have hconstant : 1 ≤ constant := (by norm_num : (1 : ℝ≥0) ≤ 2).trans (le_max_left _ _)
  have hc : 1 ≤ c := by dsimp only [c]; omega
  obtain ⟨hreserveGap, hfutureGap, hrateGap, hdensityGap, _, hinnerGap, hmarked, _, hreserveDensity⟩ :=
    E.physical v D hv hD
  have hsub : D-v ≤ D := Nat.sub_le _ _
  have hmarkedD : v+(1+v+S+2*b)*(q+1)+1 ≤ D := by
    have hm := hmarked
    rw [Nat.mul_comm (q+1)] at hm
    dsimp only [S]
    omega
  have hcurrentGap : 2*S ≤ D := by dsimp only [S]; omega
  have hpointGap : 2*b+1 ≤ D := by omega
  have hauxGap : 3*b*(q-3)+v ≤ D :=
    source_auxiliary_gap_of_marked_gap q b S v D (by dsimp only [S]; omega) hmarked
  obtain ⟨MI, TI, hMI, hTI, hI⟩ := eventually_exists_source_internal_stage_budget q ell R b S v d D (D-v)
    eta0 constant (16*C) B0 hb heta0 heta01 hconstant hinnerGap hrateGap hpointGap
  obtain ⟨ML, TL, hML, hTL, hL⟩ := eventually_exists_source_link_stage_budget q h ell b S v D (D-v) rootExp R
    (sourceOrdinaryInternalConstant q eta0 C) (B0+1) eta0 hb heta0 heta01 hreserveGap hfutureGap
    hinnerGap hcurrentGap hmarkedD hroot
  let minimum := max MI ML
  refine ⟨minimum, hMI.trans (le_max_left _ _), ?_⟩
  intro m hm
  have hm1 : 1 ≤ m := (hMI.trans (le_max_left _ _)).trans hm
  have hMIm : MI ≤ m := (le_max_left _ _).trans hm
  have hMLm : ML ≤ m := (le_max_right _ _).trans hm
  obtain ⟨Tcover, hTcover, hcover⟩ := eventually_source_compressed_cover q h (2*c) E.B ((26*q+12)*c) c c Ran m eta0 heta0
  obtain ⟨Trp, Tra, hTrp, hTra, hreserve⟩ := eventually_source_reserve_preparation_budget
    q ell b S D (D-v) step R (2*c) E.B ((26*q+12)*c) c Ran eta0 heta0
    (by dsimp only [S]; omega) hstep (by dsimp only [S]; omega) (by omega) (by omega)
  have hC8 : 1 ≤ 8*C := by
    simpa only [one_mul] using mul_le_mul (show (1 : ℝ≥0) ≤ 8 by norm_num) hC zero_le zero_le
  obtain ⟨Tsp, Tsa, hTsp, hTsa, hTsaLarge, hSparse⟩ := eventually_source_sparse_stage_budget
    q i.val E.B b c v d Ran m (max Tcover Tra) (sourceAuxiliaryCoefficient q i.val) (4*C) (8*C) B0 eta0
    hb hc hm1 hdensityGap (by dsimp only [d]; omega) (one_le_sourceAuxiliaryCoefficient q i.val) hC8 heta0
    E.envelope E.pair E.configuration
  let Tp := TI+TL+Trp+Tsp+2
  refine ⟨Tp, Tsa, by dsimp only [Tp]; omega, by omega, ?_⟩
  intro t analytic ht ha hat hpower V _ _ W bank ambient Gamma hN hn hu hratio hstepRatio hscale hz
    hfutureSize hfutureZ p eta xi xi' beta incoming hp hpUpper heta heta1 hxi hxiStep hxiSize
    hmi hrequired hbeta hnonempty hsource law hlaw
  have ht8 : 8 ≤ t := by dsimp only [Tp] at ht; omega
  have ht1 : 1 ≤ t := by omega
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have haLarge : 49152 ≤ analytic := hTsaLarge.trans ha
  have ha1 : 1 ≤ analytic := by omega
  have haNN : (1 : ℝ≥0) ≤ analytic := by exact_mod_cast ha1
  have ha0 : (0 : ℝ≥0) < analytic := zero_lt_one.trans_le haNN
  have hatNN : (analytic : ℝ≥0) ≤ t := by exact_mod_cast hat
  have hpowerNN : (t : ℝ≥0)^d ≤ (analytic : ℝ≥0)^c := by exact_mod_cast hpower
  have htac : t ≤ analytic^c := by
    apply le_trans _ hpower
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < t by omega) (show 1 ≤ d by dsimp only [d]; omega)
  have hNa : Fintype.card V ≤ analytic^Ran := by
    calc
      _ ≤ t^R := hN
      _ ≤ (analytic^c)^R := Nat.pow_le_pow_left htac R
      _ = _ := (pow_mul analytic c R).symm
  have hba : beta ≤ B0/(analytic : ℝ≥0)^sourceStageRequiredError q c Ran m :=
    cross_scale_incoming_error t analytic beta B0 incoming (sourceStageRequiredError q c Ran m)
      haNN hatNN hrequired hbeta
  obtain ⟨sparse, hauxError, hdelta, hpAnalyticLo, hpAnalyticHi, hCaux⟩ :=
    hSparse t analytic (by dsimp only [Tp] at ht; omega) ha hat hpower (W.U i.castSucc).card (Fintype.card V)
      hscale (card_le_univ _) hNa p eta beta hp hpUpper heta heta1 hba (sourcePrefixZ q bank i.val) hz
  have hn0 : (0 : ℝ≥0) < (W.U i.castSucc).card := by
    exact_mod_cast (show 0 < (W.U i.castSucc).card by have hnp := sparse.current_pos; omega)
  have hratioDensity : 24/(analytic : ℝ≥0)^(2*c) ≤ p^2*eta := by
    have hmul : (24/(analytic : ℝ≥0)^(2*c))*((W.U i.castSucc).card : ℝ≥0) ≤
        (p^2*eta)*((W.U i.castSucc).card : ℝ≥0) := by
      calc
        _ = 24*(((W.U i.castSucc).card : ℝ≥0)/(analytic : ℝ≥0)^(2*c)) := by ring
        _ ≤ 24*(p^2*eta*(W.U i.castSucc).card/24) := mul_le_mul_of_nonneg_left sparse.ratio_floor zero_le
        _ = _ := by ring
    exact le_of_mul_le_mul_right hmul hn0
  have hprep := hreserve t analytic (Fintype.card V) (W.U i.castSucc).card (W.U i.succ).card
    (by dsimp only [Tp] at ht; omega) ((le_max_right _ _).trans (hTsa.trans ha))
    hN ((card_le_univ _).trans hN) hn hu hstepRatio hscale ((card_le_univ _).trans hNa)
    p eta xi hp heta hratioDensity hxi
  rcases hprep with ⟨hr1, hrSmall, hxiRef, hxiSmall, hendpoint, hmass, hinner, htheta,
    hthetaHalf, hsampling, hreserveError, _⟩
  have hbetaI : beta ≤ B0/(t : ℝ≥0)^MI := hbeta.trans
    (polynomial_incoming_error_budget t B0 incoming MI htNN (hMIm.trans hmi))
  have hdeltaI : 1/(analytic : ℝ≥0)^(c*m) ≤ 1/(t : ℝ≥0)^MI := hdelta.trans
    (polynomial_incoming_error_budget t 1 m MI htNN hMIm)
  obtain ⟨internal, hdegreeI⟩ := hI t (by dsimp only [Tp] at ht; omega) W i bank c analytic p eta beta
    (1/(analytic : ℝ≥0)^(c*m)) hN hn (by exact_mod_cast hu) (by exact_mod_cast hratio) hpowerNN
    hp hpUpper heta hbetaI hdeltaI hz
  have hsum : beta+1/(analytic : ℝ≥0)^(c*m) ≤ (B0+1)/(t : ℝ≥0)^ML := by
    calc
      _ ≤ B0/(t : ℝ≥0)^ML+1/(t : ℝ≥0)^ML := add_le_add
        (hbeta.trans (polynomial_incoming_error_budget t B0 incoming ML htNN (hMLm.trans hmi)))
        (hdelta.trans (polynomial_incoming_error_budget t 1 m ML htNN hMLm))
      _ = _ := by ring
  obtain ⟨link, hdegreeL, hdegreeErrorL, hreference⟩ := hL t (by dsimp only [Tp] at ht; omega)
    W i bank p (beta+1/(analytic : ℝ≥0)^(c*m)) eta xi xi' hN hn hu hratio hz hfutureSize hfutureZ
    hp hpUpper sparse.p_le_one heta heta1 hxiStep hxiSize hsum
  have herrorHalf : 1/(t : ℝ≥0)^2 ≤ 1/2 := by
    have ht2 : (2 : ℝ≥0) ≤ t := by exact_mod_cast (show 2 ≤ t by omega)
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ≥0) < 2^2) (pow_le_pow_left' ht2 2)).trans
      (by apply NNReal.coe_le_coe.mp; norm_num)
  have hauxDensity : 1 ≤ p^3*(W.U i.castSucc).card := by
    have hb0 : b*3+0 ≤ D := by omega
    simpa only [pow_zero] using inversePower_density_ge_power t p (W.U i.castSucc).card b 3 0 D
      htNN hp hb0 (by exact_mod_cast hn)
  have hauxExtension : ∀ j ∈ Icc 4 q, ∀ j' ∈ Icc j q,
      sourcePrefixZ q bank i.val j' ≤ sourcePrefixY q i.val*p^(3*(j-3))*(W.U i.castSucc).card := by
    intro j hj j' hj'
    have hj'q : j' ∈ Icc 4 q := mem_Icc.mpr ⟨(mem_Icc.mp hj).1.trans (mem_Icc.mp hj').1, (mem_Icc.mp hj').2⟩
    exact source_auxiliary_extension_power t (W.U i.castSucc).card p (sourcePrefixZ q bank i.val j')
      (sourcePrefixY q i.val) q j b v D htNN (one_le_sourcePrefixY q i.val) hp (hz j' hj'q)
      (by exact_mod_cast hn) (mem_Icc.mp hj).2 hauxGap
  let budget : SourceCoverStageBudget q h (2*c) E.B ((26*q+12)*c) analytic c c Ran m W i bank
      p eta xi xi' (1/(t : ℝ≥0)^S) C beta eta0 B0 (1/(t : ℝ≥0)^2) := {
    C_pos := hC
    h_large := hh
    eta_floor := heta
    r_pos := by positivity
    r_le_one := hr1
    r_small := hrSmall
    xi_reference := hxiRef
    xi_small := hxiSmall
    reference_endpoint := hendpoint
    current_density := hmass
    inner_margin := hinner
    theta_pos := htheta
    theta_half := hthetaHalf
    sampling := hsampling
    reserve_error := hreserveError
    error_half := herrorHalf
    analytic_density_lower := hpAnalyticLo
    analytic_density_upper := hpAnalyticHi
    auxiliary_coefficient := hCaux
    auxiliary_density := hauxDensity
    auxiliary_extension := hauxExtension
    auxiliary_error := hauxError
    sparse := sparse
    internal := internal
    link := link
    link_degree := hdegreeL
    degree_error := by rw [hdegreeI, hdegreeErrorL]
    link_reference := hreference }
  exact hcover analytic ((le_max_left _ _).trans (hTsa.trans ha)) W i bank ambient Gamma
    p eta xi xi' (1/(t : ℝ≥0)^S) C beta B0 (1/(t : ℝ≥0)^2) budget hnonempty hsource law hlaw

end

end Erdos207
