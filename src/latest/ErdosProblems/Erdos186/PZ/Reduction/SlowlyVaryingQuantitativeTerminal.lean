/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.FrozenSlowlyVaryingConstruction

/-!
# Quantitative terminal reduction with frozen slowly-varying parameters
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible
open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

theorem exists_quantitative_terminal_slowlyVarying
    (ell : ℕ) (beta eta : ℝ)
    (C : HigherDimensionalContext (2 * (beta + 1)) eta)
    (hbeta : 1 < beta) (heta0 : 0 < eta) (heta1 : eta < 1)
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < (1 / 3 : ℝ)) :
    ∃ K0 : ℕ, 1 ≤ K0 ∧
    ∃ constant : ℝ, 0 < constant ∧
      ∀ kappa : ℝ, 0 < kappa →
      ∀ K : ℕ, K0 ≤ K →
        ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ (B : CFP.IntegerBox ell)
          (A : Finset (LatticePoint ell)),
          threshold ≤ A.card → A ⊆ B.carrier →
          (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) beta →
          IsBoxNonaveraging A →
          ∃ selector : BoundedCFPSelector C,
          ∃ hnorm : selector.Eligible (normalizeSet B A),
            Nonempty (IrreducibleReplacementResult selector B A hnorm
              epsilon (Erdos186.delta kappa A.card)
                (Erdos186.gamma kappa (K : ℝ) A.card) K constant) := by
  let tau : ℝ := 1 - epsilon / 2
  let sigma : ℝ := guardedScaleExponent epsilon
  let a : ℝ := 1 - epsilon
  have hepsilon_lt_one : epsilon < 1 := hepsilon1.trans (by norm_num)
  have htau0 : 0 < tau := by dsimp [tau]; linarith
  have htau1 : tau < 1 := by dsimp [tau]; linarith
  have hsigma0 : 0 < sigma := guardedScaleExponent_pos hepsilon0 hepsilon_lt_one
  have hsigma1 : sigma < 1 := guardedScaleExponent_lt_one hepsilon0 hepsilon_lt_one
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha23 : (2 / 3 : ℝ) ≤ a := by dsimp [a]; linarith
  have hata : tau * sigma = a := by
    dsimp [tau, sigma, a]
    exact cutoff_mul_guardedScaleExponent (by linarith)
  have hasigma : a ≤ sigma := by
    dsimp [a, sigma]
    exact one_sub_le_guardedScaleExponent hepsilon0 hepsilon_lt_one
  let D0 := C.rankBound ell
  let D := C.scaleDen ell
  let initialCost := initialUniformCost D0 D ell
  have hD : 0 < D := C.scaleDen_pos ell
  have hinitialCost : 0 < initialCost := initialUniformCost_pos hD
  obtain ⟨J, hJ⟩ := exists_nat_gt (beta / a)
  have hgap : beta < a * (J + 1 : ℕ) := by
    have hdiv : beta / a < (J : ℝ) := hJ
    have hbetaJ' : beta < (J : ℝ) * a := (div_lt_iff₀ ha0).mp hdiv
    have hbetaJ : beta < a * (J : ℝ) := by simpa [mul_comm] using hbetaJ'
    have hJle : (J : ℝ) ≤ (J + 1 : ℕ) := by exact_mod_cast (Nat.le_succ J)
    nlinarith
  let Q := D0 + J
  obtain ⟨coreLossThreshold, hcoreLossThreshold4, hcoreLoss⟩ :=
    exists_scaleSelector_loss_half_threshold_boundedDimension
      (exponent := sigma) C (max ell Q)
  have hcorePopulationEventually : ∀ᶠ m : ℕ in Filter.atTop,
      (coreLossThreshold : ℝ) ≤ Real.rpow (m : ℝ) a :=
    (nat_rpow_tendsto_atTop ha0).eventually_ge_atTop coreLossThreshold
  obtain ⟨corePopulationThreshold, hcorePopulation⟩ :=
    Filter.eventually_atTop.1 hcorePopulationEventually
  let pCost := uniformStepCost Q (scaleDenSum C Q)
  let changeCap := D0 + 2 * J
  let fixed := pCost ^ changeCap * initialCost
  have hpCost : 0 < pCost :=
    lt_of_lt_of_le zero_lt_one (one_le_uniformStepCost (scaleDenSum_pos C Q))
  have hfixed : 0 < fixed := mul_pos (pow_pos hpCost _) hinitialCost
  obtain ⟨K0, hK01, gapThreshold, hgapThreshold2, hgapThreshold⟩ :=
    exists_terminalGapAbsorption fixed beta tau changeCap hfixed htau1
  let constant := pCost ^ changeCap * initialCost
  have hconstant : 0 < constant := by
    dsimp [constant]
    exact mul_pos (pow_pos hpCost _) hinitialCost
  refine ⟨K0, hK01, constant, hconstant, ?_⟩
  intro kappa hkappa K hK
  have hKpos : 0 < K := lt_of_lt_of_le (by omega : 0 < K0) hK
  have hKreal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hsource : ∀ᶠ N : ℕ in atTop,
      Erdos186.delta kappa N ∈ Set.Ioo (0 : ℝ) 1 ∧
      Erdos186.gamma kappa (K : ℝ) N ∈ Set.Ioo (0 : ℝ) 1 ∧
      Real.rpow (N : ℝ) (-(1 / 3 : ℝ)) ≤
        Erdos186.gamma kappa (K : ℝ) N := by
    filter_upwards [Erdos186.eventually_delta_mem_Ioo hkappa,
      Erdos186.eventually_gamma_mem_Ioo hkappa hKreal,
      Erdos186.eventually_cubeRoot_inv_le_gamma kappa (K : ℝ)]
      with N hdeltaN hgammaN hlowerN
    exact ⟨hdeltaN, hgammaN, hlowerN⟩
  obtain ⟨sourceThreshold, hsourceThreshold⟩ := eventually_atTop.1 hsource
  have hcontextExponent : beta ≤ 2 * (beta + 1) := by linarith
  obtain ⟨scaleThreshold, hscaleThreshold2, hscaleInput⟩ :=
    exists_threshold_normalizedCanonicalEligibleInput C ell heta0 heta1
      hcontextExponent (ε := 1 - sigma) (sub_pos.mpr hsigma1) (by linarith)
  obtain ⟨jumpThreshold, hjumpThreshold2, hjumpThreshold⟩ :=
    exists_guarded_upwardJump_threshold (C := C)
      (selector := C.scaleSelector sigma)
      D0 J beta tau sigma initialCost hsigma0.le (hata ▸ ha0)
      (by simpa [hata] using hgap)
      C.scaleSelector_usesScaleExponent hinitialCost
  obtain ⟨closureThreshold, hclosureThreshold2, hclosure⟩ :=
    exists_terminalCandidateClosure_slowlyVarying_threshold C Q epsilon sigma
      kappa constant hbeta heta0 heta1 hepsilon0 hepsilon1 hsigma0 hsigma1
      hconstant
  let threshold := max scaleThreshold
    (max jumpThreshold
      (max gapThreshold
        (max closureThreshold (max corePopulationThreshold sourceThreshold))))
  refine ⟨threshold, le_max_of_le_left hscaleThreshold2, ?_⟩
  intro B A hcard hAB hbox hNA
  have hall : scaleThreshold ≤ A.card ∧ jumpThreshold ≤ A.card ∧
      gapThreshold ≤ A.card ∧ closureThreshold ≤ A.card ∧
      corePopulationThreshold ≤ A.card ∧ sourceThreshold ≤ A.card := by
    simpa only [threshold, max_le_iff] using hcard
  rcases hall with ⟨hscaleCard, hjumpCard, hgapCard, hclosureCard,
    hcorePopulationCard, hsourceCard⟩
  obtain ⟨hdeltaRange, hgammaRange, hgammaLower⟩ :=
    hsourceThreshold A.card hsourceCard
  let delta := Erdos186.delta kappa A.card
  let gamma := Erdos186.gamma kappa (K : ℝ) A.card
  have hdelta0 : 0 < delta := hdeltaRange.1
  have hdelta1 : delta < 1 := hdeltaRange.2
  have hdelta1le : delta ≤ 1 := hdelta1.le
  have hgamma0 : 0 < gamma := hgammaRange.1
  have hgamma1 : gamma ≤ 1 := hgammaRange.2.le
  have hgammaLt : gamma < 1 := hgammaRange.2
  have hgammaDelta : gamma ≤ delta ^ K := by
    dsimp only [gamma, delta]
    exact (by simp [Erdos186.gamma] :
      Erdos186.gamma kappa (K : ℝ) A.card =
        Erdos186.delta kappa A.card ^ K).le
  have hm2 : 2 ≤ A.card := hscaleThreshold2.trans hscaleCard
  have hmpos : 0 < A.card := by omega
  obtain ⟨I, _hIbox, _hIscale, _hIstrong, hnorm'⟩ :=
    hscaleInput B A hscaleCard hAB hbox
  have hexponent : 1 - (1 - sigma) = sigma := by ring
  rw [hexponent] at hnorm'
  let selector := C.scaleSelector sigma
  let initial : CoordinateReplacementState selector :=
    ⟨ell, normalizeSet B A, hnorm'⟩
  have hstrongSigma : selector.UsesScaleExponent sigma :=
    C.scaleSelector_usesScaleExponent
  have hstrongA : selector.UsesScaleExponent a :=
    C.scaleSelector_usesScaleExponent_of_le hasigma
  have hinitialRank : initial.selected.dimension ≤ D0 := by
    dsimp [initial, D0]
    exact (⟨ell, normalizeSet B A, hnorm'⟩ :
      CoordinateReplacementState selector).selected_dimension_le
  have hinitialDen : initial.selected.witness.scaleDen ≤ D := by
    have heq := initial.selected_scaleDen
    dsimp [initial, D] at heq ⊢
    omega
  have hinitialScale : Real.rpow (A.card : ℝ) a ≤
      (D : ℝ) * (initial.selected.dilation : ℝ) := by
    have hs := hstrongA (normalizeSet B A) hnorm'
    have hcardNorm : (normalizeSet B A).card = A.card := card_normalizeSet B A
    rw [hcardNorm] at hs
    have hscaleNat := initial.selected.witness.scale_lower
    have hscaleNum : initial.selected.witness.scaleNum = C.scaleNum ell := by
      dsimp [initial, CoordinateReplacementState.selected,
        BoundedCFPSelector.chosen]
      exact (selector.input (normalizeSet B A) hnorm').selectedCFP_scaleNum
    rw [hscaleNum] at hscaleNat
    have hnum : 1 ≤ C.scaleNum ell := C.scaleNum_pos ell
    have hscaleLe : (selector.input (normalizeSet B A) hnorm').scale ≤
        initial.selected.witness.scaleDen * initial.selected.dilation := by
      calc
        (selector.input (normalizeSet B A) hnorm').scale =
            1 * (selector.input (normalizeSet B A) hnorm').scale := by simp
        _ ≤ C.scaleNum ell *
              (selector.input (normalizeSet B A) hnorm').scale :=
          Nat.mul_le_mul_right _ hnum
        _ ≤ initial.selected.witness.scaleDen * initial.selected.dilation :=
          hscaleNat
    have hscaleD :
        (selector.input (normalizeSet B A) hnorm').scale ≤
          D * initial.selected.dilation :=
      hscaleLe.trans (Nat.mul_le_mul_right _ hinitialDen)
    exact hs.trans (by exact_mod_cast hscaleD)
  have hAne : A.Nonempty := Finset.card_pos.mp hmpos
  have hinitialBounds := initial_uniform_bounds_of_witness B hAne hAB
    initial.selected.witness hinitialRank hinitialDen hD hmpos hinitialScale
  have hinitialVolumePower :
      (initial.selected.progression.volume : ℝ) ≤
        initialCost * Real.rpow (A.card : ℝ) beta := by
    calc
      _ ≤ initialCost * (B.carrier.card : ℝ) := hinitialBounds.1
      _ ≤ initialCost * Real.rpow (A.card : ℝ) beta :=
        mul_le_mul_of_nonneg_left hbox hinitialCost.le
  have hjumpAll : ∀ {length : ℕ},
      (Tg : RelationTrace
        (GuardedCoordinateReplacement selector delta gamma
          (Real.rpow (A.card : ℝ) tau)) initial length) →
      coordinateUpwardJump Tg.forgetPopulationGuard length ≤ J :=
    hjumpThreshold hdelta0.le hgamma0.le hgamma1 A.card initial hjumpCard
      hinitialRank hinitialVolumePower
  have hinitialPopulation : Real.rpow (A.card : ℝ) tau <
      (initial.points.card : ℝ) := by
    have hmone : (1 : ℝ) < (A.card : ℝ) := by exact_mod_cast hm2
    have hr := Real.rpow_lt_rpow_of_exponent_lt hmone htau1
    simpa [initial, card_normalizeSet B A] using hr
  obtain ⟨L, Tg, hterminal, hjump, hfinalRank, hpopulationTau⟩ :=
    exists_quantitative_guarded_terminal_of_gamma_lt_one initial
      hdelta0.le hgamma0.le hgammaLt hmpos hsigma0.le
      (by rw [hata]; exact ha0.le)
      hstrongSigma hinitialRank hinitialPopulation hjumpAll
  have hgapAbsorb := hgapThreshold K hK A.card hgapCard
  have hirreducible : (Tg.state L).Irreducible delta gamma := by
    refine irreducible_of_quantitative_guarded_terminal
      (m := A.card) (L := L) (K := K) (D0 := D0) (J := J)
      (beta0 := beta) (tau := tau) (sigma := sigma)
      (initialCost := initialCost) initial Tg hterminal
      hdelta0 hdelta1le hgamma0 hgammaDelta hgammaLower hm2 hsigma0.le
      (by rw [hata]; exact ha0.le) hstrongSigma
      (card_normalizeSet B A) hinitialRank hinitialVolumePower hjump ?_
    · dsimp only
      change fixed * Real.rpow (A.card : ℝ)
        (beta - (K : ℝ) * (1 - tau) +
          (((changeCap + 1 : ℕ) : ℕ) : ℝ) / 3) < 1
      exact hgapAbsorb
  let T := Tg.forgetPopulationGuard
  have hterminalAmbient : (Tg.state L).ambientDimension ≤ max ell Q := by
    by_cases hL : L = 0
    · subst L
      rw [Tg.state_zero]
      exact le_max_left ell Q
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
      have hn : n < n + 1 := by omega
      change (T.state (n + 1)).ambientDimension ≤ max ell Q
      rw [T.ambientDimension_succ hn]
      have hselected : (T.state n).selected.dimension ≤ D0 + J := by
        have hzero : (T.state 0).selected.dimension =
            initial.selected.dimension := congrArg
          (fun V : CoordinateReplacementState selector ↦
            V.selected.dimension) T.state_zero
        calc
          (T.state n).selected.dimension ≤
              (T.state 0).selected.dimension + J :=
            T.selected_dimension_le_of_upwardJump_le (by omega) hjump
          _ = initial.selected.dimension + J := by rw [hzero]
          _ ≤ D0 + J := Nat.add_le_add_right hinitialRank J
      exact hselected.trans (le_max_right ell Q)
  let p := quantitativeMoveParameters C delta gamma A.card (tau * sigma) Q Q
    hdelta0.le hgamma0.le hgamma1 hmpos (by rw [hata]; exact ha0.le)
  let H : CoordinateTraceControl p T :=
    guardedTraceControl_of_jump_le_uniform Tg hdelta0.le
      hgamma0.le hgamma1 hmpos hsigma0.le
      (by rw [hata]; exact ha0.le) hstrongSigma
      hinitialRank hjump
  have hcases := quantitative_terminal_volume_cases T p H p.one_le_cost
    (by rfl) (by dsimp [p, quantitativeMoveParameters]; rw [hata])
    hdelta0 hdelta1le hgamma0 hgammaDelta hgammaLower
    hm2 ha23 hinitialCost.le (by positivity)
    (by change (normalizeSet B A).card = A.card; exact card_normalizeSet B A)
    hinitialRank
    hinitialBounds.1 hinitialBounds.2 hjump
  have hterminalState : T.state L = Tg.state L := rfl
  have hterminalConstant : p.cost ^ (D0 + 2 * J) * initialCost =
      constant := rfl
  have hpopulation : Real.rpow (A.card : ℝ) a <
      ((Tg.state L).points.card : ℝ) := by
    have hmone : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast (show 1 ≤ A.card by omega)
    have hat : a < tau := by dsimp [a, tau]; linarith
    exact (Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast (show 1 < A.card by omega)) hat).trans hpopulationTau
  have hcoreLossCard : coreLossThreshold ≤ (Tg.state L).points.card := by
    have hp := hcorePopulation A.card hcorePopulationCard
    have hlt : coreLossThreshold < (Tg.state L).points.card := by
      exact_mod_cast hp.trans_lt hpopulation
    omega
  have hcoreHalf : (1 / 2 : ℝ) * ((Tg.state L).points.card : ℝ) ≤
      ((Tg.state L).selected.identifiedCore.card : ℝ) := by
    change (1 / 2 : ℝ) * ((Tg.state L).points.card : ℝ) ≤
      (((C.scaleSelector sigma).chosen (Tg.state L).points
        (Tg.state L).eligible).identifiedCore.card : ℝ)
    exact scaleSelector_half_card_le_identifiedCore hcoreLoss
      hterminalAmbient (Tg.state L).points (Tg.state L).eligible hcoreLossCard
  have hcoarsePower : ((Tg.state L).selected.progression.volume : ℝ) ≤
      constant * Real.rpow (A.card : ℝ) beta := by
    have hc := hcases.1
    rw [hterminalState, hterminalConstant] at hc
    calc
      _ ≤ constant * (B.carrier.card : ℝ) := hc
      _ ≤ constant * Real.rpow (A.card : ℝ) beta :=
        mul_le_mul_of_nonneg_left hbox hconstant.le
  have hclosed : selector.CandidateClosedAt
      (Tg.state L).points (Tg.state L).eligible delta :=
    hclosure A.card (Tg.state L) hclosureCard hfinalRank
      (by simpa [a] using hpopulation) hcoarsePower
  have hguardReach := Tg.reflTransGen (le_refl L)
  have hreach : Relation.ReflTransGen (CoordinateReplacement selector delta gamma)
      initial (Tg.state L) := coordinateReachable_of_guardedReachable hguardReach
  refine ⟨selector, hnorm', ?_⟩
  have hstrongFinal : selector.UsesScaleExponent (1 - epsilon) := by
    change selector.UsesScaleExponent a
    exact hstrongA
  apply irreducibleReplacementResult_of_terminal
      (C := C) (selector := selector) (B := B) (A := A)
      (hA := hnorm') (ε := epsilon) (δ := delta) (γ := gamma)
      (K := K) (constant := constant)
    hstrongFinal hNA (Tg.state L) hreach hirreducible
      hclosed hcoreHalf (by simpa [a] using hpopulation)
  · intro hrank
    have hh := hcases.2.1 hrank
    have hsub : ((((Tg.state L).selected.dimension - ell : ℕ) : ℝ)) =
        ((Tg.state L).selected.dimension : ℝ) - (ell : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hrank)]
    rw [hterminalState, hterminalConstant, hsub] at hh
    exact hh
  · intro hrank
    have hh := hcases.2.2.1 hrank
    rw [hterminalState, hterminalConstant] at hh
    exact hh
  · intro hrank
    have hh := hcases.2.2.2 hrank
    rw [hterminalState, hterminalConstant] at hh
    exact hh

theorem exists_quantitative_terminal_frozenSlowlyVarying_exactSelector
    (ell : ℕ) (beta eta : ℝ)
    (C : HigherDimensionalContext (2 * (beta + 1)) eta)
    (hbeta : 1 < beta) (heta0 : 0 < eta) (heta1 : eta < 1)
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < (1 / 3 : ℝ))
    (p : ℝ) (hp : 0 < p) :
    ∃ K0 : ℕ, 1 ≤ K0 ∧
    ∃ constant : ℝ, 0 < constant ∧
      ∀ kappa : ℝ, 0 < kappa →
      ∀ K : ℕ, K0 ≤ K →
        ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ (initialCard : ℕ) (B : CFP.IntegerBox ell)
          (A : Finset (LatticePoint ell)),
          threshold ≤ initialCard →
          Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
          A.card ≤ initialCard →
          A ⊆ B.carrier →
          (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) beta →
          IsBoxNonaveraging A →
          ∃ hnorm : (C.scaleSelector (guardedScaleExponent epsilon)).Eligible
              (normalizeSet B A),
            Nonempty (IrreducibleReplacementResult
              (C.scaleSelector (guardedScaleExponent epsilon)) B A hnorm
              epsilon (Erdos186.delta kappa initialCard)
                (Erdos186.gamma kappa (K : ℝ) initialCard) K constant) := by
  let tau : ℝ := 1 - epsilon / 2
  let sigma : ℝ := guardedScaleExponent epsilon
  let a : ℝ := 1 - epsilon
  have hepsilon_lt_one : epsilon < 1 := hepsilon1.trans (by norm_num)
  have htau0 : 0 < tau := by dsimp [tau]; linarith
  have htau1 : tau < 1 := by dsimp [tau]; linarith
  have hsigma0 : 0 < sigma := guardedScaleExponent_pos hepsilon0 hepsilon_lt_one
  have hsigma1 : sigma < 1 := guardedScaleExponent_lt_one hepsilon0 hepsilon_lt_one
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha23 : (2 / 3 : ℝ) ≤ a := by dsimp [a]; linarith
  have hata : tau * sigma = a := by
    dsimp [tau, sigma, a]
    exact cutoff_mul_guardedScaleExponent (by linarith)
  have hasigma : a ≤ sigma := by
    dsimp [a, sigma]
    exact one_sub_le_guardedScaleExponent hepsilon0 hepsilon_lt_one
  let D0 := C.rankBound ell
  let D := C.scaleDen ell
  let initialCost := initialUniformCost D0 D ell
  have hD : 0 < D := C.scaleDen_pos ell
  have hinitialCost : 0 < initialCost := initialUniformCost_pos hD
  obtain ⟨J, hJ⟩ := exists_nat_gt (beta / a)
  have hgap : beta < a * (J + 1 : ℕ) := by
    have hdiv : beta / a < (J : ℝ) := hJ
    have hbetaJ' : beta < (J : ℝ) * a := (div_lt_iff₀ ha0).mp hdiv
    have hbetaJ : beta < a * (J : ℝ) := by simpa [mul_comm] using hbetaJ'
    have hJle : (J : ℝ) ≤ (J + 1 : ℕ) := by exact_mod_cast (Nat.le_succ J)
    nlinarith
  let Q := D0 + J
  obtain ⟨coreLossThreshold, hcoreLossThreshold4, hcoreLoss⟩ :=
    exists_scaleSelector_loss_half_threshold_boundedDimension
      (exponent := sigma) C (max ell Q)
  have hcorePopulationEventually : ∀ᶠ m : ℕ in Filter.atTop,
      (coreLossThreshold : ℝ) ≤ Real.rpow (m : ℝ) a :=
    (nat_rpow_tendsto_atTop ha0).eventually_ge_atTop coreLossThreshold
  obtain ⟨corePopulationThreshold, hcorePopulation⟩ :=
    Filter.eventually_atTop.1 hcorePopulationEventually
  let pCost := uniformStepCost Q (scaleDenSum C Q)
  let changeCap := D0 + 2 * J
  let fixed := pCost ^ changeCap * initialCost
  have hpCost : 0 < pCost :=
    lt_of_lt_of_le zero_lt_one (one_le_uniformStepCost (scaleDenSum_pos C Q))
  have hfixed : 0 < fixed := mul_pos (pow_pos hpCost _) hinitialCost
  obtain ⟨K0, hK01, gapThreshold, hgapThreshold2, hgapThreshold⟩ :=
    exists_terminalGapAbsorption fixed beta tau changeCap hfixed htau1
  let constant := pCost ^ changeCap * initialCost
  have hconstant : 0 < constant := by
    dsimp [constant]
    exact mul_pos (pow_pos hpCost _) hinitialCost
  refine ⟨K0, hK01, constant, hconstant, ?_⟩
  intro kappa hkappa K hK
  have hKpos : 0 < K := lt_of_lt_of_le (by omega : 0 < K0) hK
  have hKreal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hsource : ∀ᶠ N : ℕ in atTop,
      Erdos186.delta kappa N ∈ Set.Ioo (0 : ℝ) 1 ∧
      Erdos186.gamma kappa (K : ℝ) N ∈ Set.Ioo (0 : ℝ) 1 ∧
      Real.rpow (N : ℝ) (-(p / 3)) ≤
        Erdos186.gamma kappa (K : ℝ) N := by
    filter_upwards [Erdos186.eventually_delta_mem_Ioo hkappa,
      Erdos186.eventually_gamma_mem_Ioo hkappa hKreal,
      Erdos186.eventually_nat_rpow_neg_le_gamma kappa (K : ℝ)
        (show (0 : ℝ) < p / 3 by positivity)]
      with N hdeltaN hgammaN hlowerN
    exact ⟨hdeltaN, hgammaN, hlowerN⟩
  obtain ⟨sourceThreshold, hsourceThreshold⟩ := eventually_atTop.1 hsource
  have hcontextExponent : beta ≤ 2 * (beta + 1) := by linarith
  obtain ⟨scaleThreshold, hscaleThreshold2, hscaleInput⟩ :=
    exists_threshold_normalizedCanonicalEligibleInput C ell heta0 heta1
      hcontextExponent (ε := 1 - sigma) (sub_pos.mpr hsigma1) (by linarith)
  obtain ⟨jumpThreshold, hjumpThreshold2, hjumpThreshold⟩ :=
    exists_guarded_upwardJump_threshold (C := C)
      (selector := C.scaleSelector sigma)
      D0 J beta tau sigma initialCost hsigma0.le (hata ▸ ha0)
      (by simpa [hata] using hgap)
      C.scaleSelector_usesScaleExponent hinitialCost
  obtain ⟨closureThreshold, hclosureThreshold2, hclosure⟩ :=
    exists_terminalCandidateClosure_frozenSlowlyVarying_threshold C Q epsilon
      sigma kappa constant p hbeta heta0 heta1 hepsilon0 hepsilon1 hsigma0
      hsigma1 hconstant hp
  let currentThreshold := max scaleThreshold
    (max jumpThreshold (max gapThreshold corePopulationThreshold))
  have hcurrentEventually : ∀ᶠ N : ℕ in atTop,
      (currentThreshold : ℝ) ≤ Real.rpow (N : ℝ) p :=
    ((tendsto_rpow_atTop hp).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop currentThreshold
  obtain ⟨populationThreshold, hpopulationThreshold⟩ :=
    eventually_atTop.1 hcurrentEventually
  let threshold := max closureThreshold (max sourceThreshold populationThreshold)
  refine ⟨threshold, hclosureThreshold2.trans (le_max_left _ _), ?_⟩
  intro initialCard B A hinitial hpersistence hcurrentUpper hAB hbox hNA
  have hclosureCard : closureThreshold ≤ initialCard :=
    (le_max_left _ _).trans hinitial
  have hsourceCard : sourceThreshold ≤ initialCard :=
    (le_max_left sourceThreshold populationThreshold).trans
      ((le_max_right closureThreshold _).trans hinitial)
  have hpopulationCard : populationThreshold ≤ initialCard :=
    (le_max_right sourceThreshold populationThreshold).trans
      ((le_max_right closureThreshold _).trans hinitial)
  have hcurrentReal : (currentThreshold : ℝ) ≤ (A.card : ℝ) :=
    (hpopulationThreshold initialCard hpopulationCard).trans hpersistence
  have hcurrentNat : currentThreshold ≤ A.card := by exact_mod_cast hcurrentReal
  have hall : scaleThreshold ≤ A.card ∧ jumpThreshold ≤ A.card ∧
      gapThreshold ≤ A.card ∧ corePopulationThreshold ≤ A.card := by
    simpa only [currentThreshold, max_le_iff] using hcurrentNat
  rcases hall with ⟨hscaleCard, hjumpCard, hgapCard, hcorePopulationCard⟩
  obtain ⟨hdeltaRange, hgammaRange, hgammaLower⟩ :=
    hsourceThreshold initialCard hsourceCard
  let delta := Erdos186.delta kappa initialCard
  let gamma := Erdos186.gamma kappa (K : ℝ) initialCard
  have hdelta0 : 0 < delta := hdeltaRange.1
  have hdelta1 : delta < 1 := hdeltaRange.2
  have hdelta1le : delta ≤ 1 := hdelta1.le
  have hgamma0 : 0 < gamma := hgammaRange.1
  have hgamma1 : gamma ≤ 1 := hgammaRange.2.le
  have hgammaLt : gamma < 1 := hgammaRange.2
  have hgammaDelta : gamma ≤ delta ^ K := by
    dsimp only [gamma, delta]
    exact (by simp [Erdos186.gamma] :
      Erdos186.gamma kappa (K : ℝ) initialCard =
        Erdos186.delta kappa initialCard ^ K).le
  have hgammaLowerCurrent :
      Real.rpow (A.card : ℝ) (-(1 / 3 : ℝ)) ≤ gamma := by
    have hNpos : 0 < (initialCard : ℝ) := by
      have : 2 ≤ initialCard := hclosureThreshold2.trans hclosureCard
      exact_mod_cast (by omega : 0 < initialCard)
    calc
      Real.rpow (A.card : ℝ) (-(1 / 3 : ℝ)) ≤
          Real.rpow (Real.rpow (initialCard : ℝ) p)
            (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNpos p)
          hpersistence (by norm_num)
      _ = Real.rpow (initialCard : ℝ) (p * (-(1 / 3 : ℝ))) := by
        exact (Real.rpow_mul hNpos.le p (-(1 / 3 : ℝ))).symm
      _ = Real.rpow (initialCard : ℝ) (-(p / 3)) := by
        congr 1
        ring
      _ ≤ gamma := hgammaLower
  have hm2 : 2 ≤ A.card := hscaleThreshold2.trans hscaleCard
  have hmpos : 0 < A.card := by omega
  obtain ⟨I, _hIbox, _hIscale, _hIstrong, hnorm'⟩ :=
    hscaleInput B A hscaleCard hAB hbox
  have hexponent : 1 - (1 - sigma) = sigma := by ring
  rw [hexponent] at hnorm'
  let selector := C.scaleSelector sigma
  let initial : CoordinateReplacementState selector :=
    ⟨ell, normalizeSet B A, hnorm'⟩
  have hstrongSigma : selector.UsesScaleExponent sigma :=
    C.scaleSelector_usesScaleExponent
  have hstrongA : selector.UsesScaleExponent a :=
    C.scaleSelector_usesScaleExponent_of_le hasigma
  have hinitialRank : initial.selected.dimension ≤ D0 := by
    dsimp [initial, D0]
    exact (⟨ell, normalizeSet B A, hnorm'⟩ :
      CoordinateReplacementState selector).selected_dimension_le
  have hinitialDen : initial.selected.witness.scaleDen ≤ D := by
    have heq := initial.selected_scaleDen
    dsimp [initial, D] at heq ⊢
    omega
  have hinitialScale : Real.rpow (A.card : ℝ) a ≤
      (D : ℝ) * (initial.selected.dilation : ℝ) := by
    have hs := hstrongA (normalizeSet B A) hnorm'
    have hcardNorm : (normalizeSet B A).card = A.card := card_normalizeSet B A
    rw [hcardNorm] at hs
    have hscaleNat := initial.selected.witness.scale_lower
    have hscaleNum : initial.selected.witness.scaleNum = C.scaleNum ell := by
      dsimp [initial, CoordinateReplacementState.selected,
        BoundedCFPSelector.chosen]
      exact (selector.input (normalizeSet B A) hnorm').selectedCFP_scaleNum
    rw [hscaleNum] at hscaleNat
    have hnum : 1 ≤ C.scaleNum ell := C.scaleNum_pos ell
    have hscaleLe : (selector.input (normalizeSet B A) hnorm').scale ≤
        initial.selected.witness.scaleDen * initial.selected.dilation := by
      calc
        (selector.input (normalizeSet B A) hnorm').scale =
            1 * (selector.input (normalizeSet B A) hnorm').scale := by simp
        _ ≤ C.scaleNum ell *
              (selector.input (normalizeSet B A) hnorm').scale :=
          Nat.mul_le_mul_right _ hnum
        _ ≤ initial.selected.witness.scaleDen * initial.selected.dilation :=
          hscaleNat
    have hscaleD :
        (selector.input (normalizeSet B A) hnorm').scale ≤
          D * initial.selected.dilation :=
      hscaleLe.trans (Nat.mul_le_mul_right _ hinitialDen)
    exact hs.trans (by exact_mod_cast hscaleD)
  have hAne : A.Nonempty := Finset.card_pos.mp hmpos
  have hinitialBounds := initial_uniform_bounds_of_witness B hAne hAB
    initial.selected.witness hinitialRank hinitialDen hD hmpos hinitialScale
  have hinitialVolumePower :
      (initial.selected.progression.volume : ℝ) ≤
        initialCost * Real.rpow (A.card : ℝ) beta := by
    calc
      _ ≤ initialCost * (B.carrier.card : ℝ) := hinitialBounds.1
      _ ≤ initialCost * Real.rpow (A.card : ℝ) beta :=
        mul_le_mul_of_nonneg_left hbox hinitialCost.le
  have hjumpAll : ∀ {length : ℕ},
      (Tg : RelationTrace
        (GuardedCoordinateReplacement selector delta gamma
          (Real.rpow (A.card : ℝ) tau)) initial length) →
      coordinateUpwardJump Tg.forgetPopulationGuard length ≤ J :=
    hjumpThreshold hdelta0.le hgamma0.le hgamma1 A.card initial hjumpCard
      hinitialRank hinitialVolumePower
  have hinitialPopulation : Real.rpow (A.card : ℝ) tau <
      (initial.points.card : ℝ) := by
    have hmone : (1 : ℝ) < (A.card : ℝ) := by exact_mod_cast hm2
    have hr := Real.rpow_lt_rpow_of_exponent_lt hmone htau1
    simpa [initial, card_normalizeSet B A] using hr
  obtain ⟨L, Tg, hterminal, hjump, hfinalRank, hpopulationTau⟩ :=
    exists_quantitative_guarded_terminal_of_gamma_lt_one initial
      hdelta0.le hgamma0.le hgammaLt hmpos hsigma0.le
      (by rw [hata]; exact ha0.le)
      hstrongSigma hinitialRank hinitialPopulation hjumpAll
  have hgapAbsorb := hgapThreshold K hK A.card hgapCard
  have hirreducible : (Tg.state L).Irreducible delta gamma := by
    refine irreducible_of_quantitative_guarded_terminal
      (m := A.card) (L := L) (K := K) (D0 := D0) (J := J)
      (beta0 := beta) (tau := tau) (sigma := sigma)
      (initialCost := initialCost) initial Tg hterminal
      hdelta0 hdelta1le hgamma0 hgammaDelta hgammaLowerCurrent hm2 hsigma0.le
      (by rw [hata]; exact ha0.le) hstrongSigma
      (card_normalizeSet B A) hinitialRank hinitialVolumePower hjump ?_
    · dsimp only
      change fixed * Real.rpow (A.card : ℝ)
        (beta - (K : ℝ) * (1 - tau) +
          (((changeCap + 1 : ℕ) : ℕ) : ℝ) / 3) < 1
      exact hgapAbsorb
  let T := Tg.forgetPopulationGuard
  have hterminalAmbient : (Tg.state L).ambientDimension ≤ max ell Q := by
    by_cases hL : L = 0
    · subst L
      rw [Tg.state_zero]
      exact le_max_left ell Q
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
      have hn : n < n + 1 := by omega
      change (T.state (n + 1)).ambientDimension ≤ max ell Q
      rw [T.ambientDimension_succ hn]
      have hselected : (T.state n).selected.dimension ≤ D0 + J := by
        have hzero : (T.state 0).selected.dimension =
            initial.selected.dimension := congrArg
          (fun V : CoordinateReplacementState selector ↦
            V.selected.dimension) T.state_zero
        calc
          (T.state n).selected.dimension ≤
              (T.state 0).selected.dimension + J :=
            T.selected_dimension_le_of_upwardJump_le (by omega) hjump
          _ = initial.selected.dimension + J := by rw [hzero]
          _ ≤ D0 + J := Nat.add_le_add_right hinitialRank J
      exact hselected.trans (le_max_right ell Q)
  let p := quantitativeMoveParameters C delta gamma A.card (tau * sigma) Q Q
    hdelta0.le hgamma0.le hgamma1 hmpos (by rw [hata]; exact ha0.le)
  let H : CoordinateTraceControl p T :=
    guardedTraceControl_of_jump_le_uniform Tg hdelta0.le
      hgamma0.le hgamma1 hmpos hsigma0.le
      (by rw [hata]; exact ha0.le) hstrongSigma
      hinitialRank hjump
  have hcases := quantitative_terminal_volume_cases T p H p.one_le_cost
    (by rfl) (by dsimp [p, quantitativeMoveParameters]; rw [hata])
    hdelta0 hdelta1le hgamma0 hgammaDelta hgammaLowerCurrent
    hm2 ha23 hinitialCost.le (by positivity)
    (by change (normalizeSet B A).card = A.card; exact card_normalizeSet B A)
    hinitialRank
    hinitialBounds.1 hinitialBounds.2 hjump
  have hterminalState : T.state L = Tg.state L := rfl
  have hterminalConstant : p.cost ^ (D0 + 2 * J) * initialCost =
      constant := rfl
  have hpopulation : Real.rpow (A.card : ℝ) a <
      ((Tg.state L).points.card : ℝ) := by
    have hmone : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast (show 1 ≤ A.card by omega)
    have hat : a < tau := by dsimp [a, tau]; linarith
    exact (Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast (show 1 < A.card by omega)) hat).trans hpopulationTau
  have hcoreLossCard : coreLossThreshold ≤ (Tg.state L).points.card := by
    have hp := hcorePopulation A.card hcorePopulationCard
    have hlt : coreLossThreshold < (Tg.state L).points.card := by
      exact_mod_cast hp.trans_lt hpopulation
    omega
  have hcoreHalf : (1 / 2 : ℝ) * ((Tg.state L).points.card : ℝ) ≤
      ((Tg.state L).selected.identifiedCore.card : ℝ) := by
    change (1 / 2 : ℝ) * ((Tg.state L).points.card : ℝ) ≤
      (((C.scaleSelector sigma).chosen (Tg.state L).points
        (Tg.state L).eligible).identifiedCore.card : ℝ)
    exact scaleSelector_half_card_le_identifiedCore hcoreLoss
      hterminalAmbient (Tg.state L).points (Tg.state L).eligible hcoreLossCard
  have hcoarsePower : ((Tg.state L).selected.progression.volume : ℝ) ≤
      constant * Real.rpow (A.card : ℝ) beta := by
    have hc := hcases.1
    rw [hterminalState, hterminalConstant] at hc
    calc
      _ ≤ constant * (B.carrier.card : ℝ) := hc
      _ ≤ constant * Real.rpow (A.card : ℝ) beta :=
        mul_le_mul_of_nonneg_left hbox hconstant.le
  have hclosed : selector.CandidateClosedAt
      (Tg.state L).points (Tg.state L).eligible delta :=
    hclosure initialCard A.card (Tg.state L) hclosureCard hpersistence
      hfinalRank (by simpa [a] using hpopulation) hcoarsePower
  have hguardReach := Tg.reflTransGen (le_refl L)
  have hreach : Relation.ReflTransGen (CoordinateReplacement selector delta gamma)
      initial (Tg.state L) := coordinateReachable_of_guardedReachable hguardReach
  change ∃ hnorm : selector.Eligible (normalizeSet B A),
    Nonempty (IrreducibleReplacementResult selector B A hnorm
      epsilon delta gamma K constant)
  refine ⟨hnorm', ?_⟩
  have hstrongFinal : selector.UsesScaleExponent (1 - epsilon) := by
    change selector.UsesScaleExponent a
    exact hstrongA
  apply irreducibleReplacementResult_of_terminal
      (C := C) (selector := selector) (B := B) (A := A)
      (hA := hnorm') (ε := epsilon) (δ := delta) (γ := gamma)
      (K := K) (constant := constant)
    hstrongFinal hNA (Tg.state L) hreach hirreducible
      hclosed hcoreHalf (by simpa [a] using hpopulation)
  · intro hrank
    have hh := hcases.2.1 hrank
    have hsub : ((((Tg.state L).selected.dimension - ell : ℕ) : ℝ)) =
        ((Tg.state L).selected.dimension : ℝ) - (ell : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hrank)]
    rw [hterminalState, hterminalConstant, hsub] at hh
    exact hh
  · intro hrank
    have hh := hcases.2.2.1 hrank
    rw [hterminalState, hterminalConstant] at hh
    exact hh
  · intro hrank
    have hh := hcases.2.2.2 hrank
    rw [hterminalState, hterminalConstant] at hh
    exact hh

theorem exists_quantitative_terminal_frozenSlowlyVarying
    (ell : ℕ) (beta eta : ℝ)
    (C : HigherDimensionalContext (2 * (beta + 1)) eta)
    (hbeta : 1 < beta) (heta0 : 0 < eta) (heta1 : eta < 1)
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < (1 / 3 : ℝ))
    (p : ℝ) (hp : 0 < p) :
    ∃ K0 : ℕ, 1 ≤ K0 ∧
    ∃ constant : ℝ, 0 < constant ∧
      ∀ kappa : ℝ, 0 < kappa →
      ∀ K : ℕ, K0 ≤ K →
        ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ (initialCard : ℕ) (B : CFP.IntegerBox ell)
          (A : Finset (LatticePoint ell)),
          threshold ≤ initialCard →
          Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
          A.card ≤ initialCard →
          A ⊆ B.carrier →
          (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) beta →
          IsBoxNonaveraging A →
          ∃ selector : BoundedCFPSelector C,
          ∃ hnorm : selector.Eligible (normalizeSet B A),
            Nonempty (IrreducibleReplacementResult selector B A hnorm
              epsilon (Erdos186.delta kappa initialCard)
                (Erdos186.gamma kappa (K : ℝ) initialCard) K constant) := by
  obtain ⟨K0, hK0, constant, hconstant, hterminal⟩ :=
    exists_quantitative_terminal_frozenSlowlyVarying_exactSelector ell beta eta C
      hbeta heta0 heta1 epsilon hepsilon0 hepsilon1 p hp
  refine ⟨K0, hK0, constant, hconstant, ?_⟩
  intro kappa hkappa K hK
  obtain ⟨threshold, hthreshold, hterminal'⟩ := hterminal kappa hkappa K hK
  refine ⟨threshold, hthreshold, ?_⟩
  intro initialCard B A hinitial hpersistence hcurrent hAB hbox hNA
  obtain ⟨hnorm, hresult⟩ := hterminal' initialCard B A hinitial hpersistence
    hcurrent hAB hbox hNA
  exact ⟨C.scaleSelector (guardedScaleExponent epsilon), hnorm, hresult⟩


end

end Erdos186.PZ.Reduction
