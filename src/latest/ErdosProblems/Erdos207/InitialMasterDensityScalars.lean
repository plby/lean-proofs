/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPatternAnalyticData
import ErdosProblems.Erdos207.CrossScaleRegularizationScalars
import ErdosProblems.Erdos207.InitialPowerCoupledRegularity
import ErdosProblems.Erdos207.PowerSourceWellSpread

/-! # Actual initial master densities have a fixed positive availability floor -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceMasterEtaFloor (q : ℕ) : ℝ≥0 :=
  Real.toNNReal (Real.exp (-∑ d ∈ ksssOrders q, initialErdosCoefficientBound q d))

theorem sourceMasterEtaFloor_pos (q : ℕ) : 0 < sourceMasterEtaFloor q := by
  exact Real.toNNReal_pos.mpr (Real.exp_pos _)

theorem sourceMasterEtaFloor_le_one (q : ℕ) : sourceMasterEtaFloor q ≤ 1 := by
  apply Real.toNNReal_le_iff_le_coe.mpr
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  exact sum_nonneg (fun _ _ ↦ by unfold initialErdosCoefficientBound; positivity)

theorem initial_master_density_scalars
    {V : Type*} [Fintype V] [DecidableEq V]
    (q C b t : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (bank : TripleSystemOn V)
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    (hlarge : 6 * C + 4 ≤ Fintype.card V) (ht : 1 ≤ t)
    (hmass : 3 * (t : ℝ) ^ b ≤ (initialResidualPairs H).card) :
    let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
      (outsideAvailableTriangles H bank)
    let E : ℝ := (initialResidualPairs H).card
    let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
    let p := Real.toNNReal (ksssEdgeDensity E time)
    let eta := Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
      (initialErdosTrajectoryCoefficient V (S₀.available.card : ℝ)) time))
    1 / (t : ℝ≥0) ^ b ≤ p ∧ p ≤ 2 / (t : ℝ≥0) ^ b ∧ p ≤ 1 ∧
      sourceMasterEtaFloor q ≤ eta ∧ eta ≤ 1 := by
  dsimp only
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
    (outsideAvailableTriangles H bank)
  let E : ℝ := (initialResidualPairs H).card
  let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
  let a := initialErdosTrajectoryCoefficient V (S₀.available.card : ℝ)
  have hdata := initial_absorber_pattern_analytic_data q C H bank hdegree hsupport hlarge
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le htR
  have htime := ksssDensityHorizon_bounds E (1 / (t : ℝ) ^ b) hdata.1 (by positivity)
    ((div_le_one (pow_pos ht0 b)).mpr (one_le_pow₀ htR))
  have hpoisson : ksssPoissonExponent (ksssOrders q) a time ≤
      ∑ d ∈ ksssOrders q, initialErdosCoefficientBound q d :=
    ksssPoissonExponent_le_sum _ _ _ hdata.2.2.1 hdata.2.2.2 (Nat.cast_nonneg _) htime.1
  have hpoisson0 : 0 ≤ ksssPoissonExponent (ksssOrders q) a time :=
    ksssPoissonExponent_nonneg _ _ hdata.2.2.1 (Nat.cast_nonneg _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply NNReal.le_toNNReal_of_coe_le
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_natCast] using
      htime.2.1 time le_rfl
  · apply Real.toNNReal_le_iff_le_coe.mpr
    simpa only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_pow, NNReal.coe_natCast] using
      ksssDensityHorizon_survival_upper E t b hdata.1 htR hmass
  · exact Real.toNNReal_le_iff_le_coe.mpr (ksssEdgeDensity_le_one hdata.1 (Nat.cast_nonneg _))
  · apply Real.toNNReal_le_toNNReal
    exact Real.exp_le_exp.mpr (neg_le_neg hpoisson)
  · exact Real.toNNReal_le_iff_le_coe.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hpoisson0))

theorem initialSupportPower_le_bankSubsetExponent (q rootPower : ℕ) (hq : 1 ≤ q) :
    initialSupportPower rootPower ≤ powerBankSubsetExponent q rootPower := by
  unfold initialSupportPower powerBankSubsetExponent
  nlinarith only [Nat.mul_le_mul_left (156*rootPower) hq]

theorem InitialPowerVortexPackage.initial_master_density_scalars
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (b R : ℕ) (ht : 48 ≤ t) (hc : powerAbsorberCoefficient q ≤ t)
    (hscale : t^R ≤ n) (hsupportGap : initialSupportPower rootPower+1 ≤ R)
    (hdensityGap : b+1 ≤ R) :
    let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B)
      (outsideAvailableTriangles P.H P.B)
    let E : ℝ := (initialResidualPairs P.H).card
    let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
    let p := Real.toNNReal (ksssEdgeDensity E time)
    let eta := Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
      (initialErdosTrajectoryCoefficient (Fin n) (S₀.available.card : ℝ)) time))
    1 / (t : ℝ≥0) ^ b ≤ p ∧ p ≤ 2 / (t : ℝ≥0) ^ b ∧ p ≤ 1 ∧
      sourceMasterEtaFloor q ≤ eta ∧ eta ≤ 1 := by
  have htR : (48 : ℝ) ≤ t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hscaleR : (t : ℝ)^R ≤ n := by exact_mod_cast hscale
  obtain ⟨hdegree, _hgraph, hbank⟩ := P.support_power_bounds hc
  have hlarge : 6*t^initialSupportPower rootPower+4 ≤ Fintype.card (Fin n) := by
    have hbound := (initial_support_density_power (t : ℝ) (initialSupportPower rootPower)
      (by linarith)).trans ((pow_le_pow_right₀ ht1 hsupportGap).trans hscaleR)
    simpa only [Fintype.card_fin] using (show 6*t^initialSupportPower rootPower+4 ≤ n by exact_mod_cast hbound)
  have hmass : 3*(t : ℝ)^b ≤ (initialResidualPairs P.H).card := by
    have hN1 : (1 : ℝ) ≤ n := (one_le_pow₀ ht1).trans hscaleR
    have hN : 48*(t : ℝ)^b ≤ n := by
      calc
        _ ≤ (t : ℝ)*(t : ℝ)^b := mul_le_mul_of_nonneg_right htR (pow_nonneg (by positivity) _)
        _ = (t : ℝ)^(b+1) := by rw [pow_succ]; ring
        _ ≤ _ := (pow_le_pow_right₀ ht1 hdensityGap).trans hscaleR
    have hdensity := initialResidualPairs_density_lower (q := q) hdegree hbank hlarge
    simp only [Fintype.card_fin] at hdensity
    nlinarith only [hN1, hN, hdensity]
  exact Erdos207.initial_master_density_scalars q (t^initialSupportPower rootPower) b t
    P.H P.B hdegree hbank hlarge (by omega) hmass

end

end Erdos207
