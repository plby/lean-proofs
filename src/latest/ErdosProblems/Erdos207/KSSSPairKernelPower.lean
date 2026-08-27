/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSOneStepPowerBounds
import ErdosProblems.Erdos207.KSSSStateSelectorPower
import ErdosProblems.Erdos207.KSSSDiscreteSupermartingale
import ErdosProblems.Erdos207.KSSSDeterministicIncrementPower
import ErdosProblems.Erdos207.DyadicPairJumpVariance
import ErdosProblems.Erdos207.CenteredPowerBounds

/-! # All centered pair kernel estimates from the actual active-state conditions -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSOnTrajectories.pair_oneStep_power
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B k t : ℕ}
    {Q : Finset (Finset V)} {a coeff : ℕ → ℝ} {E A time sigma : ℝ}
    (h : KSSSOnTrajectories F S q Q a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time (Fintype.card V) t)
    (hcrude : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hN : 1 ≤ (Fintype.card V : ℝ))
    (hratio : A / E ≤ (Fintype.card V : ℝ))
    (ht : 32 ≤ t) (hsigma : |sigma| = 1)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t)
    (hB : ksssPairDriftCoefficient q coeff + ksssPairTaylorCoefficient (ksssOrders q) coeff ≤
      3 * (B : ℝ)) (P : PairOn V) (hP : P.1 ∈ Q) :
    KSSSOneStepPowerBounds F S (.inl P : KSSSTrajectoryIndex V q) a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B sigma time
      (Fintype.card V) t b k := by
  let N : ℝ := Fintype.card V
  let scale := N / (t : ℝ) ^ ksssPowerErrorExponent b B
  let X := fun S' : GreedyStateOn V ↦ ((availableTrianglesContainingPair S' P.1).card : ℝ) -
    (availableTrianglesContainingPair S P.1).card
  let df := ksssPairTrajectory (ksssOrders q) a E A (time + 1) -
    ksssPairTrajectory (ksssOrders q) a E A time
  let de := ksssErrorEnvelope E scale B (time + 1) - ksssErrorEnvelope E scale B time
  let R := S.available \ availableTrianglesContainingPair S P.1
  let D := ksssPairDriftCoefficient q coeff
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast (show 2 ≤ t by omega)
  have ht6 : (6 : ℝ) ≤ t := by exact_mod_cast (show 6 ≤ t by omega)
  have htpos : (0 : ℝ) < t := by linarith
  have hNpos : 0 < N := by dsimp only [N]; linarith
  have hs : 0 ≤ scale := by dsimp only [scale]; positivity
  have hb : ∀ d ∈ ksssOrders q, 0 ≤ coeff d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hC := ksssThreatCoefficient_nonneg (ksssOrders q) coeff hb
  have hD : 0 ≤ D := by dsimp only [D, ksssPairDriftCoefficient]; positivity
  have horders : ∀ d ∈ ksssOrders q, 1 ≤ d := fun d hd ↦ (mem_Icc.mp hd).1
  have hcommon : ((dyadicCrudeThresholds V t k).common : ℝ) ≤
      ksssErrorEnvelope E scale B time := by
    change (t : ℝ) ^ k ≤ _
    exact (pow_le_pow_right₀ ht1 (Nat.le_succ k)).trans hscalar.overlap_error
  have hlarge : 24 ≤ E * ksssEdgeDensity E time := by
    have ht32 : (32 : ℝ) ≤ t := by exact_mod_cast ht
    linarith [hscalar.clock_base]
  have hraw (hR : R.Nonempty) :
      |(restrictedGreedyKernel F S R hR).expectationReal X -
        ksssPairSlope (ksssOrders q) a E A time| ≤
          D * ksssErrorEnvelope E scale B time / (E * ksssEdgeDensity E time) :=
    h.pair_drift_error hcrude hS hpack hcard hQ hcover hQcard hE hA htime
      hscalar.clock_strict ha hab hscalar.error_two hscalar.error_small hcommon hlarge
      hscalar.pair_clock_error P.1 hP hR
  have hloss := ksss_pair_slope_error_power (ksssOrders q) a coeff E A scale time N t D B b
    hE hA htime hscalar.clock_strict horders ha hab hNpos htpos hD hratio
    hscalar.error_small hscalar.clock_lower hcoeff.pair
  have hslopeSmall : |ksssPairSlope (ksssOrders q) a E A time| ≤ 1 / N * (t : ℝ) ^ (2 * b + 1) := by
    have hp := ksssEdgeDensity_pos hE hscalar.clock_strict
    have he : 0 ≤ ksssErrorEnvelope E scale B time := by unfold ksssErrorEnvelope; positivity
    have herror : 0 ≤ D * ksssErrorEnvelope E scale B time / (E * ksssEdgeDensity E time) :=
      div_nonneg (mul_nonneg hD he) (mul_nonneg hE.le hp.le)
    linarith only [hloss, herror]
  have hslope : |ksssPairSlope (ksssOrders q) a E A time| ≤
      1 / N * (t : ℝ) ^ (5 * b + 6) := hslopeSmall.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hdet : |df| + |de| ≤ 1 / N * (t : ℝ) ^ (5 * b + 7) :=
    ksss_pair_deterministic_increment_power (ksssOrders q) a coeff E A scale time N t B b
      hE hA.le hs htime hscalar.unit_clock hscalar.taylor_size horders ha hab hNpos ht6
      hratio hscalar.error_small hscalar.clock_lower hcoeff.pairTaylor hcoeff.envelope hslope
  have hid (S' : GreedyStateOn V) :
      ksssCenteredTrajectoryObservable F a E A scale B sigma (time + 1) S' (.inl P : KSSSTrajectoryIndex V q) -
        ksssCenteredTrajectoryObservable F a E A scale B sigma time S (.inl P : KSSSTrajectoryIndex V q) =
          sigma * (X S' - df) - de := by
    rw [ksssCenteredTrajectoryObservable_increment]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    have hjump := hcrude.dyadic_pair_jump P hS hpack (show 16 ≤ t by omega) hT
    have hrawJump : |X (greedyStep F S T)| ≤ N ^ 0 * (t : ℝ) ^ (k + 2) := by
      simp only [pow_zero, one_mul]
      exact hjump.trans (pow_le_pow_right₀ ht1 (by omega))
    have hbound := centered_step_abs_power N t sigma (X (greedyStep F S T)) df de
      0 (k + 2) (5 * b + 7) hN ht2 hsigma hrawJump (by simpa only [pow_zero] using hdet)
    simpa only [← hid, ksssTrajectoryDimension, ksssPowerJumpExponent,
      ksssPowerDeterministicExponent] using hbound
  · intro hR
    have hbound := ksss_pair_centered_step_drift_nonpos (restrictedGreedyKernel F S R hR) X
      (ksssOrders q) a coeff E A scale time sigma D B hsigma hE hA.le hs htime
      (by linarith [hscalar.unit_clock]) hscalar.taylor_size horders ha hab (hraw hR) hB
    change (restrictedGreedyKernel F S R hR).expectationReal
      (fun S' ↦ sigma * (X S' - df) - de) ≤ 0 at hbound
    simpa only [← hid, ksssTrajectorySelectors, R, N, scale] using hbound
  · intro hR
    have hvariance := hcrude.dyadic_pair_variance P hS hpack (show 16 ≤ t by omega) hR
      (ksssPairSlope (ksssOrders q) a E A time)
      (D * ksssErrorEnvelope E scale B time / (E * ksssEdgeDensity E time)) (hraw hR) hloss
    have hrawSecond : (restrictedGreedyKernel F S R hR).expectationReal (fun S' ↦ X S' ^ 2) ≤
        N ^ (2 * 0) / N * (t : ℝ) ^ (k + 5 * b + 8) := by
      simp only [mul_zero, pow_zero]
      exact hvariance.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
    have hbound := centered_step_secondMoment_power (restrictedGreedyKernel F S R hR) X
      N t sigma df de 0 (k + 5 * b + 8) (5 * b + 7) hN ht2 hsigma hrawSecond
      (by simpa only [pow_zero] using hdet)
    simpa only [← hid, ksssTrajectorySelectors, R, N, scale,
      ksssTrajectoryDimension, ksssPowerVarianceExponent,
      ksssPowerRawVarianceExponent, ksssPowerDeterministicExponent] using hbound

end

end Erdos207
