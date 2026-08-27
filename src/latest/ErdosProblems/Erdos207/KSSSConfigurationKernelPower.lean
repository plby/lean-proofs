/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationPowerDrift
import ErdosProblems.Erdos207.KSSSConfigurationRawPower
import ErdosProblems.Erdos207.KSSSDiscreteSupermartingale
import ErdosProblems.Erdos207.CenteredPowerBounds

/-! # All centered configuration estimates from the actual active-state conditions -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSOnTrajectories.configuration_oneStep_power
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B k t Rmin : ℕ}
    {Q : Finset (Finset V)} {a coeff : ℕ → ℝ} {E A time sigma : ℝ}
    (h : KSSSOnTrajectories F S q Q a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time (Fintype.card V) t)
    (hcrude : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (hminimal : minimalForbiddenFamily F = F)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    (hcard : ∀ D ∈ F, 2 ≤ D.card → D.card + 2 ≤ q)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E * ksssEdgeDensity E time)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hN : 1 ≤ Fintype.card V)
    (hratioUpper : A / E ≤ (Fintype.card V : ℝ))
    (ht : 32 ≤ t) (hconst : 2 ^ q ≤ t) (hqt : q ≤ t) (hsigma : |sigma| = 1)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ Fintype.card V)
    (hfloor : 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E time)
    (hratio : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤ A / E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t) (hB : 4 * q ≤ B)
    (hbudget : ∀ i : CrudeOrderIndex q 4, ksssIndexedConfigurationDriftCoefficient q coeff i +
      ksssConfigurationTaylorCoefficient (ksssOrders q) coeff (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2)
    (i : CrudeOrderIndex q 4) {root : TripleOn V} (hroot : root ∈ S.available) :
    KSSSOneStepPowerBounds F S (.inr (i, root) : KSSSTrajectoryIndex V q) a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B sigma time
      (Fintype.card V) t b k := by
  let N : ℝ := Fintype.card V
  let scale := N / (t : ℝ) ^ ksssPowerErrorExponent b B
  let index : KSSSTrajectoryIndex V q := .inr (i, root)
  let z := i.order - 3 - i.chosen - 1
  let R := S.available \ greedyClosedThreats F S root
  let X := fun S' : GreedyStateOn V ↦ ksssTrajectoryValue F S' index - ksssTrajectoryValue F S index
  let df := ksssConfigurationTrajectory (ksssOrders q) a E A (i.order - 3) i.chosen (time + 1) -
    ksssConfigurationTrajectory (ksssOrders q) a E A (i.order - 3) i.chosen time
  let de := ksssConfigurationErrorEnvelope E A scale B z (time + 1) -
    ksssConfigurationErrorEnvelope E A scale B z time
  have hN1 : (1 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast hN
  have hNpos : 0 < N := by linarith
  have ht6 : (6 : ℝ) ≤ t := by exact_mod_cast (show 6 ≤ t by omega)
  have hs : 0 ≤ scale := by dsimp only [scale]; positivity
  have hc := i.budget
  have hj := i.order_le
  have hd : i.order - 3 ∈ ksssOrders q := by simp only [ksssOrders, mem_Icc]; omega
  have hz : i.order - 4 - i.chosen = z := by dsimp only [z]; omega
  have hdim : ksssTrajectoryDimension index = z := hz
  have horders : ∀ d ∈ ksssOrders q, 1 ≤ d := fun d hd ↦ (mem_Icc.mp hd).1
  have hslope := ksss_configuration_slope_power_of_coefficients q b B k a coeff E A time N t
    hscalar hE hA htime hNpos ht6 (by exact_mod_cast hqt) hratioUpper ha hab hcoeff i
  have hdet : |df| + |de| ≤ N ^ z / N * (t : ℝ) ^ (5 * b + 7) :=
    ksss_configuration_deterministic_increment_power (ksssOrders q) a coeff E A scale time N t B
      (i.order - 3) i.chosen b hE hA.le hs htime hscalar.unit_clock hscalar.taylor_size
      horders ha hab hd (by omega) (by omega) hNpos ht6 hratioUpper hscalar.error_small
      hscalar.clock_lower (hcoeff.configuration i).2 hcoeff.envelope hslope
  have hraw := h.configuration_raw_power hscalar hcrude hS hpack hcard hQ hcover hQcard
    hE hA htime hN hratioUpper ht hconst hqt ha hab hcoeff i hroot
  have hid (S' : GreedyStateOn V) :
      ksssCenteredTrajectoryObservable F a E A scale B sigma (time + 1) S' index -
        ksssCenteredTrajectoryObservable F a E A scale B sigma time S index =
          sigma * (X S' - df) - de := by
    rw [ksssCenteredTrajectoryObservable_increment]
    simp only [index, ksssTrajectoryTarget, ksssTrajectoryError, hz]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    have hrawJump : |X (greedyStep F S T)| ≤ N ^ z * (t : ℝ) ^ (k + 2) := by
      simpa only [ksssTrajectoryDimension, hz] using hraw.1 T hT
    have hbound := centered_step_abs_power N t sigma (X (greedyStep F S T)) df de z
      (k + 2) (5 * b + 7) hN1 (by linarith) hsigma hrawJump hdet
    simpa only [← hid, index, ksssTrajectoryDimension, hz, ksssPowerJumpExponent,
      ksssPowerDeterministicExponent] using hbound
  · intro hR
    have hmean := h.configuration_power_drift hscalar hcrude hminimal hS hpack hcard hQ hcover hQcard
      hE hA htime hN ht hconst hscale hfloor hratio ha hab hcoeff i hroot hR
    have hbound := ksss_configuration_centered_step_drift_nonpos (restrictedGreedyKernel F S R hR) X
      (ksssOrders q) a coeff E A scale time sigma (ksssIndexedConfigurationDriftCoefficient q coeff i)
      B (i.order - 3) i.chosen hsigma hd (by omega) (by omega) hE hA.le hs htime
      (by linarith [hscalar.unit_clock]) hscalar.taylor_size horders ha hab hmean (hbudget i)
    change (restrictedGreedyKernel F S R hR).expectationReal
      (fun S' ↦ sigma * (X S' - df) - de) ≤ 0 at hbound
    simpa only [← hid, index, ksssTrajectorySelectors, R, N, scale] using hbound
  · intro hR
    have hrawSecond : (restrictedGreedyKernel F S R hR).expectationReal (fun S' ↦ X S' ^ 2) ≤
        N ^ (2 * z) / N * (t : ℝ) ^ (k + 5 * b + 8) := by
      simpa only [ksssTrajectoryDimension, hz, ksssPowerRawVarianceExponent,
        ksssTrajectorySelectors, R, N, X, index] using hraw.2 hR
    have hbound := centered_step_secondMoment_power (restrictedGreedyKernel F S R hR) X N t sigma df de
      z (k + 5 * b + 8) (5 * b + 7) hN1 (by linarith) hsigma hrawSecond hdet
    simpa only [← hid, index, ksssTrajectorySelectors, R, N, scale, ksssTrajectoryDimension, hz,
      ksssPowerVarianceExponent, ksssPowerRawVarianceExponent, ksssPowerDeterministicExponent] using hbound

end

end Erdos207
