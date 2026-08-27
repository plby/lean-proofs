/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerDeterministicIncrement
import ErdosProblems.Erdos207.KSSSUniformCountBounds
import ErdosProblems.Erdos207.KSSSTaylorSourceScale
import ErdosProblems.Erdos207.KSSSErrorEnvelopeUpper

/-! # The actual deterministic trajectory and envelope increments on the common scale -/

namespace Erdos207

open Finset

noncomputable section

theorem ksss_configuration_deterministic_increment_power
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A scale time N t : ℝ) (B d c b : ℕ)
    (hE : 0 < E) (hA : 0 ≤ A) (hs : 0 ≤ scale) (htime : 0 ≤ time)
    (hclock : 3 * time + 6 ≤ E) (hsize : A ≤ scale * E ^ 2)
    (horders : ∀ k ∈ orders, 1 ≤ k) (ha : ∀ k ∈ orders, 0 ≤ a k)
    (hab : ∀ k ∈ orders, a k * E ^ k ≤ coeff k)
    (hd : d ∈ orders) (hc : c < d) (hB : 2 * (d - c - 1) ≤ B)
    (hN : 0 < N) (ht : 6 ≤ t) (hratio : A / E ≤ N)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory orders a E A time / 4)
    (hL : N ^ 2 / t ^ (2 * b) ≤ E * ksssEdgeDensity E time)
    (hTaylorCoeff : ksssConfigurationTaylorCoefficient orders coeff d c ≤ t)
    (hEnvelopeCoeff : 6 * (B : ℝ) * 2 ^ B ≤ t)
    (hslope : |ksssConfigurationSlope orders a E A d c time| ≤
      N ^ (d - c - 1) / N * t ^ (5 * b + 6)) :
    |ksssConfigurationTrajectory orders a E A d c (time + 1) -
      ksssConfigurationTrajectory orders a E A d c time| +
      |ksssConfigurationErrorEnvelope E A scale B (d - c - 1) (time + 1) -
        ksssConfigurationErrorEnvelope E A scale B (d - c - 1) time| ≤
      N ^ (d - c - 1) / N * t ^ (5 * b + 7) := by
  have hclock0 : 3 * time < E := by linarith
  have hp := ksssEdgeDensity_pos hE hclock0
  have hb : ∀ k ∈ orders, 0 ≤ coeff k := fun k hk ↦
    (mul_nonneg (ha k hk) (pow_nonneg hE.le k)).trans (hab k hk)
  have he : 0 ≤ ksssConfigurationErrorEnvelope E A scale B (d - c - 1) time := by
    unfold ksssConfigurationErrorEnvelope ksssErrorEnvelope
    positivity
  have hEdgeN := ksssErrorEnvelope_le_ambient orders a E A scale time N B
    hE hA htime hclock0 ha hN.le hratio hsmall
  have hEnvSize := ksssConfigurationErrorEnvelope_le_ambient_power E A scale time N B (d - c - 1)
    hE hA hs htime hclock0 hratio hEdgeN
  have hTaylor := ksssConfigurationTrajectory_unitStep_error_source_scale orders a coeff E A scale time
    B d c hd hc hB hE hA hs htime (by linarith) hsize horders ha hab
  have hGrowth := ksssConfigurationErrorEnvelope_unitStep_abs_upper E A scale time B (d - c - 1)
    hE hA hs hclock hB
  exact deterministic_increment_power N t _ _ _
    (ksssConfigurationErrorEnvelope E A scale B (d - c - 1) time)
    (E * ksssEdgeDensity E time) (ksssConfigurationTaylorCoefficient orders coeff d c)
    (6 * (B : ℝ) * 2 ^ B) (d - c - 1) b hN ht he
    (ksssConfigurationTaylorCoefficient_nonneg orders coeff d c hb hd) (by positivity)
    hEnvSize hTaylorCoeff hEnvelopeCoeff hL hslope hTaylor hGrowth

theorem ksss_pair_deterministic_increment_power
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A scale time N t : ℝ) (B b : ℕ)
    (hE : 0 < E) (hA : 0 ≤ A) (hs : 0 ≤ scale) (htime : 0 ≤ time)
    (hclock : 3 * time + 6 ≤ E) (hsize : A ≤ scale * E ^ 2)
    (horders : ∀ k ∈ orders, 1 ≤ k) (ha : ∀ k ∈ orders, 0 ≤ a k)
    (hab : ∀ k ∈ orders, a k * E ^ k ≤ coeff k)
    (hN : 0 < N) (ht : 6 ≤ t) (hratio : A / E ≤ N)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory orders a E A time / 4)
    (hL : N ^ 2 / t ^ (2 * b) ≤ E * ksssEdgeDensity E time)
    (hTaylorCoeff : ksssPairTaylorCoefficient orders coeff ≤ t)
    (hEnvelopeCoeff : 6 * (B : ℝ) * 2 ^ B ≤ t)
    (hslope : |ksssPairSlope orders a E A time| ≤ 1 / N * t ^ (5 * b + 6)) :
    |ksssPairTrajectory orders a E A (time + 1) - ksssPairTrajectory orders a E A time| +
      |ksssErrorEnvelope E scale B (time + 1) - ksssErrorEnvelope E scale B time| ≤
      1 / N * t ^ (5 * b + 7) := by
  have hclock0 : 3 * time < E := by linarith
  have hp := ksssEdgeDensity_pos hE hclock0
  have hb : ∀ k ∈ orders, 0 ≤ coeff k := fun k hk ↦
    (mul_nonneg (ha k hk) (pow_nonneg hE.le k)).trans (hab k hk)
  have he : 0 ≤ ksssErrorEnvelope E scale B time := by unfold ksssErrorEnvelope; positivity
  have hEdgeN := ksssErrorEnvelope_le_ambient orders a E A scale time N B
    hE hA htime hclock0 ha hN.le hratio hsmall
  have hTaylor := ksssPairTrajectory_unitStep_error_source_scale orders a coeff E A scale time B
    hE hA hs htime (by linarith) hsize horders ha hab
  have hGrowth := ksssErrorEnvelope_unitStep_abs_upper E scale time B hE hs hclock
  have h := deterministic_increment_power N t _ _ _ (ksssErrorEnvelope E scale B time)
    (E * ksssEdgeDensity E time) (ksssPairTaylorCoefficient orders coeff) (6 * (B : ℝ) * 2 ^ B)
    0 b hN ht he (ksssPairTaylorCoefficient_nonneg orders coeff hb) (by positivity)
    (by simpa only [zero_add, pow_one] using hEdgeN) hTaylorCoeff hEnvelopeCoeff hL
    (by simpa only [pow_zero] using hslope) hTaylor hGrowth
  simpa only [pow_zero] using h

end

end Erdos207
