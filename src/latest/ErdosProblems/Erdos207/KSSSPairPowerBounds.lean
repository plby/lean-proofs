/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSUniformCountBounds
import ErdosProblems.Erdos207.PowerSelectorBounds
import ErdosProblems.Erdos207.DyadicCrudeCutoffs

/-! # The source pair slope and the expected-loss power scale -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssPairSlope_clock_ambient_bound
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E A time N : ℝ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E ^ d ≤ b d) (hratio : A / E ≤ N) :
    |ksssPairSlope orders a E A time| ≤
      (9 * (ksssThreatCoefficient orders b + 1)) * N / (E * ksssEdgeDensity E time) := by
  let x := ksssPairTrajectory orders a E A time
  let H := ksssThreatTrajectory orders a E A time
  let L := E * ksssEdgeDensity E time
  let C := ksssThreatCoefficient orders b
  have hp := ksssEdgeDensity_pos hE hclock
  have hx : 0 < x := ksssPairTrajectory_pos orders a hE hA hclock
  have hL : 0 < L := mul_pos hE hp
  have hb : ∀ d ∈ orders, 0 ≤ b d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hC : 0 ≤ C := ksssThreatCoefficient_nonneg orders b hb
  have hH := ksssThreatTrajectory_bounds orders a b horders ha hab hE hA htime hclock
  have hH0 : 0 ≤ H := by dsimp only [H]; linarith only [hx, hH.1]
  have hHabs : |H| ≤ C * x := by rw [abs_of_nonneg hH0]; exact hH.2
  have hsub : |H - x| ≤ C * x + x := by
    calc
      _ ≤ |H| + |x| := abs_sub _ _
      _ ≤ C * x + x := by rw [abs_of_pos hx]; exact add_le_add hHabs le_rfl
  have hxN : x ≤ 3 * N := by
    have h := ksssPairTrajectory_le_three_ratio orders a E A time hE hA.le htime hclock ha
    dsimp only [x]
    linarith only [h, hratio]
  calc
    _ = (3 / L) * |H - x| := by
      rw [ksssPairSlope_eq_source_drift orders a E A time horders hE.ne' hp.ne']
      change |-(3 / L) * (H - x)| = _
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 3 / L)]
    _ ≤ (3 / L) * (C * x + x) := mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = 3 * (C + 1) * x / L := by ring
    _ ≤ 3 * (C + 1) * (3 * N) / L := by gcongr
    _ = _ := by dsimp only [C, L]; ring

theorem ksssPairSlope_power
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ) (b : ℕ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E ^ d ≤ coeff d)
    (hN : 0 < N) (ht : 0 < t) (hratio : A / E ≤ N)
    (hL : N ^ 2 / t ^ (2 * b) ≤ E * ksssEdgeDensity E time)
    (hcoeff : 9 * (ksssThreatCoefficient orders coeff + 1) ≤ t) :
    |ksssPairSlope orders a E A time| ≤ 1 / N * t ^ (2 * b + 1) := by
  have hb : ∀ d ∈ orders, 0 ≤ coeff d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hC := ksssThreatCoefficient_nonneg orders coeff hb
  have hbound := coefficient_envelope_div_clock_power N t N
    (9 * (ksssThreatCoefficient orders coeff + 1)) (E * ksssEdgeDensity E time) 0 b
    hN ht hN.le (by positivity) (by simp) hcoeff hL
  exact (ksssPairSlope_clock_ambient_bound orders a coeff E A time N
    hE hA htime hclock horders ha hab hratio).trans (by simpa only [pow_zero] using hbound)

theorem ksss_pair_slope_error_power
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A scale time N t D : ℝ) (B b : ℕ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E ^ d ≤ coeff d)
    (hN : 0 < N) (ht : 0 < t) (hD : 0 ≤ D) (hratio : A / E ≤ N)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory orders a E A time / 4)
    (hL : N ^ 2 / t ^ (2 * b) ≤ E * ksssEdgeDensity E time)
    (hcoeff : 9 * (ksssThreatCoefficient orders coeff + 1) + D ≤ t) :
    |ksssPairSlope orders a E A time| + D * ksssErrorEnvelope E scale B time /
        (E * ksssEdgeDensity E time) ≤ 1 / N * t ^ (2 * b + 1) := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hb : ∀ d ∈ orders, 0 ≤ coeff d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hC := ksssThreatCoefficient_nonneg orders coeff hb
  have he := ksssErrorEnvelope_le_ambient orders a E A scale time N B
    hE hA.le htime hclock ha hN.le hratio hsmall
  have herror := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hD) (mul_nonneg hE.le hp.le)
  have hslope := ksssPairSlope_clock_ambient_bound orders a coeff E A time N
    hE hA htime hclock horders ha hab hratio
  have hbound := coefficient_envelope_div_clock_power N t N
    (9 * (ksssThreatCoefficient orders coeff + 1) + D) (E * ksssEdgeDensity E time) 0 b
    hN ht hN.le (by positivity) (by simp) hcoeff hL
  calc
    _ ≤ (9 * (ksssThreatCoefficient orders coeff + 1)) * N / (E * ksssEdgeDensity E time) +
        D * N / (E * ksssEdgeDensity E time) := add_le_add hslope herror
    _ = (9 * (ksssThreatCoefficient orders coeff + 1) + D) * N /
        (E * ksssEdgeDensity E time) := by ring
    _ ≤ _ := by simpa only [pow_zero] using hbound

end

end Erdos207
