/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternTrajectory
import ErdosProblems.Erdos207.KSSSDyadicPairBounds

/-! # Positive lower bounds for the relative pattern denominator -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssPatternTrajectory_pos
    (orders : Finset ℕ) (a : ℕ → ℝ) (E M time : ℝ) (h m : ℕ)
    (hM : 0 < M) (hp : 0 < ksssEdgeDensity E time) :
    0 < ksssPatternTrajectory orders a E M h m time := by
  unfold ksssPatternTrajectory
  positivity

theorem ksssPatternTrajectory_power_lower
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E M time t : ℝ) (h m b : ℕ)
    (hM : 0 ≤ M) (ht : 0 < t) (htime : 0 ≤ time) (hclock : time ≤ E)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E ^ d ≤ coeff d)
    (hexp : Real.exp (∑ d ∈ orders, coeff d) ≤ t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time) :
    M / t ^ (b * h + m) ≤ ksssPatternTrajectory orders a E M h m time := by
  have hbase := ksssPoisson_exp_neg_ge_inverse_scale orders a coeff E time t ha hab htime hclock hexp
  have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / t) hbase m
  have hexpPower : (1 / t) ^ m ≤ Real.exp (-(m : ℝ) * ksssPoissonExponent orders a time) := by
    calc
      _ ≤ Real.exp (-ksssPoissonExponent orders a time) ^ m := hpower
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hpPower := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / t ^ b) hfloor h
  have hp : 0 < ksssEdgeDensity E time := (by positivity : 0 < 1 / t ^ b).trans_le hfloor
  calc
    _ = M * (1 / t ^ b) ^ h * (1 / t) ^ m := by
      rw [pow_add, one_div_pow, one_div_pow, ← pow_mul]
      ring
    _ ≤ M * ksssEdgeDensity E time ^ h * Real.exp (-(m : ℝ) * ksssPoissonExponent orders a time) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpPower hM) hexpPower
        (by positivity) (by positivity)
    _ = _ := rfl

theorem ksssPatternTrajectory_le_size
    (orders : Finset ℕ) (a : ℕ → ℝ) (E M time : ℝ) (h m : ℕ)
    (hE : 0 < E) (hM : 0 ≤ M) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ orders, 0 ≤ a d) :
    ksssPatternTrajectory orders a E M h m time ≤ M := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hp1 := ksssEdgeDensity_le_one hE htime
  have hpow : ksssEdgeDensity E time ^ h ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hp.le hp1 h
  have hexp : Real.exp (-(m : ℝ) * ksssPoissonExponent orders a time) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg m)) (ksssPoissonExponent_nonneg orders a ha htime))
  calc
    _ ≤ M * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hpow hM) hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem pattern_target_step_relative_bound
    (f fp H A L x G tau : ℝ) (hf : 0 < f) (hL : 0 < L) (hx : 0 < x)
    (hA : A = L * x / 3) (hH : |H| ≤ G * x)
    (hTaylor : |fp - f + f * H / A| ≤ tau) :
    |fp - f| / f ≤ 3 * G / L + tau / f := by
  subst A
  have hslope : |f * H / (L * x / 3)| ≤ f * (3 * G / L) := by
    rw [abs_div, abs_mul, abs_of_pos hf, abs_of_pos (by positivity : 0 < L * x / 3)]
    calc
      _ ≤ f * (G * x) / (L * x / 3) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH hf.le) (by positivity)
      _ = _ := by field_simp
  have hstep : |fp - f| ≤ tau + f * (3 * G / L) := by
    calc
      _ = |(fp - f + f * H / (L * x / 3)) - f * H / (L * x / 3)| := by
        congr 1
        ring
      _ ≤ |fp - f + f * H / (L * x / 3)| + |f * H / (L * x / 3)| := abs_sub _ _
      _ ≤ _ := add_le_add hTaylor hslope
  calc
    _ ≤ (tau + f * (3 * G / L)) / f := div_le_div_of_nonneg_right hstep hf.le
    _ = _ := by field_simp; ring

theorem pattern_target_next_ge_half
    (f fp rate : ℝ) (hf : 0 < f) (hstep : |fp - f| / f ≤ rate) (hrate : rate ≤ 1 / 2) :
    f / 2 ≤ fp := by
  have h := (div_le_iff₀ hf).mp (hstep.trans hrate)
  have hlo := (abs_le.mp h).1
  linarith only [hlo]

end

end Erdos207
