/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedSharpInitialLaw
import ErdosProblems.Erdos207.OuterSharpClockHarmonic

/-!
# Polynomial decay of the sharp tracked-edge survival factor

The canonical pair schedules are close enough that the effective hazard for
a fixed witness family is at least twice the reciprocal eligible-pair clock.
The logarithmic clock estimate then yields a rational power of its terminal
ratio.  Raising to the seventh power keeps the final result algebraic.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

lemma twice_reciprocal_le_effective_hazard
    (E M d u s : ℕ) (hE : 0 < E) (hM : 0 < M)
    (hd : 0 < d) (hMbound : 3 * M ≤ E * u)
    (hratio : 4 * u ≤ 5 * d) (hsmall : 18 * s ≤ d) :
    2 / (E : ℝ) ≤ ((d - 3 * s : ℕ) : ℝ) / M := by
  have heffective : 5 * d ≤ 6 * (d - 3 * s) := by omega
  have hratioScaled := Nat.mul_le_mul_left E hratio
  have heffectiveScaled := Nat.mul_le_mul_left E heffective
  have hfinal : 2 * M ≤ E * (d - 3 * s) := by nlinarith
  rw [div_le_div_iff₀ (by exact_mod_cast hE) (by exact_mod_cast hM)]
  exact_mod_cast (by simpa only [Nat.mul_comm E] using hfinal)

lemma boundedSharpSurvivalTheta_coe_le_exp
    (M d K : ℕ) (hM : 0 < M) (hdM : d ≤ M) :
    (boundedSharpSurvivalTheta M d K : ℝ) ≤
      Real.exp (-(((d - K : ℕ) : ℝ) / M)) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hsub : d - K ≤ M := (Nat.sub_le d K).trans hdM
  have hidentity : (boundedSharpSurvivalTheta M d K : ℝ) =
      1 - ((d - K : ℕ) : ℝ) / M := by
    simp only [boundedSharpSurvivalTheta, NNReal.coe_mul,
      NNReal.coe_natCast, NNReal.coe_inv, Nat.cast_sub hsub]
    field_simp
  rw [hidentity]
  simpa only [sub_eq_add_neg, add_comm] using
    Real.add_one_le_exp (-(((d - K : ℕ) : ℝ) / M))

theorem cumulativeSurvival_boundedSharp_le_exp_neg_sum
    (fuel K : ℕ) (M d : ℕ → ℕ)
    (hM : ∀ i, i < fuel → 0 < M i)
    (hdM : ∀ i, i < fuel → d i ≤ M i) :
    (cumulativeSurvival (boundedSharpSurvivalSchedule fuel M d K) fuel : ℝ) ≤
      Real.exp (-(∑ i ∈ range fuel, ((d i - K : ℕ) : ℝ) / M i)) := by
  simp only [cumulativeSurvival, NNReal.coe_prod]
  calc
    (∏ i ∈ range fuel,
        (boundedSharpSurvivalSchedule fuel M d K i : ℝ)) ≤
        ∏ i ∈ range fuel, Real.exp (-(((d i - K : ℕ) : ℝ) / M i)) := by
      apply prod_le_prod
      · intro i _hi
        exact NNReal.coe_nonneg _
      · intro i hi
        have hiFuel := mem_range.mp hi
        simpa only [boundedSharpSurvivalSchedule, if_pos hiFuel] using
          boundedSharpSurvivalTheta_coe_le_exp (M i) (d i) K
            (hM i hiFuel) (hdM i hiFuel)
    _ = Real.exp (-(∑ i ∈ range fuel,
        ((d i - K : ℕ) : ℝ) / M i)) := by
      rw [← Real.exp_sum, sum_neg_distrib]

/-- The survival product has exponent at least four sevenths of the
logarithmic clock drop. -/
theorem cumulativeSurvival_boundedSharp_le_exp_log_clock
    (fuel s : ℕ) (E M d u : ℕ → ℕ)
    (hlarge : ∀ i, i < fuel → 21 ≤ E i)
    (hstep : ∀ i, i < fuel → E (i + 1) = E i - 3)
    (hM : ∀ i, i < fuel → 0 < M i)
    (hd : ∀ i, i < fuel → 0 < d i)
    (hdM : ∀ i, i < fuel → d i ≤ M i)
    (hMbound : ∀ i, i < fuel → 3 * M i ≤ E i * u i)
    (hratio : ∀ i, i < fuel → 4 * u i ≤ 5 * d i)
    (hsmall : ∀ i, i < fuel → 18 * s ≤ d i) :
    (cumulativeSurvival
        (boundedSharpSurvivalSchedule fuel M d (3 * s)) fuel : ℝ) ≤
      Real.exp (-(4 / 7 : ℝ) * (Real.log (E 0) - Real.log (E fuel))) := by
  have hlog := log_clock_ratio_le_seven_halves_mul_sum_inv
    E fuel hlarge hstep
  have hsum : 2 * (∑ i ∈ range fuel, ((E i : ℝ)⁻¹)) ≤
      ∑ i ∈ range fuel, ((d i - 3 * s : ℕ) : ℝ) / M i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hiFuel := mem_range.mp hi
    have hEpos : 0 < E i := by have := hlarge i hiFuel; omega
    simpa only [div_eq_mul_inv] using
      twice_reciprocal_le_effective_hazard (E i) (M i) (d i) (u i) s
        hEpos (hM i hiFuel) (hd i hiFuel) (hMbound i hiFuel)
        (hratio i hiFuel) (hsmall i hiFuel)
  apply (cumulativeSurvival_boundedSharp_le_exp_neg_sum
    fuel (3 * s) M d hM hdM).trans
  apply Real.exp_le_exp.mpr
  linarith

/-- An integral-power form of the clock decay, avoiding real powers. -/
theorem cumulativeSurvival_boundedSharp_pow_seven_le_clock_ratio
    (fuel s : ℕ) (E M d u : ℕ → ℕ)
    (hEzero : 0 < E 0) (hEfinal : 0 < E fuel)
    (hlarge : ∀ i, i < fuel → 21 ≤ E i)
    (hstep : ∀ i, i < fuel → E (i + 1) = E i - 3)
    (hM : ∀ i, i < fuel → 0 < M i)
    (hd : ∀ i, i < fuel → 0 < d i)
    (hdM : ∀ i, i < fuel → d i ≤ M i)
    (hMbound : ∀ i, i < fuel → 3 * M i ≤ E i * u i)
    (hratio : ∀ i, i < fuel → 4 * u i ≤ 5 * d i)
    (hsmall : ∀ i, i < fuel → 18 * s ≤ d i) :
    cumulativeSurvival
        (boundedSharpSurvivalSchedule fuel M d (3 * s)) fuel ^ 7 ≤
      ((E fuel : ℝ≥0) / E 0) ^ 4 := by
  have hraw := cumulativeSurvival_boundedSharp_le_exp_log_clock
    fuel s E M d u hlarge hstep hM hd hdM hMbound hratio hsmall
  have hzero : (0 : ℝ) < E 0 := by exact_mod_cast hEzero
  have hfinal : (0 : ℝ) < E fuel := by exact_mod_cast hEfinal
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_natCast]
  calc
    (cumulativeSurvival
        (boundedSharpSurvivalSchedule fuel M d (3 * s)) fuel : ℝ) ^ 7 ≤
        Real.exp (-(4 / 7 : ℝ) *
          (Real.log (E 0) - Real.log (E fuel))) ^ 7 := by
      exact pow_le_pow_left₀ (NNReal.coe_nonneg _) hraw 7
    _ = Real.exp (4 * Real.log ((E fuel : ℝ) / E 0)) := by
      rw [← Real.exp_nat_mul, Real.log_div hfinal.ne' hzero.ne']
      congr 1
      norm_num
      ring
    _ = ((E fuel : ℝ) / E 0) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log (div_pos hfinal hzero)]

end

end Erdos207
