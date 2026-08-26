/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicScales

/-!
# A single dyadic ray with vanishing smooth exceptions for every multiplier

The ray parameter is chosen once from the Rankin Euler constant, not
from D. This preserves the arbitrary interval multiplier in the final
large-gap construction.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

theorem exists_smoothResidualException_frontier_rankin_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ r U : ℕ, 1 ≤ r → 0 < U →
      ((smoothResidualException U (smoothFrontier r)).card : ℝ) ≤
        (U : ℝ) ^ (1 - delta r) * Real.exp (B * (2 : ℝ) ^ r) := by
  obtain ⟨B, hB, hEuler⟩ := exists_eulerExponentConstant
  refine ⟨B, hB, ?_⟩
  intro r U hr hU
  exact (card_smoothResidualException_rankin_le hU (delta_pos r)
    ((delta_le_half r).trans_lt (by norm_num))).trans
      (mul_le_mul_of_nonneg_left (hEuler r hr) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem scaled_smoothRankinExpression_le_coreSix
    {B : ℝ} {a D r : ℕ} (hr : 1 ≤ r) (hD : 0 < D)
    (hB : B + 6 * Real.log 2 ≤ (2 : ℝ) ^ a * Real.log 2) :
    (D * intervalLength a r : ℕ) ^ (1 - delta r) * Real.exp (B * (2 : ℝ) ^ r) ≤
      (D * intervalLength a r : ℕ) / (core r : ℝ) ^ 6 := by
  have hU : 0 < D * intervalLength a r := Nat.mul_pos hD (intervalLength_pos (by omega))
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hlogU : Real.log (intervalLength a r : ℝ) ≤ Real.log (D * intervalLength a r : ℕ) :=
    Real.log_le_log (by exact_mod_cast intervalLength_pos (a := a) (by omega : 0 < r))
      (by exact_mod_cast Nat.le_mul_of_pos_left (intervalLength a r) hD)
  have hsave := (delta_mul_log_intervalLength_lower (a := a) hr).trans
    (mul_le_mul_of_nonneg_left hlogU (delta_pos r).le)
  rw [pow_add] at hsave
  have hB' := mul_le_mul_of_nonneg_right hB (show (0 : ℝ) ≤ (2 : ℝ) ^ r by positivity)
  have hexponent : -delta r * Real.log (D * intervalLength a r : ℕ) + B * (2 : ℝ) ^ r ≤
      -6 * Real.log (core r : ℝ) := by
    rw [log_core]
    nlinarith
  rw [rpow_one_sub_eq_mul_exp_neg hU, mul_assoc, ← Real.exp_add]
  calc
    _ ≤ (D * intervalLength a r : ℕ) * Real.exp (-6 * Real.log (core r : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (Nat.cast_nonneg _)
    _ = _ := by
      rw [show -6 * Real.log (core r : ℝ) = -Real.log ((core r : ℝ) ^ 6) by
        rw [Real.log_pow]; norm_num]
      rw [Real.exp_neg, Real.exp_log (pow_pos hcore 6), div_eq_mul_inv]

theorem scaled_smoothRankinExpression_le_budget
    {B : ℝ} {a D r : ℕ} (hr : 1 ≤ r) (hD : 0 < D)
    (hB : B + 6 * Real.log 2 ≤ (2 : ℝ) ^ a * Real.log 2)
    (har : a + 2 * r ≤ 2 ^ r) :
    (D * intervalLength a r : ℕ) ^ (1 - delta r) * Real.exp (B * (2 : ℝ) ^ r) ≤
      ((D : ℝ) / (core r : ℝ) ^ 2) *
        ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r) := by
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hVupper : dyadicAmbientScale a r ≤ (core r : ℝ) ^ 2 := by
    rw [dyadicAmbientScale_eq]
    exact (mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2).trans
      (by exact_mod_cast primaryExponent_le_core_sq_of har)
  have hUupper : ((D * intervalLength a r : ℕ) : ℝ) ≤
      (D : ℝ) * (primaryFrontier a r : ℝ) * (core r : ℝ) ^ 2 := by
    exact_mod_cast (show D * intervalLength a r ≤ D * primaryFrontier a r * core r ^ 2 by
      simpa only [mul_assoc] using
        Nat.mul_le_mul_left D (intervalLength_le_primary_mul_core_sq a r))
  calc
    _ ≤ (D * intervalLength a r : ℕ) / (core r : ℝ) ^ 6 :=
      scaled_smoothRankinExpression_le_coreSix hr hD hB
    _ ≤ ((D : ℝ) * (primaryFrontier a r : ℝ) * (core r : ℝ) ^ 2) / (core r : ℝ) ^ 6 :=
      div_le_div_of_nonneg_right hUupper (by positivity)
    _ = ((D : ℝ) / (core r : ℝ) ^ 2) * ((primaryFrontier a r : ℝ) / (core r : ℝ) ^ 2) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hV hVupper) (by positivity)

theorem exists_dyadicRay_smoothException_vanishing :
    ∃ a : ℕ, ∀ D : ℕ, 0 < D → ∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop,
      ((smoothResidualException (D * intervalLength a r) (smoothFrontier r)).card : ℝ) ≤
        ε * ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r) := by
  obtain ⟨B, hBpos, hcard⟩ := exists_smoothResidualException_frontier_rankin_bound
  obtain ⟨a, ha⟩ := exists_lossExponent (B + 2 * Real.log 2)
  have hB : B + 6 * Real.log 2 ≤ (2 : ℝ) ^ a * Real.log 2 := by linarith
  refine ⟨a, ?_⟩
  intro D hD ε hε
  have hcoreNat : Tendsto core atTop atTop := tendsto_atTop_mono self_le_core tendsto_id
  have hcore : Tendsto (fun r : ℕ ↦ (core r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcoreNat
  have hlim : Tendsto (fun r ↦ (D : ℝ) / (core r : ℝ) ^ 2) atTop (𝓝 0) := by
    have hh := ((tendsto_inv_atTop_zero.comp hcore).pow 2).const_mul (D : ℝ)
    rw [show (D : ℝ) * (0 : ℝ) ^ (2 : ℕ) = 0 by norm_num] at hh
    simpa only [Function.comp_def, div_eq_mul_inv, inv_pow] using hh
  filter_upwards [eventually_ge_atTop (max a 4), hlim.eventually (gt_mem_nhds hε)]
    with r hr hsmall
  have hra : a ≤ r := (le_max_left a 4).trans hr
  have hr4 : 4 ≤ r := (le_max_right a 4).trans hr
  have hU := Nat.mul_pos hD (intervalLength_pos (a := a) (by omega : 0 < r))
  have hfirst := hcard r (D * intervalLength a r) (by omega) hU
  have hmain := scaled_smoothRankinExpression_le_budget (by omega : 1 ≤ r) hD hB
    (stable_exponent_comparison hra hr4)
  apply (hfirst.trans hmain).trans
  exact mul_le_mul_of_nonneg_right hsmall.le (by
    apply div_nonneg (Nat.cast_nonneg _)
    exact zero_le_one.trans (one_le_dyadicAmbientScale a r))

end

end Erdos4b.SmoothParameters
