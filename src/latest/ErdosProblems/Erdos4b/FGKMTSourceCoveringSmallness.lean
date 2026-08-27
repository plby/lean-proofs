/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceCoveringScales

/-! # Full-ray verification of covering smallness and normalized sparsity -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_source_covering_log_absorption :
    ∀ᶠ x : ℝ in atTop,
      2600 * Real.log x ^ (1 / 10 : ℝ) * Real.log (Real.log x) ^ 4 ≤ Real.log x / 20 := by
  have hL := Real.tendsto_log_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((4 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 9 / 10)).comp_tendsto hL).bound
      (by norm_num : (0 : ℝ) < 1 / 52000)
  filter_upwards [hsmall, hL.eventually_ge_atTop 1] with x hx hlarge
  have hL0 : 0 < Real.log x := zero_lt_one.trans_le hlarge
  have hℓ0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlarge
  have hs : Real.log (Real.log x) ^ 4 ≤
      (1 / 52000) * Real.log x ^ (9 / 10 : ℝ) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hℓ0 4),
      abs_of_nonneg (Real.rpow_nonneg hL0.le (9 / 10 : ℝ))] using hx
  have hp : Real.log x ^ (1 / 10 : ℝ) * Real.log x ^ (9 / 10 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hL0]
    norm_num
  calc
    _ ≤ 2600 * Real.log x ^ (1 / 10 : ℝ) *
        ((1 / 52000) * Real.log x ^ (9 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (Real.log x ^ (1 / 10 : ℝ) * Real.log x ^ (9 / 10 : ℝ)) / 20 := by ring
    _ = _ := by rw [hp]

theorem eventually_source_covering_smallness :
    ∀ᶠ x : ℝ in atTop, ∀ k : ℕ, (k : ℝ) ≤ Real.log x ^ (1 / 10 : ℝ) →
      x ^ (-1 / 20 : ℝ) ≤
        (1 / coveringScale (sourceCoveringSize k x) 4 (sourceSurvivalFloor x)) ^
          (10 ^ (sourceBatchCount x + 2)) := by
  have hL := Real.tendsto_log_atTop
  have hℓ := Real.tendsto_log_atTop.comp hL
  filter_upwards [eventually_source_covering_log_absorption, eventually_ge_atTop (1 : ℝ),
    hL.eventually_ge_atTop 1, hℓ.eventually_ge_atTop 1] with x hx hx1 hL1 hℓ1 k hk
  change 1 ≤ Real.log (Real.log x) at hℓ1
  have hbudget := (sourceCovering_log_budget_le hL1 hℓ1 hk).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hS : 0 < coveringScale (sourceCoveringSize k x) 4 (sourceSurvivalFloor x) := by
    unfold coveringScale
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
      (one_div_pos.mpr (pow_pos (sourceSurvivalFloor_pos x) _))
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hx0 (-1 / 20 : ℝ))
    (pow_pos (one_div_pos.mpr hS) _)).mp
  rw [Real.log_rpow hx0, Real.log_pow, Real.log_div (by norm_num) hS.ne', Real.log_one]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

theorem source_normalized_sparsity {x : ℝ} {N : ℕ} (hx : 1 ≤ x)
    (hN : 0 < N) (hNx : (N : ℝ) ≤ x) :
    x ^ (-3 / 5 : ℝ) ≤ x ^ (-1 / 20 : ℝ) / Real.sqrt (N : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hN0)).mpr
  calc
    _ ≤ x ^ (-3 / 5 : ℝ) * Real.sqrt x :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNx) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-1 / 10 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

end

end Erdos4b.FGKMT
