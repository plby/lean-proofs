/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBatchCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform verification of the source batch-partition failure budget -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem batchVariancePower_identity {x : ℝ} (hx : 0 < x) :
    x * (x ^ (-3 / 5 : ℝ)) ^ 2 = 1 / x ^ (1 / 5 : ℝ) := by
  calc
    _ = x ^ (1 : ℝ) * x ^ (-6 / 5 : ℝ) := by
      rw [Real.rpow_one, ← Real.rpow_mul_natCast hx.le]
      norm_num
    _ = x ^ (-(1 / 5 : ℝ)) := by
      rw [← Real.rpow_add hx]
      norm_num
    _ = _ := by simp only [Real.rpow_neg hx.le, one_div]

theorem batch_failure_exponent_le {x N : ℝ} (hx : 0 < x) (hN : 0 < N) (hNx : N ≤ x)
    (hL : 1 ≤ Real.log x) (hℓ : 1 ≤ Real.log (Real.log x))
    (hgrowth : 4 * Real.log x ^ 5 ≤ x ^ (1 / 5 : ℝ)) :
    -2 * (1 / Real.log (Real.log x) ^ 2) ^ 2 / (N * (x ^ (-3 / 5 : ℝ)) ^ 2) ≤
      -4 * Real.log x := by
  let L := Real.log x
  let ell := Real.log L
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hell : 0 < ell := zero_lt_one.trans_le hℓ
  have hellL : ell ≤ L := Real.log_le_self hL0.le
  have hpow := pow_le_pow_left₀ hell.le hellL 4
  have hg : 4 * L * ell ^ 4 ≤ x ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ 4 * L * L ^ 4 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 4 * L ^ 5 := by ring
      _ ≤ _ := hgrowth
  have hdiv : 4 * L ≤ x ^ (1 / 5 : ℝ) / ell ^ 4 :=
    (le_div_iff₀ (pow_pos hell 4)).mpr hg
  have hden : 0 < N * (x ^ (-3 / 5 : ℝ)) ^ 2 :=
    mul_pos hN (sq_pos_of_pos (Real.rpow_pos_of_pos hx _))
  have hdenle : N * (x ^ (-3 / 5 : ℝ)) ^ 2 ≤ 1 / x ^ (1 / 5 : ℝ) :=
    (mul_le_mul_of_nonneg_right hNx (sq_nonneg _)).trans_eq (batchVariancePower_identity hx)
  have hratio : 2 * x ^ (1 / 5 : ℝ) / ell ^ 4 ≤
      2 * (1 / ell ^ 2) ^ 2 / (N * (x ^ (-3 / 5 : ℝ)) ^ 2) := by
    calc
      _ = (2 * (1 / ell ^ 2) ^ 2) / (1 / x ^ (1 / 5 : ℝ)) := by
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden hdenle
  have hbound : 4 * L ≤ 2 * (1 / ell ^ 2) ^ 2 / (N * (x ^ (-3 / 5 : ℝ)) ^ 2) := by
    rw [mul_div_assoc] at hratio
    linarith
  simpa only [neg_div, neg_mul] using neg_le_neg hbound

theorem batch_failure_budget_lt_one {x N V m : ℝ} (hx : 2 < x)
    (hN : 0 < N) (hNx : N ≤ x) (hV : V ≤ x ^ 2)
    (hm0 : 0 ≤ m) (hm : m ≤ x) (hL : 1 ≤ Real.log x)
    (hℓ : 1 ≤ Real.log (Real.log x))
    (hgrowth : 4 * Real.log x ^ 5 ≤ x ^ (1 / 5 : ℝ)) :
    2 * V * m * Real.exp
      (-2 * (1 / Real.log (Real.log x) ^ 2) ^ 2 / (N * (x ^ (-3 / 5 : ℝ)) ^ 2)) < 1 := by
  have hx0 : 0 < x := by linarith
  have hcount : 2 * V * m ≤ 2 * x ^ 3 := by
    calc
      _ ≤ (2 * x ^ 2) * x := mul_le_mul (by nlinarith) hm hm0 (by positivity)
      _ = _ := by ring
  have hexp := Real.exp_le_exp.mpr (batch_failure_exponent_le hx0 hN hNx hL hℓ hgrowth)
  have hexact : Real.exp (-4 * Real.log x) = (x ^ 4)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    congr 1
    simpa only [Nat.cast_ofNat, Real.exp_log hx0] using Real.exp_nat_mul (Real.log x) 4
  calc
    _ ≤ (2 * x ^ 3) * Real.exp (-4 * Real.log x) :=
      mul_le_mul hcount hexp (Real.exp_pos _).le (by positivity)
    _ = 2 / x := by
      rw [hexact]
      field_simp
    _ < 1 := (div_lt_one hx0).mpr hx

theorem eventually_batch_log_growth :
    ∀ᶠ x : ℕ in atTop, 4 * Real.log (x : ℝ) ^ 5 ≤ (x : ℝ) ^ (1 / 5 : ℝ) := by
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 10)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  have hrpow : Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hsmall, hrpow.eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hsmall hfour hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hlog0 := Real.log_natCast_nonneg x
  simp only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog0 5),
    abs_of_nonneg (Real.rpow_nonneg hx0.le (1 / 10 : ℝ))] at hsmall
  calc
    _ ≤ (x : ℝ) ^ (1 / 10 : ℝ) * (x : ℝ) ^ (1 / 10 : ℝ) :=
      mul_le_mul hfour hsmall (pow_nonneg hlog0 5) (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; norm_num

end

end Erdos4b.FGKMT
