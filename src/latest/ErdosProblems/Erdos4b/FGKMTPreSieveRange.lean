/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTDimensionPreSieve
import ErdosProblems.Erdos4b.FGKMTDimensionLossAbsorption
import ErdosProblems.Erdos4b.FGKMTSieveRadius

/-! # Checking the numerical ranges of the actual small-prime modulus -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

theorem eventually_dimensionPrimeCutoff_le_half :
    ∀ᶠ x : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) → 2 * k ^ 2 ≤ x / 2 := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).def (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hsmall, hlogTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hL
  intro k hk
  have hkL : (k : ℝ) ≤ Real.log (x : ℝ) :=
    hk.trans (Real.rpow_le_self_of_one_le hL (by norm_num))
  have hk2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hkL 2
  have hsmall' : Real.log (x : ℝ) ^ 2 ≤ (1 / 4 : ℝ) * x := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.rpow_one,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (x : ℝ))),
      abs_of_nonneg (show (0 : ℝ) ≤ x from Nat.cast_nonneg x)] using hx
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
  have hR : (2 * (k : ℝ) ^ 2) * 2 ≤ x := by nlinarith
  exact_mod_cast hR

theorem eventually_dimensionPreSieveModulus_le_rpow :
    ∀ᶠ x : ℕ in atTop, ∀ k B : ℕ, 1 ≤ k →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      (dimensionPreSieveModulus k B : ℝ) ≤ (x : ℝ) ^ (1 / 18 : ℝ) := by
  filter_upwards [eventually_uniform_squareDimension_loss
      (by norm_num : (0 : ℝ) < 8) (by norm_num : (0 : ℝ) < 1),
    eventually_exp_mul_sqrtLog_le_rpow 1 (by norm_num : (0 : ℝ) < 1 / 18)] with x hx he
  intro k B hk1 hk
  have hcost : 8 * (k : ℝ) ^ 2 ≤ Real.sqrt (Real.log (x : ℝ)) := by
    have hS := mul_le_mul_of_nonneg_left (one_le_dimensionLogLossScale x)
      (by positivity : 0 ≤ 8 * (k : ℝ) ^ 2)
    have hc := hx k hk1 hk
    simp only [mul_one, one_mul] at hS hc
    exact hS.trans hc
  calc
    _ ≤ Real.exp (8 * (k : ℝ) ^ 2) := dimensionPreSieveModulus_le_exp k B
    _ ≤ Real.exp (Real.sqrt (Real.log (x : ℝ))) := Real.exp_monotone hcost
    _ ≤ _ := by simpa only [one_mul] using he

theorem eventually_dimensionPreSieve_radius_range :
    ∀ᶠ x : ℕ in atTop, ∀ k B : ℕ, 1 ≤ k →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      dimensionPreSieveModulus k B * dimensionSieveRadius x ^ 2 ≤ x / 2 ∧
      ((dimensionPreSieveModulus k B * dimensionSieveRadius x ^ 2 : ℕ) : ℝ) ≤
        vaughanCubeRoot x := by
  filter_upwards [eventually_dimensionPreSieveModulus_le_rpow,
    eventually_ge_atTop (4 : ℕ)] with x hx hx4
  intro k B hk1 hk
  have hxR : (4 : ℝ) ≤ x := by exact_mod_cast hx4
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by positivity
  have hprod : ((dimensionPreSieveModulus k B * dimensionSieveRadius x ^ 2 : ℕ) : ℝ) ≤
      (x : ℝ) ^ (5 / 18 : ℝ) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (x : ℝ) ^ (1 / 18 : ℝ) * (x : ℝ) ^ (2 / 9 : ℝ) :=
        mul_le_mul (hx k B hk1 hk) (dimensionSieveRadius_sq_le_rpow x)
          (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg x) _)
      _ = _ := by rw [← Real.rpow_add hxpos]; norm_num
  have hhalf : (x : ℝ) ^ (5 / 18 : ℝ) ≤ (x : ℝ) / 2 := by
    calc
      _ ≤ (x : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow _).symm
      _ ≤ _ := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  refine ⟨?_, hprod.trans ?_⟩
  · apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    have hn := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp (hprod.trans hhalf)
    exact_mod_cast hn
  · exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5 / 18 : ℝ) ≤ 1 / 3)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_dimensionPrimeCutoff_le_half
#print axioms Erdos4b.FGKMT.eventually_dimensionPreSieveModulus_le_rpow
#print axioms Erdos4b.FGKMT.eventually_dimensionPreSieve_radius_range
