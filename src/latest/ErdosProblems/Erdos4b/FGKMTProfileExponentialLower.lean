/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMainLowerBound
import ErdosProblems.Erdos4b.FGKMTPresieveDensityLower

/-!
# Explicit exponential lower bounds for the chosen profile

These deliberately coarse inequalities retain enough room at dimension
log(x)^0.1. They apply to the same finite face-energy formula already proved.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exp_neg_two_mul_le_inv_two_mul {t : ℝ} (ht : 0 < t) :
    Real.exp (-2 * t) ≤ 1 / (2 * t) := by
  have h : 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
  simpa only [neg_mul] using exp_neg_le_inv_of_le_exp (by positivity : 0 < 2 * t) h

theorem exp_neg_two_mul_le_inv_profileScale {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    Real.exp (-2 * (k : ℝ)) ≤ 1 / (2 * sieveProfileScale k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le (profile_scales_bounds hk hlog).1
  have hlogle : Real.log (k : ℝ) ≤ k := (Real.log_le_sub_one_of_pos hkpos).trans (by linarith)
  have hTbound : sieveProfileScale k ≤ (k : ℝ) ^ 2 := by
    dsimp [sieveProfileScale]
    nlinarith
  have hkle : (k : ℝ) ≤ Real.exp (k : ℝ) := by linarith [Real.add_one_le_exp (k : ℝ)]
  have hprod := mul_le_mul (Real.two_mul_le_exp (x := (k : ℝ))) hkle hkpos.le (Real.exp_pos _).le
  have hbound : 2 * sieveProfileScale k ≤ Real.exp (2 * (k : ℝ)) := by
    calc
      _ ≤ (2 * (k : ℝ)) * k := by nlinarith
      _ ≤ Real.exp (k : ℝ) * Real.exp (k : ℝ) := hprod
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  simpa only [neg_mul] using exp_neg_le_inv_of_le_exp (by positivity) hbound

theorem faceLowerFormula_ge_exp_square {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    Real.exp (-10 * (k : ℝ) ^ 2) ≤
      (1 / (2 * (k : ℝ))) ^ 2 * (1 / (2 * sieveProfileScale k)) ^ j / 4 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hjR : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le (profile_scales_bounds hk hlog).1
  have hfirst := pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_two_mul_le_inv_two_mul hkpos) 2
  have hmass := pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_two_mul_le_inv_profileScale hk hlog) j
  have hfour : Real.exp (-4) ≤ (1 / 4 : ℝ) :=
    exp_neg_le_inv_of_le_exp (by norm_num) (by linarith [Real.add_one_le_exp 4])
  have hproduct : Real.exp (-2 * (k : ℝ)) ^ 2 * Real.exp (-2 * (k : ℝ)) ^ j * Real.exp (-4) ≤
      (1 / (2 * (k : ℝ))) ^ 2 * (1 / (2 * sieveProfileScale k)) ^ j / 4 := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul (mul_le_mul hfirst hmass (by positivity) (by positivity)) hfour
        (Real.exp_pos _).le (by positivity)
  apply le_trans _ hproduct
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_monotone
  norm_num
  have hjmul := mul_le_mul_of_nonneg_left hjR hkpos.le
  nlinarith

theorem dimensionFaceEnergy_ge_exp_square {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    Real.exp (-10 * (k : ℝ) ^ 2) ≤ dimensionFaceEnergy k j :=
  (faceLowerFormula_ge_exp_square hk hlog hj).trans (dimensionFaceEnergy_explicit_lower hk hlog hj)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.faceLowerFormula_ge_exp_square
#print axioms Erdos4b.FGKMT.dimensionFaceEnergy_ge_exp_square
