import ErdosProblems.Erdos67b.MRSelectedPrimeMass

/-!
# Selected-prime Euler bounds near the line one

The exponential cost depends on the reciprocal mass of the selected set,
not the reciprocal mass of all primes below its largest element.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrInv_one_sub_le_exp_two_mul {r : ℝ} (hr : 0 ≤ r) (hhalf : r ≤ 1 / 2) :
    (1 - r)⁻¹ ≤ Real.exp (2 * r) := by
  have hden : 0 < 1 - r := by linarith
  have hinv : (1 - r)⁻¹ ≤ 1 + 2 * r := by
    have hquot : 1 / (1 - r) ≤ 1 + 2 * r := (div_le_iff₀ hden).2 (by nlinarith)
    simpa only [one_div] using hquot
  apply (Real.log_le_iff_le_exp (inv_pos.mpr hden)).1
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  linarith

theorem mrSelected_eulerProduct_le_exp_mass
    (A : Finset ℕ) (sigma : ℝ)
    (hhalf : ∀ p ∈ A, (p : ℝ) ^ (-sigma) ≤ 1 / 2) :
    (∏ p ∈ A, (1 - (p : ℝ) ^ (-sigma))⁻¹) ≤
      Real.exp (2 * ∑ p ∈ A, (p : ℝ) ^ (-sigma)) := by
  calc
    _ ≤ ∏ p ∈ A, Real.exp (2 * (p : ℝ) ^ (-sigma)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (by linarith [hhalf p hp])
      · intro p hp
        exact mrInv_one_sub_le_exp_two_mul (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hhalf p hp)
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

theorem mrSelected_shiftedPower_le_exp_one_div {p : ℕ} (hp : 0 < p)
    {b : ℝ} (hb : 0 < b) (hlog : Real.log (p : ℝ) ≤ b) :
    (p : ℝ) ^ (-(1 - b⁻¹)) ≤ Real.exp 1 / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hratio : Real.log (p : ℝ) * b⁻¹ ≤ 1 := by
    simpa only [div_eq_mul_inv] using (div_le_one hb).2 hlog
  have hpower : (p : ℝ) ^ (-(1 - b⁻¹)) =
      (p : ℝ)⁻¹ * Real.exp (Real.log (p : ℝ) * b⁻¹) := by
    rw [show -(1 - b⁻¹) = -1 + b⁻¹ by ring, Real.rpow_add hpR,
      Real.rpow_neg_one, Real.rpow_def_of_pos hpR]
  rw [hpower, div_eq_mul_inv, mul_comm (Real.exp 1)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hratio) (inv_nonneg.mpr hpR.le)

theorem mrSelected_eulerProduct_shifted_le_reciprocalMass
    (A : Finset ℕ) {b : ℝ} (hb : 2 ≤ b)
    (hfour : ∀ p ∈ A, 4 ≤ p) (hlog : ∀ p ∈ A, Real.log (p : ℝ) ≤ b) :
    (∏ p ∈ A, (1 - (p : ℝ) ^ (-(1 - b⁻¹)))⁻¹) ≤
      Real.exp (2 * Real.exp 1 * ∑ p ∈ A, 1 / (p : ℝ)) := by
  have hbpos : 0 < b := by linarith
  have hinv : b⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hb
  have hhalf : ∀ p ∈ A, (p : ℝ) ^ (-(1 - b⁻¹)) ≤ 1 / 2 := by
    intro p hp
    have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hfour p hp
    calc
      _ ≤ (4 : ℝ) ^ (-(1 - b⁻¹)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by linarith)
      _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]; norm_num
  apply (mrSelected_eulerProduct_le_exp_mass A (1 - b⁻¹) hhalf).trans
  apply Real.exp_le_exp.mpr
  have hsum : (∑ p ∈ A, (p : ℝ) ^ (-(1 - b⁻¹))) ≤
      Real.exp 1 * ∑ p ∈ A, 1 / (p : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_one_div] using mrSelected_shiftedPower_le_exp_one_div
      (by have := hfour p hp; omega) hbpos (hlog p hp)
  linarith

theorem mrSelected_rankin_exp_cutoff {b tau : ℝ} (hb : 0 < b) :
    (Real.exp (tau * b)) ^ ((1 - b⁻¹) - 1) = Real.exp (-tau) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp
  ring

end

end Erdos67b
