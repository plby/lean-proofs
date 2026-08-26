import ErdosProblems.Erdos67b.MRSparsePrimeEnergy

/-! # An absolute logarithmic prime-block mass bound from the fixed sieve -/

open Filter
open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrPrimeBlockMassConstant : ℝ :=
  4000 / mrPrimeSieveExponent 2 + mrPrimeKernelErrorConstant 2

theorem mrPrimeBlockMassConstant_pos : 0 < mrPrimeBlockMassConstant := by
  have := mrPrimeSieveExponent_pos 2
  have := mrPrimeKernelErrorConstant_pos 2
  unfold mrPrimeBlockMassConstant
  positivity

theorem mrNorm_smoothPrimeKernel_zero_eq_weightMass (D : ℕ) (hD : 1 ≤ D) (P : ℝ) :
    ‖mrSmoothPrimeSelbergKernel D hD P 0‖ =
      ∑ n ∈ mrSmoothPrimeKernelSupport P, mrSmoothPrimeSieveWeight D hD P n := by
  have heq : mrSmoothPrimeSelbergKernel D hD P 0 =
      ((∑ n ∈ mrSmoothPrimeKernelSupport P, mrSmoothPrimeSieveWeight D hD P n : ℝ) : ℂ) := by
    simp [mrSmoothPrimeSelbergKernel, mrSmoothPrimeSieveWeight, mrSmoothPrimeKernelIntegrand,
      mrPrimeMellinMonomial, mrPrimeMellinCoefficient, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg fun n _ ↦ mrSmoothPrimeSelbergWeight_nonneg D hD P n)

theorem mrPrimeCard_le_smoothPrimeKernel_zero (D : ℕ) (hD : 1 ≤ D) {P : ℝ}
    (hP : 0 < P) (A : Finset ℕ) (hprime : ∀ p ∈ A, p.Prime)
    (hcutoff : ∀ p ∈ A, D < p) (hblock : ∀ p ∈ A, (p : ℝ) ∈ Set.Icc P (2 * P)) :
    (A.card : ℝ) ≤ ‖mrSmoothPrimeSelbergKernel D hD P 0‖ := by
  rw [mrNorm_smoothPrimeKernel_zero_eq_weightMass]
  calc
    _ = ∑ p ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ A, mrSmoothPrimeSieveWeight D hD P p :=
      Finset.sum_le_sum fun p hp ↦
        mrSmoothPrimeSelbergWeight_ge_one D hD hP (hprime p hp) (hcutoff p hp) (hblock p hp)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun p hp ↦ mrMem_smoothPrimeKernelSupport hP (hblock p hp))
      (fun n _ _ ↦ mrSmoothPrimeSelbergWeight_nonneg D hD P n)

theorem mrEventually_log_le_primeKernelPower :
    ∀ᶠ P : ℝ in atTop, Real.log P ≤ P ^ mrPrimeKernelSaving 2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (isLittleO_log_rpow_atTop (mrPrimeKernelSaving_pos 2)).eventuallyLE] with P hP hh
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hP.le),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ P) _)] using hh

theorem mrExists_primeBlock_card_bound :
    ∃ P₀ : ℝ, 1 < P₀ ∧ ∀ P ≥ P₀,
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, (p : ℝ) ∈ Set.Icc P (2 * P)) →
        (A.card : ℝ) ≤ mrPrimeBlockMassConstant * P / Real.log P := by
  obtain ⟨P₁, hP₁one, hP₁⟩ :=
    mrExists_smoothPrime_powerCutoff_kernel_bound 2 (by norm_num) (h := 1) (by norm_num)
  obtain ⟨P₂, hP₂⟩ := eventually_atTop.1 mrEventually_log_le_primeKernelPower
  refine ⟨max P₁ P₂, hP₁one.trans_le (le_max_left _ _), ?_⟩
  intro P hP A hprime hblock
  have hPfirst : P₁ ≤ P := (le_max_left P₁ P₂).trans hP
  have hPone : 1 < P := hP₁one.trans_le hPfirst
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos hPone
  have hC := mrPrimeKernelErrorConstant_pos 2
  have hsmall := hP₂ P ((le_max_right P₁ P₂).trans hP)
  obtain ⟨hDtwo, hkernel⟩ := hP₁ P hPfirst
  have hD : 1 ≤ mrPrimePowerCutoff 2 P := by omega
  have hcutoff := mrPrimePowerCutoff_lt_scale (R := 2) (by norm_num) hPone
  have hcard := mrPrimeCard_le_smoothPrimeKernel_zero _ hD hPpos A hprime
    (fun p hp ↦ by exact_mod_cast hcutoff.trans_le (hblock p hp).1) hblock
  have hb := hkernel hD 0 (by simp [hPpos.le])
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, mul_one] at hb
  have hpower : P ^ (1 - mrPrimeKernelSaving 2) ≤ P / Real.log P := by
    rw [Real.rpow_sub hPpos, Real.rpow_one]
    exact div_le_div_of_nonneg_left hPpos.le hlogP hsmall
  apply (hcard.trans hb).trans
  calc
    _ ≤ 4000 * P / (mrPrimeSieveExponent 2 * Real.log P) +
        mrPrimeKernelErrorConstant 2 * (P / Real.log P) := by
      gcongr
    _ = mrPrimeBlockMassConstant * P / Real.log P := by
      unfold mrPrimeBlockMassConstant
      field_simp

theorem mrExists_primeBlock_inverse_square_mass :
    ∃ P₀ : ℝ, 1 < P₀ ∧ ∀ P ≥ P₀,
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, (p : ℝ) ∈ Set.Icc P (2 * P)) →
        (∑ p ∈ A, 1 / (p : ℝ) ^ 2) ≤ mrPrimeBlockMassConstant / (P * Real.log P) := by
  obtain ⟨P₀, hP₀one, hP₀⟩ := mrExists_primeBlock_card_bound
  refine ⟨P₀, hP₀one, ?_⟩
  intro P hP A hprime hblock
  have hPpos : 0 < P := by have := hP₀one.trans_le hP; linarith
  have hcard := hP₀ P hP A hprime hblock
  calc
    _ ≤ ∑ p ∈ A, 1 / P ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply one_div_le_one_div_of_le (sq_pos_of_pos hPpos)
      exact pow_le_pow_left₀ hPpos.le (hblock p hp).1 _
    _ = (A.card : ℝ) / P ^ 2 := by simp [div_eq_mul_inv]
    _ ≤ (mrPrimeBlockMassConstant * P / Real.log P) / P ^ 2 :=
      div_le_div_of_nonneg_right hcard (sq_nonneg P)
    _ = mrPrimeBlockMassConstant / (P * Real.log P) := by field_simp

end

end Erdos67b
