import ErdosProblems.Erdos421.PrimeCofactorTwoWindows
import ErdosProblems.Erdos421.LogarithmicPrimeCofactors

/-! # Product windows as actual weighted integer kernels -/

namespace Erdos421

theorem scaledProductWindow_sigma_one (S T : Finset ℕ) (a b : ℕ → ℂ)
    (hS : ∀ m ∈ S, 0 < m) (hT : ∀ n ∈ T, 0 < n) (δ y : ℝ) :
    scaledProductWindow S T a b 1 oneSidedSchwartzWindow δ y =
      ∑ m ∈ S, ∑ n ∈ T, (a m * b n) * logarithmicIntegerWeight δ y (m * n) := by
  unfold scaledProductWindow
  simp only [Real.rpow_neg_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hmp : (0 : ℝ) < m := by exact_mod_cast hS m hm
  have hnp : (0 : ℝ) < n := by exact_mod_cast hT n hn
  simp only [logarithmicIntegerWeight, Nat.cast_mul, mul_inv,
    Real.log_mul hmp.ne' hnp.ne', sub_add_eq_sub_sub, Complex.real_smul,
    Complex.ofReal_mul]
  ring

theorem scaledProductWindow_real_coefficients (S T : Finset ℕ) (a : ℕ → ℝ)
    (hS : ∀ m ∈ S, 0 < m) (hT : ∀ p ∈ T, 0 < p) (δ y : ℝ) :
    (scaledProductWindow S T (fun m ↦ (a m : ℂ)) (fun _ ↦ 1)
      1 oneSidedSchwartzWindow δ y).re =
        ∑ p ∈ T, ∑ m ∈ S, a m * (logarithmicIntegerWeight δ y (p * m)).re := by
  rw [scaledProductWindow_sigma_one S T _ _ hS hT, Complex.re_sum]
  simp only [Complex.re_sum, mul_one, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_comm m p]

end Erdos421
