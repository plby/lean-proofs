import ErdosProblems.Erdos421.ZetaBlocks
import ErdosProblems.Erdos421.MeanSquare

/-! # Mean squares for Dirichlet polynomials on vertical lines -/

namespace Erdos421

open Complex MeasureTheory

noncomputable def dirichletPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * (n : ℂ) ^ (-s)

theorem dirichletPolynomial_eq_exponentialSum (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ t : ℝ) :
    dirichletPolynomial S a (σ + t * I) =
      exponentialSum S (fun n ↦ a n * ((n : ℝ) ^ (-σ) : ℝ)) (fun n ↦ Real.log n) (-t) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.ofReal_natCast, cpow_neg_eq_weighted_phase (by exact_mod_cast hS n hn)]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
    add_im, mul_I_im, zero_add]
  ring

theorem dirichletPolynomial_vertical_continuous (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ : ℝ) :
    Continuous (fun t : ℝ ↦ dirichletPolynomial S a (σ + t * I)) := by
  simp_rw [dirichletPolynomial_eq_exponentialSum S a hS σ]
  exact (exponentialSum_continuous S _ _).comp continuous_neg

theorem dirichletPolynomial_mean_square (S : Finset ℕ) (a : ℕ → ℂ) {U : ℕ}
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ U) (σ u v : ℝ) :
    (∫ t in u..v, ‖dirichletPolynomial S a (σ + t * I)‖ ^ 2) ≤
      (v - u + 4 * U * (1 + Real.log U)) *
        (∑ n ∈ S, ‖a n * ((n : ℝ) ^ (-σ) : ℝ)‖ ^ 2) := by
  simp_rw [dirichletPolynomial_eq_exponentialSum S a (fun n hn ↦ (hS n hn).1) σ]
  rw [intervalIntegral.integral_comp_neg (f := fun t : ℝ ↦
    ‖exponentialSum S (fun n ↦ a n * ((n : ℝ) ^ (-σ) : ℝ)) (fun n ↦ Real.log n) t‖ ^ 2)]
  have h := dirichlet_mean_square_bound S (fun n ↦ a n * ((n : ℝ) ^ (-σ) : ℝ))
    hS (-v) (-u)
  convert h using 1
  ring

theorem dirichletCoefficient_norm_le {M n : ℕ} (hM : 1 ≤ M) (hn : M ≤ n)
    {a : ℂ} (ha : ‖a‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ) :
    ‖a * ((n : ℝ) ^ (-σ) : ℝ)‖ ≤ (M : ℝ)⁻¹ := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hM.trans hn
  rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hnp.le _)]
  calc
    _ ≤ 1 * (n : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hnp.le _)
    _ = (n : ℝ) ^ (-σ) := one_mul _
    _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hσ)
    _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ _ := inv_anti₀ hMp (by exact_mod_cast hn)

theorem dirichletPolynomial_mean_square_bounded (S : Finset ℕ) (a : ℕ → ℂ)
    {M U : ℕ} (hM : 1 ≤ M) (hS : ∀ n ∈ S, M ≤ n ∧ n ≤ U)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) {σ u v : ℝ} (hσ : 1 ≤ σ) (huv : u ≤ v) :
    (∫ t in u..v, ‖dirichletPolynomial S a (σ + t * I)‖ ^ 2) ≤
      (v - u + 4 * U * (1 + Real.log U)) * S.card / (M : ℝ) ^ 2 := by
  have hpos : ∀ n ∈ S, 0 < n ∧ n ≤ U := fun n hn ↦
    ⟨by have := (hS n hn).1; omega, (hS n hn).2⟩
  have hcoeff : (∑ n ∈ S, ‖a n * ((n : ℝ) ^ (-σ) : ℝ)‖ ^ 2) ≤
      (S.card : ℝ) * ((M : ℝ)⁻¹) ^ 2 := by
    calc
      _ ≤ ∑ _n ∈ S, ((M : ℝ)⁻¹) ^ 2 := Finset.sum_le_sum fun n hn ↦
        pow_le_pow_left₀ (norm_nonneg _)
          (dirichletCoefficient_norm_le hM (hS n hn).1 (ha n hn) hσ) 2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hfactor : 0 ≤ v - u + 4 * U * (1 + Real.log U) := by
    have := Real.log_natCast_nonneg U
    positivity
  calc
    _ ≤ (v - u + 4 * U * (1 + Real.log U)) *
        (∑ n ∈ S, ‖a n * ((n : ℝ) ^ (-σ) : ℝ)‖ ^ 2) :=
      dirichletPolynomial_mean_square S a hpos σ u v
    _ ≤ (v - u + 4 * U * (1 + Real.log U)) *
        ((S.card : ℝ) * ((M : ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hcoeff hfactor
    _ = _ := by simp only [div_eq_mul_inv, inv_pow]; ring

end Erdos421
