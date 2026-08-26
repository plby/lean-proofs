import ErdosProblems.Erdos421.PrimeScaleSaving
import ErdosProblems.Erdos421.WeightedDirichletMeanSquare

/-! # A prime factor and a bounded Dirichlet polynomial in mean square -/

namespace Erdos421

open Complex MeasureTheory Filter Topology

theorem primeDirichletBlock_vertical_continuous (M N : ℕ) (σ : ℝ) :
    Continuous (fun t : ℝ ↦ primeDirichletBlock M N (σ + t * I)) := by
  have he : (fun t : ℝ ↦ primeDirichletBlock M N (σ + t * I)) =
      fun t : ℝ ↦ ∑ n ∈ (Finset.range N).filter (fun n ↦ (M + n + 1).Prime),
        ((((M + n + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          oscillatoryPhase (Real.log (M + n + 1 : ℕ)) (-t) := by
    funext t
    apply Finset.sum_congr rfl
    intro n _
    rw [← Complex.ofReal_natCast,
      cpow_neg_eq_weighted_phase (by exact_mod_cast (show 0 < M + n + 1 by omega))]
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      add_im, mul_I_im, zero_add]
  rw [he]
  exact continuous_finsetSum _ (fun n _ ↦ continuous_const.mul
    ((oscillatoryPhase_continuous _).comp continuous_neg))

theorem integral_norm_product_le {P Q : ℝ → ℂ} (hP : Continuous P) (hQ : Continuous Q)
    {u v B : ℝ} (huv : u ≤ v) (hQbound : ∀ t ∈ Set.Icc u v, ‖Q t‖ ≤ B) :
    (∫ t in u..v, ‖P t * Q t‖ ^ 2) ≤ B ^ 2 * (∫ t in u..v, ‖P t‖ ^ 2) := by
  calc
    _ ≤ ∫ t in u..v, B ^ 2 * ‖P t‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on huv
        ((hP.mul hQ).norm.pow 2 |>.intervalIntegrable u v)
        ((continuous_const.mul (hP.norm.pow 2)).intervalIntegrable u v)
      intro t ht
      change ‖P t * Q t‖ ^ 2 ≤ B ^ 2 * ‖P t‖ ^ 2
      rw [norm_mul, mul_pow]
      have h := pow_le_pow_left₀ (norm_nonneg (Q t)) (hQbound t ht) 2
      nlinarith [sq_nonneg ‖P t‖]
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem primeFactor_mean_square_bound (S : Finset ℕ) (a : ℕ → ℂ)
    {M U H J : ℕ} (hM : 1 ≤ M) (hS : ∀ n ∈ S, M ≤ n ∧ n ≤ U)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) {σ u v B : ℝ} (hσ : 1 ≤ σ) (huv : u ≤ v)
    (hprime : ∀ t ∈ Set.Icc u v, ‖primeDirichletBlock H J (σ + t * I)‖ ≤ B) :
    (∫ t in u..v, ‖dirichletPolynomial S a (σ + t * I) *
      primeDirichletBlock H J (σ + t * I)‖ ^ 2) ≤
      B ^ 2 * ((v - u + 4 * U * (1 + Real.log U)) * S.card / (M : ℝ) ^ 2) := by
  have hpos : ∀ n ∈ S, 0 < n := fun n hn ↦ by have := (hS n hn).1; omega
  exact (integral_norm_product_le (dirichletPolynomial_vertical_continuous S a hpos σ)
    (primeDirichletBlock_vertical_continuous H J σ) huv hprime).trans
      (mul_le_mul_of_nonneg_left (dirichletPolynomial_mean_square_bounded S a hM hS ha hσ huv)
        (sq_nonneg B))

theorem primeFactor_ambient_mean_square {δ : ℝ} (hδ : 0 < δ)
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ H J : ℕ, (X : ℝ) ^ δ ≤ H → H ≤ X → J ≤ H →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ) (M U : ℕ), 1 ≤ M →
      (∀ n ∈ S, M ≤ n ∧ n ≤ U) → (∀ n ∈ S, ‖a n‖ ≤ 1) →
      ∀ σ u v : ℝ, 1 ≤ σ → (Real.log X) ^ (2 * A + 9) ≤ u → u ≤ v → v ≤ X →
      (∫ t in u..v, ‖dirichletPolynomial S a (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2) ≤
        (ε / (Real.log X) ^ A) ^ 2 *
          ((v - u + 4 * U * (1 + Real.log U)) * S.card / (M : ℝ) ^ 2) := by
  filter_upwards [primeDirichletBlock_ambient_log_saving hδ hA hε] with X hX
  intro H J hXH hHX hJ S a M U hM hS ha σ u v hσ hlo huv hhi
  apply primeFactor_mean_square_bound S a hM hS ha hσ huv
  intro t ht
  have ht0 : 0 ≤ t := (Real.rpow_nonneg (Real.log_natCast_nonneg X) _).trans (hlo.trans ht.1)
  have hst : (σ + (t : ℂ) * I).im = t := by simp
  have hsr : (σ + (t : ℂ) * I).re = σ := by simp
  apply hX H J hXH hHX hJ (σ + t * I) (by simpa only [hsr] using hσ)
  · simpa only [hst, abs_of_nonneg ht0] using hlo.trans ht.1
  · simpa only [hst, abs_of_nonneg ht0] using ht.2.trans hhi

end Erdos421
