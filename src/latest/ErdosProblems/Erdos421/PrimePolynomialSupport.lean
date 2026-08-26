import ErdosProblems.Erdos421.PrimeFactorMeanSquare
import Mathlib.Algebra.BigOperators.Intervals

/-! # Prime blocks as Dirichlet polynomials with a finite positive support -/

namespace Erdos421

open Complex

def primeBlockSupport (M N : ℕ) : Finset ℕ := (Finset.Ioc M (M + N)).filter Nat.Prime

theorem primeDirichletBlock_eq_polynomial (M N : ℕ) (s : ℂ) :
    primeDirichletBlock M N s = dirichletPolynomial (primeBlockSupport M N) (fun _ ↦ 1) s := by
  classical
  unfold primeDirichletBlock dirichletPolynomial primeBlockSupport
  simp only [one_mul, Finset.sum_filter]
  have he : Finset.Ioc M (M + N) = Finset.Ico (M + 1) (M + N + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sum_range,
    show M + N + 1 - (M + 1) = N by omega]
  apply Finset.sum_congr rfl
  intro n _
  rw [show M + 1 + n = M + n + 1 by omega]

theorem primeBlockSupport_bounds {M N : ℕ} (hN : N ≤ M) :
    ∀ n ∈ primeBlockSupport M N, M ≤ n ∧ n ≤ 2 * M := by
  intro n hn
  have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
  omega

theorem primeBlockSupport_card_le (M N : ℕ) : (primeBlockSupport M N).card ≤ N := by
  have h := Finset.card_filter_le (Finset.Ioc M (M + N)) Nat.Prime
  simpa only [primeBlockSupport, Nat.card_Ioc, Nat.add_sub_cancel_left] using h

theorem dirichletPolynomial_norm_le_card (S : Finset ℕ) (a : ℕ → ℂ)
    {M : ℕ} (hM : 1 ≤ M) (hS : ∀ n ∈ S, M ≤ n) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) (t : ℝ) :
    ‖dirichletPolynomial S a (σ + t * I)‖ ≤ (S.card : ℝ) / M := by
  have hpos : ∀ n ∈ S, 0 < n := fun n hn ↦ by have := hS n hn; omega
  rw [dirichletPolynomial_eq_exponentialSum S a hpos σ t]
  calc
    _ ≤ ∑ n ∈ S, ‖a n * ((n : ℝ) ^ (-σ) : ℝ) * oscillatoryPhase (Real.log n) (-t)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ S, ‖a n * ((n : ℝ) ^ (-σ) : ℝ)‖ := by
      simp only [norm_mul, norm_oscillatoryPhase, mul_one]
    _ ≤ ∑ _n ∈ S, (M : ℝ)⁻¹ := Finset.sum_le_sum fun n hn ↦
      dirichletCoefficient_norm_le hM (hS n hn) (ha n hn) hσ
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem dirichletPolynomial_norm_le_one (S : Finset ℕ) (a : ℕ → ℂ)
    {M : ℕ} (hM : 1 ≤ M) (hS : ∀ n ∈ S, M ≤ n) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    (hcard : S.card ≤ M) {σ : ℝ} (hσ : 1 ≤ σ) (t : ℝ) :
    ‖dirichletPolynomial S a (σ + t * I)‖ ≤ 1 := by
  apply (dirichletPolynomial_norm_le_card S a hM hS ha hσ t).trans
  exact (div_le_one (by exact_mod_cast (show 0 < M by omega))).mpr (by exact_mod_cast hcard)

end Erdos421
