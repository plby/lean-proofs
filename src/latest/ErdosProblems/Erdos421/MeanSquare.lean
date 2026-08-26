import ErdosProblems.Erdos421.HarmonicRows

/-! # An elementary mean-square bound with a logarithmic loss -/

namespace Erdos421

open Complex MeasureTheory
open scoped ComplexConjugate

theorem symmetric_weighted_sum_le (S : Finset ℕ) (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    {R : ℝ} (hw : ∀ m n, 0 ≤ w m n) (hsym : ∀ m n, w m n = w n m)
    (hrow : ∀ m ∈ S, (∑ n ∈ S, w m n) ≤ R) :
    (∑ m ∈ S, ∑ n ∈ S, 2 * x m * x n * w m n) ≤ 2 * R * (∑ m ∈ S, x m ^ 2) := by
  have hsplit : (∑ m ∈ S, ∑ n ∈ S, (x m ^ 2 + x n ^ 2) * w m n) =
      2 * (∑ m ∈ S, x m ^ 2 * (∑ n ∈ S, w m n)) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    have hfirst : (∑ m ∈ S, ∑ n ∈ S, x m ^ 2 * w m n) =
        ∑ m ∈ S, x m ^ 2 * (∑ n ∈ S, w m n) := by simp only [Finset.mul_sum]
    have hsecond : (∑ m ∈ S, ∑ n ∈ S, x n ^ 2 * w m n) =
        ∑ m ∈ S, x m ^ 2 * (∑ n ∈ S, w m n) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      simp_rw [hsym _ n, ← Finset.mul_sum]
    rw [hfirst, hsecond]
    ring
  calc
    _ ≤ ∑ m ∈ S, ∑ n ∈ S, (x m ^ 2 + x n ^ 2) * w m n := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (x m - x n)]) (hw m n)
    _ = 2 * (∑ m ∈ S, x m ^ 2 * (∑ n ∈ S, w m n)) := hsplit
    _ ≤ 2 * (∑ m ∈ S, x m ^ 2 * R) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun m hm ↦ mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _))
    _ = 2 * R * (∑ m ∈ S, x m ^ 2) := by rw [← Finset.sum_mul]; ring

theorem dirichlet_mean_square_complex_error (S : Finset ℕ) (c : ℕ → ℂ) {N : ℕ}
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (a b : ℝ) :
    ‖(∫ t in a..b, exponentialSum S c (fun n ↦ Real.log n) t *
        conj (exponentialSum S c (fun n ↦ Real.log n) t)) -
      ((b - a : ℝ) : ℂ) * (∑ m ∈ S, c m * conj (c m))‖ ≤
      4 * N * (1 + Real.log N) * (∑ m ∈ S, ‖c m‖ ^ 2) := by
  classical
  have hω : Set.InjOn (fun n : ℕ ↦ Real.log (n : ℝ)) S := by
    intro m hm n hn heq
    by_contra hmn
    exact logarithmic_frequency_ne (hS m hm).1 (hS n hn).1 hmn (sub_eq_zero.mpr heq)
  apply (exponentialSum_mean_square_error S c _ hω a b).trans
  let w : ℕ → ℕ → ℝ := fun m n ↦ 1 / |Real.log (m : ℝ) - Real.log (n : ℝ)|
  have hrow : ∀ m ∈ S, (∑ n ∈ S, w m n) ≤ 2 * N * (1 + Real.log N) := by
    intro m hm
    have hz : w m m = 0 := by simp [w]
    rw [← Finset.sum_erase _ hz]
    exact sum_inverse_log_difference_le S (hS m hm).1 (hS m hm).2 hS
  have hbound := symmetric_weighted_sum_le S (fun n ↦ ‖c n‖) w
    (fun _ _ ↦ by dsimp only [w]; positivity) (fun m n ↦ by simp only [w, abs_sub_comm]) hrow
  have heq : (∑ m ∈ S, ∑ n ∈ S.erase m,
      2 * ‖c m‖ * ‖c n‖ / |Real.log (m : ℝ) - Real.log (n : ℝ)|) =
      ∑ m ∈ S, ∑ n ∈ S, 2 * ‖c m‖ * ‖c n‖ * w m n := by
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_erase]
    · apply Finset.sum_congr rfl
      intro n _
      dsimp only [w]
      ring
    · simp
  rw [heq]
  nlinarith [hbound]

/-- A classical mean-square estimate for arbitrary complex coefficients,
with the harmless `log N` loss needed by the subsequent sieve estimates. -/
theorem dirichlet_mean_square_bound (S : Finset ℕ) (c : ℕ → ℂ) {N : ℕ}
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (a b : ℝ) :
    (∫ t in a..b, ‖exponentialSum S c (fun n ↦ Real.log n) t‖ ^ 2) ≤
      (b - a + 4 * N * (1 + Real.log N)) * (∑ m ∈ S, ‖c m‖ ^ 2) := by
  have heq : (∫ t in a..b, exponentialSum S c (fun n ↦ Real.log n) t *
      conj (exponentialSum S c (fun n ↦ Real.log n) t)) =
      ((∫ t in a..b, ‖exponentialSum S c (fun n ↦ Real.log n) t‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact intervalIntegral.integral_ofReal
  have hdiag : ((b - a : ℝ) : ℂ) * (∑ m ∈ S, c m * conj (c m)) =
      (((b - a) * (∑ m ∈ S, ‖c m‖ ^ 2) : ℝ) : ℂ) := by
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_mul,
      Complex.ofReal_sum]
  have h := dirichlet_mean_square_complex_error S c hS a b
  rw [heq, hdiag, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  have hle := (le_abs_self _).trans h
  nlinarith

end Erdos421
