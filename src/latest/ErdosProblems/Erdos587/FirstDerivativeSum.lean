import ErdosProblems.Erdos587.Analytic

/-!
# First-derivative exponential sums: the finite algebraic step

Summation by parts bounds a phase sum by the variation of the inverse
successive phase increments. The monotonicity and distance estimates for
those increments are separate analytic inputs.
-/

open scoped BigOperators

namespace Erdos587

lemma sum_weighted_forward_difference (b z : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), b n * (z (n + 1) - z n)) =
      b N * z (N + 1) - b 0 * z 0 -
        ∑ n ∈ Finset.range N, (b (n + 1) - b n) * z (n + 1) := by
  induction N with
  | zero => simp [mul_sub]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

lemma norm_sum_le_of_inverse_difference_variation (z b : ℕ → ℂ) (N : ℕ) {B V : ℝ}
    (hrec : ∀ n ≤ N, b n * (z (n + 1) - z n) = z n)
    (hz : ∀ n ≤ N + 1, ‖z n‖ ≤ 1)
    (hb0 : ‖b 0‖ ≤ B) (hbN : ‖b N‖ ≤ B)
    (hvariation : (∑ n ∈ Finset.range N, ‖b (n + 1) - b n‖) ≤ V) :
    ‖∑ n ∈ Finset.range (N + 1), z n‖ ≤ 2 * B + V := by
  have heq : (∑ n ∈ Finset.range (N + 1), z n) =
      b N * z (N + 1) - b 0 * z 0 -
        ∑ n ∈ Finset.range N, (b (n + 1) - b n) * z (n + 1) := by
    rw [← sum_weighted_forward_difference]
    exact Finset.sum_congr rfl (fun n hn => (hrec n (by have := Finset.mem_range.mp hn; omega)).symm)
  have hsum : ‖∑ n ∈ Finset.range N, (b (n + 1) - b n) * z (n + 1)‖ ≤ V := by
    apply (norm_sum_le _ _).trans
    apply le_trans _ hvariation
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hz (n + 1) (by have := Finset.mem_range.mp hn; omega))
  have hfirst : ‖b N * z (N + 1)‖ ≤ B := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hz _ le_rfl)).trans hbN
  have hlast : ‖b 0 * z 0‖ ≤ B := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hz _ (by omega))).trans hb0
  rw [heq]
  calc
    _ ≤ ‖b N * z (N + 1) - b 0 * z 0‖ +
        ‖∑ n ∈ Finset.range N, (b (n + 1) - b n) * z (n + 1)‖ := norm_sub_le _ _
    _ ≤ (‖b N * z (N + 1)‖ + ‖b 0 * z 0‖) + V :=
      add_le_add (norm_sub_le _ _) hsum
    _ ≤ 2 * B + V := by linarith

lemma inverse_phase_increment_recurrence (f : ℕ → ℝ) (n : ℕ)
    (hne : phase (f (n + 1) - f n) ≠ 1) :
    (phase (f (n + 1) - f n) - 1)⁻¹ * (phase (f (n + 1)) - phase (f n)) = phase (f n) := by
  have hdiff : phase (f (n + 1)) - phase (f n) =
      (phase (f (n + 1) - f n) - 1) * phase (f n) := by
    rw [sub_mul, one_mul, ← phase_add]
    congr 1
    congr 1
    ring
  rw [hdiff, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_mul]

theorem norm_phase_sum_le_of_inverse_increment_variation (f : ℕ → ℝ) (N : ℕ) {B V : ℝ}
    (hne : ∀ n ≤ N, phase (f (n + 1) - f n) ≠ 1)
    (hb0 : ‖(phase (f 1 - f 0) - 1)⁻¹‖ ≤ B)
    (hbN : ‖(phase (f (N + 1) - f N) - 1)⁻¹‖ ≤ B)
    (hvariation : (∑ n ∈ Finset.range N,
      ‖(phase (f (n + 2) - f (n + 1)) - 1)⁻¹ -
        (phase (f (n + 1) - f n) - 1)⁻¹‖) ≤ V) :
    ‖∑ n ∈ Finset.range (N + 1), phase (f n)‖ ≤ 2 * B + V := by
  apply norm_sum_le_of_inverse_difference_variation (fun n => phase (f n))
    (fun n => (phase (f (n + 1) - f n) - 1)⁻¹) N
  · intro n hn
    exact inverse_phase_increment_recurrence f n (hne n hn)
  · intro n hn
    exact (norm_phase _).le
  · exact hb0
  · exact hbN
  · simpa only [Nat.add_assoc] using hvariation

lemma norm_sub_eq_abs_im_sub_of_re_eq {z w : ℂ} (hre : z.re = w.re) :
    ‖z - w‖ = |z.im - w.im| := by
  have heq : z - w = ((z.im - w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hre]
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]

lemma inverse_increment_variation_of_monotone_im (b : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hre : ∀ n ≤ N, (b n).re = (b 0).re)
    (him : ∀ n < N, (b n).im ≤ (b (n + 1)).im)
    (hb0 : ‖b 0‖ ≤ B) (hbN : ‖b N‖ ≤ B) :
    (∑ n ∈ Finset.range N, ‖b (n + 1) - b n‖) ≤ 2 * B := by
  have hterm (n : ℕ) (hn : n < N) : ‖b (n + 1) - b n‖ = (b (n + 1)).im - (b n).im := by
    rw [norm_sub_eq_abs_im_sub_of_re_eq ((hre _ (by omega)).trans (hre _ (by omega)).symm),
      abs_of_nonneg (sub_nonneg.mpr (him n hn))]
  have htel (M : ℕ) : (∑ n ∈ Finset.range M, ((b (n + 1)).im - (b n).im)) =
      (b M).im - (b 0).im := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ = ∑ n ∈ Finset.range N, ((b (n + 1)).im - (b n).im) :=
      Finset.sum_congr rfl (fun n hn => hterm n (Finset.mem_range.mp hn))
    _ = (b N).im - (b 0).im := htel N
    _ ≤ 2 * B := by
      have hh0 := Complex.abs_im_le_norm (b 0)
      have hhN := Complex.abs_im_le_norm (b N)
      linarith [le_abs_self (b N).im, neg_le_abs (b 0).im]

theorem norm_sum_le_of_monotone_inverse_differences (z b : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hrec : ∀ n ≤ N, b n * (z (n + 1) - z n) = z n)
    (hz : ∀ n ≤ N + 1, ‖z n‖ ≤ 1)
    (hre : ∀ n ≤ N, (b n).re = (b 0).re)
    (him : ∀ n < N, (b n).im ≤ (b (n + 1)).im)
    (hb0 : ‖b 0‖ ≤ B) (hbN : ‖b N‖ ≤ B) :
    ‖∑ n ∈ Finset.range (N + 1), z n‖ ≤ 4 * B := by
  have hh := norm_sum_le_of_inverse_difference_variation z b N hrec hz hb0 hbN
    (inverse_increment_variation_of_monotone_im b N hre him hb0 hbN)
  linarith

end Erdos587
