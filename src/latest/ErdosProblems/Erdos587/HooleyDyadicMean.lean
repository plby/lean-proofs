import Mathlib

/-!
# Finite weak-to-strong dyadic summation

A weak first-moment estimate is summed over finitely many dyadic levels.
A second moment controls the remaining tail, so the number of levels can
be logarithmic in the second-moment scale rather than in the support.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_min_double_le (f t : ℝ) :
    min f (2 * t) ≤ min f t + if t < f then t else 0 := by
  by_cases h : t < f
  · rw [if_pos h, min_eq_right h.le]
    simpa only [two_mul] using min_le_right f (2 * t)
  · rw [if_neg h, min_eq_left (le_of_not_gt h), add_zero]
    exact min_le_left f _

lemma delta_min_dyadic_le (f T : ℝ) (k : ℕ) :
    min f (T * 2 ^ k) ≤ T +
      ∑ j ∈ Finset.range k, if T * 2 ^ j < f then T * 2 ^ j else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h := delta_min_double_le f (T * 2 ^ k)
    rw [show 2 * (T * (2 : ℝ) ^ k) = T * 2 ^ (k + 1) by rw [pow_succ]; ring] at h
    linarith

lemma delta_le_min_add_sq_div (f : ℝ) {M : ℝ} (hM : 0 < M) :
    f ≤ min f M + f ^ 2 / M := by
  by_cases h : f ≤ M
  · rw [min_eq_left h]
    have hnonneg : 0 ≤ f ^ 2 / M := div_nonneg (sq_nonneg f) hM.le
    linarith
  · have hf : M < f := lt_of_not_ge h
    rw [min_eq_right hf.le]
    have hsq : f ≤ f ^ 2 / M := by
      apply (le_div_iff₀ hM).mpr
      nlinarith
    linarith

open Classical in
/-- The weak estimate costs one constant per dyadic level, with the
unsummed tail bounded by the second moment. -/
theorem finite_delta_weak_to_strong {α : Type*} (S : Finset α) (f w : α → ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n) {T M B : ℝ} (hT : 0 < T) (k : ℕ)
    (hweak : ∀ j < k, (∑ n ∈ S.filter (fun n => T * 2 ^ j < f n), w n) ≤ M / 2 ^ j)
    (hsecond : (∑ n ∈ S, f n ^ 2 * w n) ≤ B) :
    (∑ n ∈ S, f n * w n) ≤ T * (∑ n ∈ S, w n) + (k : ℝ) * T * M + B / (T * 2 ^ k) := by
  have hscale : 0 < T * (2 : ℝ) ^ k := by positivity
  have hpoint (n : α) : f n ≤ T +
      (∑ j ∈ Finset.range k, if T * 2 ^ j < f n then T * 2 ^ j else 0) +
        f n ^ 2 / (T * 2 ^ k) := by
    have hmin := delta_min_dyadic_le (f n) T k
    have htail := delta_le_min_add_sq_div (f n) hscale
    linarith
  have hlevels : (∑ n ∈ S,
      (∑ j ∈ Finset.range k, if T * 2 ^ j < f n then T * 2 ^ j else 0) * w n) ≤
        (k : ℝ) * T * M := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _j ∈ Finset.range k, T * M := by
        apply Finset.sum_le_sum
        intro j hj
        have hpow : 0 < (2 : ℝ) ^ j := by positivity
        calc
          _ = (T * 2 ^ j) * ∑ n ∈ S.filter (fun n => T * 2 ^ j < f n), w n := by
            rw [Finset.sum_filter, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            split_ifs <;> ring
          _ ≤ (T * 2 ^ j) * (M / 2 ^ j) :=
            mul_le_mul_of_nonneg_left (hweak j (Finset.mem_range.mp hj)) (by positivity)
          _ = T * M := by field_simp
      _ = _ := by simp; ring
  calc
    _ ≤ ∑ n ∈ S, (T +
        (∑ j ∈ Finset.range k, if T * 2 ^ j < f n then T * 2 ^ j else 0) +
          f n ^ 2 / (T * 2 ^ k)) * w n :=
      Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right (hpoint n) (hw n hn))
    _ = T * (∑ n ∈ S, w n) +
        (∑ n ∈ S, (∑ j ∈ Finset.range k,
          if T * 2 ^ j < f n then T * 2 ^ j else 0) * w n) +
            (∑ n ∈ S, f n ^ 2 * w n) / (T * 2 ^ k) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ _ := add_le_add (add_le_add le_rfl hlevels)
      (div_le_div_of_nonneg_right hsecond hscale.le)

end Erdos587
