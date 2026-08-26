import ErdosProblems.Erdos421.LogLocalizedMoments
import ErdosProblems.Erdos421.PositiveShiftAverage

/-! # A complete-system mean-value estimate for logarithmic exponential sums -/

namespace Erdos421

noncomputable def logarithmicRangeSum (A : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, oscillatoryPhase 1 (t * Real.log (A + n))

theorem logarithmicRangeSum_nat (A N : ℕ) (t : ℝ) :
    logarithmicRangeSum A N t = logarithmicSum A N t := by
  unfold logarithmicRangeSum logarithmicSum
  apply Finset.sum_congr rfl
  intro n _
  unfold oscillatoryPhase
  congr 1
  push_cast
  ring

theorem norm_positive_logPhaseSum (M : ℕ) (t z : ℝ) :
    ‖∑ n ∈ Finset.range M, oscillatoryPhase 1 (t * Real.log (z + ((n : ℝ) + 1)))‖ =
      ‖localLogSum M t z‖ := by
  have heq : (∑ n ∈ Finset.range M,
      oscillatoryPhase 1 (t * Real.log (z + ((n : ℝ) + 1)))) =
        oscillatoryPhase 1 (t * Real.log z) * localLogSum M t z := by
    unfold localLogSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    unfold oscillatoryPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [heq, norm_mul, norm_oscillatoryPhase, one_mul]

noncomputable def logarithmicMomentUpper (k s M N : ℕ) (t A : ℝ) : ℝ :=
  (Real.pi * k) ^ k * k.factorial * (M : ℝ) ^ (k + meanValueTriangle k) *
    (1 + 2 * (A + N) ^ (k + 1) / ((k : ℝ) ^ 2 * |t| * (M : ℝ) ^ k)) *
      (3 : ℝ) ^ (2 * s) * (M + 1 : ℕ) * (vinogradovCount s k M : ℝ)

theorem logarithmicRangeSum_meanValue_bound {k M s : ℕ}
    (hk : 0 < k) (hM : 0 < M) (hs : 0 < s) (N : ℕ)
    {t A : ℝ} (ht : t ≠ 0) (hA : 0 < A) (htA : |t| ≤ A ^ k)
    (hscale : |t| * (M : ℝ) ^ (k + 1) ≤ A ^ (k + 1)) :
    ‖logarithmicRangeSum A N t‖ ≤
      ((N : ℝ) ^ (2 * s - 1) * logarithmicMomentUpper k s M N t A) ^
        (((2 * s : ℕ) : ℝ)⁻¹) / M + 4 * M := by
  let u : ℕ → ℂ := fun n ↦ oscillatoryPhase 1 (t * Real.log (A + n))
  have hshift := positive_short_shift_moment_bound u N hM (Nat.mul_pos (by decide : 0 < 2) hs)
    (fun n _ ↦ (norm_oscillatoryPhase 1 (t * Real.log (A + n))).le)
  have hinner (n : ℕ) : ‖∑ h ∈ Finset.range M, u (n + h + 1)‖ =
      ‖localLogSum M t (A + n)‖ := by
    simpa only [u, Nat.cast_add, Nat.cast_one, add_assoc] using
      norm_positive_logPhaseSum M t (A + n)
  simp_rw [hinner] at hshift
  have hmom : (∑ n ∈ Finset.range N, ‖localLogSum M t (A + n)‖ ^ (2 * s)) ≤
      logarithmicMomentUpper k s M N t A := sum_localLogSum_moments hk hM s N ht hA htA hscale
  exact hshift.trans (add_le_add
    (div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_left hmom (by positivity)) (by positivity)) (Nat.cast_nonneg M)) le_rfl)

end Erdos421
