import ErdosProblems.Erdos239.External.Erdos67.MRGSA10RpowAverage

/-!
# The two-shift positive exponential average in A.10

This is the real, nonnegative version of the exact complex exponential
average.  It is used after taking norms in the Perron near-mass term: the
two auxiliary integrations recover one reciprocal logarithm of the product
and one reciprocal logarithm of the second distinguished factor.
-/

open MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Exact rectangular average of the positive two-shift exponential. -/
theorem intervalIntegral_intervalIntegral_exp_two_shift_eq
    {L M eta : ℝ} (hLM : L + M ≠ 0) (hM : M ≠ 0) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Real.exp (-alpha * L) *
          Real.exp (-(alpha + 2 * beta) * M)) =
      ((1 - Real.exp (-(L + M) * eta)) / (L + M)) *
        ((1 - Real.exp (-(2 * M) * eta)) / (2 * M)) := by
  have htwoM : 2 * M ≠ 0 := mul_ne_zero (by norm_num) hM
  have hpoint (alpha beta : ℝ) :
      Real.exp (-alpha * L) * Real.exp (-(alpha + 2 * beta) * M) =
        Real.exp (-(L + M) * alpha) *
          Real.exp (-(2 * M) * beta) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1 <;> ring
  simp_rw [hpoint]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral_exp_neg_mul_eq hLM,
    intervalIntegral_exp_neg_mul_eq htwoM]

/-- The exact average is bounded by the product of its two reciprocal
logarithmic scales. -/
theorem intervalIntegral_intervalIntegral_exp_two_shift_le
    {L M eta : ℝ} (hL : 0 < L) (hM : 0 < M) (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Real.exp (-alpha * L) *
          Real.exp (-(alpha + 2 * beta) * M)) ≤
      (L + M)⁻¹ * (2 * M)⁻¹ := by
  rw [intervalIntegral_intervalIntegral_exp_two_shift_eq
    (ne_of_gt (add_pos hL hM)) (ne_of_gt hM)]
  have hLM : 0 < L + M := add_pos hL hM
  have htwoM : 0 < 2 * M := mul_pos (by norm_num) hM
  have hnumLM0 : 0 ≤ 1 - Real.exp (-(L + M) * eta) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hLM.le) heta)
  have hnumLM1 : 1 - Real.exp (-(L + M) * eta) ≤ 1 := by
    linarith [Real.exp_pos (-(L + M) * eta)]
  have hnumM0 : 0 ≤ 1 - Real.exp (-(2 * M) * eta) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htwoM.le) heta)
  have hnumM1 : 1 - Real.exp (-(2 * M) * eta) ≤ 1 := by
    linarith [Real.exp_pos (-(2 * M) * eta)]
  have hfirst :
      (1 - Real.exp (-(L + M) * eta)) / (L + M) ≤ (L + M)⁻¹ := by
    rw [div_eq_mul_inv]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hnumLM1 (inv_nonneg.mpr hLM.le)
  have hsecond :
      (1 - Real.exp (-(2 * M) * eta)) / (2 * M) ≤ (2 * M)⁻¹ := by
    rw [div_eq_mul_inv]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hnumM1 (inv_nonneg.mpr htwoM.le)
  exact mul_le_mul hfirst hsecond
    (mul_nonneg hnumM0 (inv_nonneg.mpr htwoM.le))
    (inv_nonneg.mpr hLM.le)

/-- Natural-logarithm specialization for two positive integer factors. -/
theorem intervalIntegral_intervalIntegral_exp_natLog_two_shift_le
    {m n : ℕ} {eta : ℝ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Real.exp (-alpha * Real.log m) *
          Real.exp (-(alpha + 2 * beta) * Real.log n)) ≤
      (Real.log m + Real.log n)⁻¹ * (2 * Real.log n)⁻¹ := by
  exact intervalIntegral_intervalIntegral_exp_two_shift_le
    (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))) heta

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.intervalIntegral_intervalIntegral_exp_natLog_two_shift_le
