import ErdosProblems.Erdos327.Analytic.SieveScheduleAsymptotic

/-!
# Logarithmic comparison for the sieve schedule

Under the schedule-dominance hypothesis, Euclidean division shows that the
logarithm of the dyadic scale is at most `4096 h²` times the logarithm of
the scheduled prime cutoff.
-/

namespace Erdos327.Analytic

open Real

noncomputable section

/-- Exact logarithm of the dyadic scale. -/
theorem log_dyadicScale (j : ℕ) :
    log (dyadicScale j : ℝ) = (j : ℝ) * log 2 := by
  simp [dyadicScale, Real.log_pow]

/-- Exact logarithm of the scheduled cutoff. -/
theorem log_sieveCutoff (j : ℕ) :
    log (sieveCutoff j : ℝ) =
      (sieveCutoffExponent j : ℝ) * log 2 := by
  simp [sieveCutoff, Real.log_pow]

/-- The cutoff logarithm is positive in the dominant range. -/
theorem log_sieveCutoff_pos
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    0 < log (sieveCutoff j : ℝ) := by
  have hk := two_le_sieveCutoffExponent hdom
  rw [log_sieveCutoff]
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- Lean form of
`log X_j / log z_j < 32 R_j = 4096 h_j²`. -/
theorem log_dyadicScale_lt_height_sq_mul_log_sieveCutoff
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    log (dyadicScale j : ℝ) <
      (4096 : ℝ) * (sieveHeight j : ℝ) ^ 2 *
        log (sieveCutoff j : ℝ) := by
  have hnat :=
    lt_thirtytwo_mul_radius_mul_cutoffExponent hdom
  have hreal :
      (j : ℝ) <
        32 * (sieveRadius j : ℝ) *
          (sieveCutoffExponent j : ℝ) := by
    exact_mod_cast hnat
  have hlog2 : 0 < log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  rw [log_dyadicScale, log_sieveCutoff]
  have hradius :
      (sieveRadius j : ℝ) =
        128 * (sieveHeight j : ℝ) ^ 2 := by
    simp [sieveRadius]
  rw [hradius] at hreal
  nlinarith

/-- Non-strict ratio form used by the product-envelope estimates. -/
theorem log_dyadicScale_div_log_sieveCutoff_le
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    log (dyadicScale j : ℝ) /
        log (sieveCutoff j : ℝ) ≤
      (4096 : ℝ) * (sieveHeight j : ℝ) ^ 2 := by
  exact (div_le_iff₀ (log_sieveCutoff_pos hdom)).2
    (log_dyadicScale_lt_height_sq_mul_log_sieveCutoff hdom).le

/-- A negative power at the smaller denominator loses at most the
corresponding power of a ratio bound. -/
theorem rpow_neg_le_ratio_rpow
    {x z H r : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hH : 1 ≤ H) (hr : 0 ≤ r)
    (hratio : x / z ≤ H) :
    z ^ (-r) ≤ H ^ r * x ^ (-r) := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hmul : x ≤ H * z :=
    (div_le_iff₀ hz).1 hratio
  have hbase : x / H ≤ z := by
    exact (div_le_iff₀ hHpos).2 (by simpa [mul_comm] using hmul)
  have hpow :=
    Real.rpow_le_rpow_of_nonpos (div_pos hx hHpos)
      hbase (neg_nonpos.mpr hr)
  rw [Real.div_rpow hx.le hHpos.le, Real.rpow_neg hHpos.le] at hpow
  simpa [div_inv_eq_mul, mul_comm] using hpow

end

end Erdos327.Analytic
