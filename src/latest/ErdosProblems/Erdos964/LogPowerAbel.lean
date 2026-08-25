import ErdosProblems.Erdos964.MonotoneLogAbel

/-!
# Logarithmic power moments from a bounded cumulative error
-/

namespace Erdos964

open BoundedGaps.Maynard MeasureTheory

theorem log_power_weighted_abel_error (Q : ℕ) (hQ : 1 ≤ Q)
    (c : ℕ → ℝ) (hc : c 0 = 0) (S E L : ℝ) (hE : 0 ≤ E)
    (hL : Real.log Q ≤ L) (k : ℕ)
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q, |abelCumulative c t - S * Real.log t| ≤ E) :
    |(∑ n ∈ Finset.Icc 0 Q, (L - Real.log n) ^ k * c n) -
      S / (k + 1) * (L ^ (k + 1) - (L - Real.log Q) ^ (k + 1))| ≤ E * L ^ k := by
  let f : ℝ → ℝ := fun t => (L - Real.log t) ^ k
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpos (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) : 0 < t := zero_lt_one.trans_le ht.1
  have hlogle (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) : Real.log t ≤ L :=
    (Real.log_le_log (hpos t ht) ht.2).trans hL
  have hf : ContinuousOn f (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_const.sub (continuousOn_id.log (fun t ht => (hpos t ht).ne'))).pow k
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) :
      HasDerivAt f (-(k : ℝ) * (L - Real.log t) ^ (k - 1) / t) t := by
    have h := ((Real.hasDerivAt_log (hpos t ht).ne').const_sub L).pow k
    simpa only [f, Pi.pow_def, div_eq_mul_inv, mul_neg, neg_mul] using h
  have hdcont : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) Q) := by
    have hformula : ContinuousOn
        (fun t : ℝ => -(k : ℝ) * (L - Real.log t) ^ (k - 1) / t)
        (Set.Icc (1 : ℝ) Q) :=
      (continuousOn_const.mul ((continuousOn_const.sub
        (continuousOn_id.log (fun t ht => (hpos t ht).ne'))).pow (k - 1))).div
        continuousOn_id (fun t ht => (hpos t ht).ne')
    exact hformula.congr (fun t ht => (hderiv t ht).deriv)
  have hdneg (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) : deriv f t ≤ 0 := by
    rw [(hderiv t ht).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k))
        (pow_nonneg (sub_nonneg.mpr (hlogle t ht)) _)) (hpos t ht).le
  have hend : 0 ≤ f Q := pow_nonneg (sub_nonneg.mpr hL) k
  have h := decreasing_log_weighted_abel_error Q hQ c hc S E hE f
    (fun t ht => (hderiv t ht).differentiableAt.hasDerivAt) hdcont hdneg hend happrox
  have hmain : logarithmicAbelMain Q S f =
      S / (k + 1) * (L ^ (k + 1) - (L - Real.log Q) ^ (k + 1)) := by
    rw [logarithmicAbelMain_eq_intervalIntegral_div hQ hf
      (fun t ht => (hderiv t ht).differentiableAt.hasDerivAt)
      (hdcont.intervalIntegrable_of_Icc hQR)]
    have hSint : IntervalIntegrable (fun t => f t * (S / t)) volume 1 Q :=
      (hf.mul (continuousOn_const.div continuousOn_id
        (fun t ht => (hpos t ht).ne'))).intervalIntegrable_of_Icc hQR
    have hkn : (k : ℝ) + 1 ≠ 0 := by positivity
    have hprim (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) Q) :
        HasDerivAt (fun t : ℝ => -(S / (k + 1)) * (L - Real.log t) ^ (k + 1))
          (f t * (S / t)) t := by
      have ht' : t ∈ Set.Icc (1 : ℝ) Q := by simpa only [Set.uIcc_of_le hQR] using ht
      have hd := (((Real.hasDerivAt_log (hpos t ht').ne').const_sub L).pow (k + 1)).const_mul
        (-(S / (k + 1)))
      simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hd
      have hid : -(S / (k + 1)) * (((k : ℝ) + 1) * (L - Real.log t) ^ k * (-t⁻¹)) =
          f t * (S / t) := by
        dsimp only [f]
        field_simp
      rw [hid] at hd
      exact hd
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hSint
    rw [hint]
    simp only [Real.log_one, sub_zero]
    ring
  rw [hmain] at h
  simpa only [f, Real.log_one, sub_zero] using h

end Erdos964
