import BoundedGaps.Maynard.LogarithmicAbelMain

/-!
# Abel transfer for a decreasing linear function of the logarithm

The endpoint term and total variation add to the initial value `a`.
This is the smooth weight used in the scalar transformed coefficient.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard MeasureTheory

theorem linear_log_weighted_abel_error (Q : ℕ) (hQ : 1 ≤ Q)
    (c : ℕ → ℝ) (hc : c 0 = 0) (S E a b : ℝ) (hE : 0 ≤ E) (hb : 0 ≤ b)
    (hba : b * Real.log Q ≤ a)
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q, |abelCumulative c t - S * Real.log t| ≤ E) :
    |(∑ n ∈ Finset.Icc 0 Q, (a - b * Real.log n) * c n) -
      S * (a * Real.log Q - b / 2 * (Real.log Q) ^ 2)| ≤ E * a := by
  let f : ℝ → ℝ := fun t => a - b * Real.log t
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpos (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) : 0 < t := zero_lt_one.trans_le ht.1
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) : HasDerivAt f (-b / t) t := by
    simpa only [f, div_eq_mul_inv, neg_mul] using
      ((Real.hasDerivAt_log (hpos t ht).ne').const_mul b).const_sub a
  have hf : ContinuousOn f (Set.Icc (1 : ℝ) Q) :=
    continuousOn_const.sub (continuousOn_const.mul
      (continuousOn_id.log (fun t ht => (hpos t ht).ne')))
  have hdcont : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) Q) := by
    have hformula : ContinuousOn (fun t : ℝ => -b / t) (Set.Icc (1 : ℝ) Q) :=
      continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')
    exact hformula.congr (fun t ht => (hderiv t ht).deriv)
  have hdint : IntervalIntegrable (deriv f) volume 1 Q := hdcont.intervalIntegrable_of_Icc hQR
  have hnormint : IntegrableOn (fun t => |deriv f t|) (Set.Ioc (1 : ℝ) Q) := by
    have h : IntegrableOn (fun t => ‖deriv f t‖) (Set.Ioc (1 : ℝ) Q) volume :=
      hdcont.norm.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    simpa only [Real.norm_eq_abs] using h
  have hmainint : IntegrableOn (fun t => deriv f t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) Q) :=
    (hdcont.mul (continuousOn_const.mul
      (continuousOn_id.log (fun t ht => (hpos t ht).ne')))).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hbinvcont : ContinuousOn (fun t : ℝ => b / t) (Set.Icc (1 : ℝ) Q) :=
    continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')
  have hbinvint : IntervalIntegrable (fun t : ℝ => b / t) volume 1 Q :=
    hbinvcont.intervalIntegrable_of_Icc hQR
  have hbinv : (∫ t in (1 : ℝ)..Q, b / t) = b * Real.log Q := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => b * Real.log t) (f' := fun t => b / t)
      (a := (1 : ℝ)) (b := (Q : ℝ)) (fun t ht => by
        have ht' : t ∈ Set.Icc (1 : ℝ) Q := by simpa only [Set.uIcc_of_le hQR] using ht
        simpa only [div_eq_mul_inv] using (Real.hasDerivAt_log (hpos t ht').ne').const_mul b)
      hbinvint
    simpa only [Real.log_one, mul_zero, sub_zero] using h
  have hvar : (∫ t in Set.Ioc (1 : ℝ) Q, |deriv f t|) ≤ b * Real.log Q := by
    apply le_of_eq
    calc
      _ = ∫ t in (1 : ℝ)..Q, b / t := by
        rw [intervalIntegral.integral_of_le hQR]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [(hderiv t ⟨ht.1.le, ht.2⟩).deriv, abs_div, abs_neg,
          abs_of_nonneg hb, abs_of_pos (hpos t ⟨ht.1.le, ht.2⟩)]
      _ = _ := hbinv
  have hmain : logarithmicAbelMain Q S f =
      S * (a * Real.log Q - b / 2 * (Real.log Q) ^ 2) := by
    rw [logarithmicAbelMain_eq_intervalIntegral_div hQ hf
      (fun t ht => (hderiv t ht).differentiableAt.hasDerivAt) hdint]
    have hSint : IntervalIntegrable (fun t => f t * (S / t)) volume 1 Q :=
      (hf.mul (continuousOn_const.div continuousOn_id
        (fun t ht => (hpos t ht).ne'))).intervalIntegrable_of_Icc hQR
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => S * (a * Real.log t - b / 2 * (Real.log t) ^ 2))
      (f' := fun t => f t * (S / t)) (a := (1 : ℝ)) (b := (Q : ℝ))
      (fun t ht => by
        have ht' : t ∈ Set.Icc (1 : ℝ) Q := by simpa only [Set.uIcc_of_le hQR] using ht
        have hd := Real.hasDerivAt_log (hpos t ht').ne'
        have hF := ((hd.const_mul a).sub ((hd.pow 2).const_mul (b / 2))).const_mul S
        simp only [Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat,
          show (2 : ℕ) - 1 = 1 by decide, pow_one] at hF
        have hid : S * (a * t⁻¹ - b / 2 * (2 * Real.log t * t⁻¹)) = f t * (S / t) := by
          dsimp only [f]
          ring
        rw [hid] at hF
        exact hF)
      hSint
    simpa only [Real.log_one, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using h
  have h := abs_weightedSum_sub_logarithmicAbelMain_le hQ hc hE
    (fun t ht => (hderiv t ht).differentiableAt) hdcont.integrableOn_Icc hnormint hmainint
    happrox hvar
  have hend : |f Q| + b * Real.log Q = a := by
    dsimp only [f]
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    ring
  rw [hmain, hend] at h
  exact h

end Erdos964
