import BoundedGaps.Maynard.LogarithmicAbelMain

/-!
# Abel transfer for decreasing nonnegative weights

For such weights, the endpoint value plus total variation equals the
initial value. The approximation error consequently needs only that value.
-/

namespace Erdos964

open BoundedGaps.Maynard MeasureTheory

theorem decreasing_log_weighted_abel_error (Q : ℕ) (hQ : 1 ≤ Q)
    (c : ℕ → ℝ) (hc : c 0 = 0) (S E : ℝ) (hE : 0 ≤ E) (f : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.Icc (1 : ℝ) Q, HasDerivAt f (deriv f t) t)
    (hdcont : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) Q))
    (hdneg : ∀ t ∈ Set.Icc (1 : ℝ) Q, deriv f t ≤ 0) (hend : 0 ≤ f Q)
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q, |abelCumulative c t - S * Real.log t| ≤ E) :
    |(∑ n ∈ Finset.Icc 0 Q, f n * c n) - logarithmicAbelMain Q S f| ≤ E * f 1 := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hdint : IntervalIntegrable (deriv f) volume 1 Q :=
    hdcont.intervalIntegrable_of_Icc hQR
  have hnormint : IntegrableOn (fun t => |deriv f t|) (Set.Ioc (1 : ℝ) Q) := by
    have h : IntegrableOn (fun t => ‖deriv f t‖) (Set.Ioc (1 : ℝ) Q) volume :=
      hdcont.norm.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    simpa only [Real.norm_eq_abs] using h
  have hmainint : IntegrableOn (fun t => deriv f t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) Q) :=
    (hdcont.mul (continuousOn_const.mul (continuousOn_id.log
      (fun t ht => (zero_lt_one.trans_le ht.1).ne')))).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hint : (∫ t in (1 : ℝ)..Q, deriv f t) = f Q - f 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
      hderiv t (by simpa only [Set.uIcc_of_le hQR] using ht)) hdint
  have hvariation : (∫ t in Set.Ioc (1 : ℝ) Q, |deriv f t|) ≤ f 1 - f Q := by
    apply le_of_eq
    calc
      _ = ∫ t in (1 : ℝ)..Q, -(deriv f t) := by
        rw [intervalIntegral.integral_of_le hQR]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact abs_of_nonpos (hdneg t ⟨ht.1.le, ht.2⟩)
      _ = _ := by rw [intervalIntegral.integral_neg, hint]; ring
  have h := abs_weightedSum_sub_logarithmicAbelMain_le hQ hc hE
    (fun t ht => (hderiv t ht).differentiableAt) hdcont.integrableOn_Icc hnormint hmainint
    happrox hvariation
  have hfactor : |f Q| + (f 1 - f Q) = f 1 := by rw [abs_of_nonneg hend]; ring
  rwa [hfactor] at h

end Erdos964
