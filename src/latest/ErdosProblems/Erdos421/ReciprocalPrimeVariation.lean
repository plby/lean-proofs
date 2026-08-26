import ErdosProblems.Erdos421.ReciprocalPrimeWeight

/-! # A uniform variation bound on a fixed logarithmic prime band -/

namespace Erdos421

open MeasureTheory

theorem reciprocalPrimeWeight_variation_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hlog : 1 ≤ Real.log a) (hscale : Real.log b ≤ 3 * Real.log a) :
    b * |reciprocalPrimeWeight b| + a * |reciprocalPrimeWeight a| +
      (∫ t in a..b, t * |deriv reciprocalPrimeWeight t|) ≤ 6 := by
  have hap : 0 < a := by linarith
  have hb1 := ha.trans_le hab
  have hLa := Real.log_pos ha
  have hLb := Real.log_pos hb1
  have hlogab := Real.log_le_log hap hab
  have hsub : Set.Icc a b ⊆ Set.Ioi 1 := fun _ ht ↦ ha.trans_le ht.1
  have hc := reciprocalPrimeWeight_continuousOn.mono hsub
  have hdc := reciprocalPrimeWeight_deriv_continuousOn.mono hsub
  have hleft : IntervalIntegrable (fun t ↦ t * |deriv reciprocalPrimeWeight t|) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (continuousOn_id.mul hdc.abs)
  have hright : IntervalIntegrable (fun t ↦ 2 * reciprocalPrimeWeight t) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (continuousOn_const.mul hc)
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab hleft hright (by
    intro t ht
    exact reciprocalPrimeWeight_deriv_variation (ha.trans_le ht.1)
      (hlog.trans (Real.log_le_log hap ht.1)))
  rw [intervalIntegral.integral_const_mul, reciprocalPrimeWeight_integral ha hb1] at hm
  have hratio : Real.log b / Real.log a ≤ 3 := (div_le_iff₀ hLa).mpr hscale
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hLb hLa)
  have hlog2 : Real.log (Real.log b / Real.log a) ≤ 2 := by linarith
  have hea := reciprocalPrimeWeight_endpoint_le ha hlog
  have heb := reciprocalPrimeWeight_endpoint_le hb1 (hlog.trans hlogab)
  linarith

end Erdos421
