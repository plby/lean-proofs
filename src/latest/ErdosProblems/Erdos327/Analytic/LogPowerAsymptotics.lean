import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic power asymptotics

The parameter selection and the scheduled dyadic sums repeatedly use the
fact that a negative power of `log x` dominates every fixed real power of
`log (log x)`.
-/

namespace Erdos327.Analytic

open Filter Real Topology Asymptotics

noncomputable section

/-- A negative real power dominates every fixed real power of the
logarithm. -/
theorem tendsto_rpow_neg_mul_log_rpow_atTop
    {η : ℝ} (hη : 0 < η) (m : ℝ) :
    Tendsto (fun x : ℝ ↦ x ^ (-η) * log x ^ m)
      atTop (𝓝 0) := by
  have h :=
    (isLittleO_log_rpow_rpow_atTop m hη).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_neg hx.le]
  ring

/-- After composing with `log`, a negative power of `log x` dominates
every fixed real power of `log (log x)`. -/
theorem tendsto_log_rpow_neg_mul_loglog_rpow_atTop
    {η : ℝ} (hη : 0 < η) (m : ℝ) :
    Tendsto
      (fun x : ℝ ↦
        log x ^ (-η) * log (log x) ^ m)
      atTop (𝓝 0) := by
  exact
    (tendsto_rpow_neg_mul_log_rpow_atTop hη m).comp
      Real.tendsto_log_atTop

/-- Exponentiating a multiple of `log (log x)` at a fixed positive base
is exactly a real power of `log x`. -/
theorem base_rpow_mul_loglog
    {b c x : ℝ} (hb : 0 < b) (hx : 1 < x) :
    b ^ (c * log (log x)) =
      log x ^ (c * log b) := by
  have hlogx : 0 < log x := log_pos hx
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hlogx]
  congr 1
  ring

/-- Negative-exponent companion to `base_rpow_mul_loglog`. -/
theorem base_rpow_neg_mul_loglog
    {b c x : ℝ} (hb : 0 < b) (hx : 1 < x) :
    b ^ (-(c * log (log x))) =
      log x ^ (-(c * log b)) := by
  simpa only [neg_mul] using
    (base_rpow_mul_loglog (b := b) (c := -c) hb hx)

end

end Erdos327.Analytic
