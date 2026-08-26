import Mathlib.Analysis.Complex.JensenFormula

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Metric Real Set

namespace CofiniteDerivatives

/-- The Jensen boundary-minus-center logarithmic statistic for a disk. -/
noncomputable def diskLogStat (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
  circleAverage (fun z ↦ Real.log ‖f z‖) c r - Real.log ‖f c‖

/-- A zero-free analytic function has vanishing Jensen statistic. This is the deterministic bridge
from a hole event to a deviation event; no zero-counting measurability is needed. -/
theorem diskLogStat_eq_zero_of_zeroFree {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c |r|))
    (hzero : ∀ z ∈ closedBall c |r|, f z ≠ 0) :
    diskLogStat f c r = 0 := by
  rw [diskLogStat, hf.circleAverage_log_norm_of_ne_zero hzero, sub_self]

/-- Entire sample paths satisfy the analytic hypothesis in the hole-to-deviation bridge. -/
theorem diskLogStat_eq_zero_of_entire_zeroFree {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hzero : ∀ z ∈ closedBall c |r|, f z ≠ 0) :
    diskLogStat f c r = 0 :=
  diskLogStat_eq_zero_of_zeroFree (hf.mono (by simp)) hzero

end CofiniteDerivatives
