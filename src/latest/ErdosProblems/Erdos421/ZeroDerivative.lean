import ErdosProblems.Erdos421.CanonicalResidual
import ErdosProblems.Erdos421.LogDerivativeBound
import Mathlib.Analysis.Calculus.LogDeriv

/-! # The logarithmic derivative as a sum over nearby zeros -/

namespace Erdos421

open Complex ComplexConjugate Filter MeromorphicOn Metric Set Topology

theorem logDeriv_canonicalFactor_zero {R : ℝ} {w : ℂ} (hR : R ≠ 0) (hw : w ≠ 0) :
    logDeriv (canonicalFactor R w) 0 = 1 / w - conj w / (R : ℂ) ^ 2 := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hn : HasDerivAt (fun z : ℂ ↦ (R : ℂ) ^ 2 - conj w * z) (-conj w) 0 := by
    convert! (hasDerivAt_const (0 : ℂ) ((R : ℂ) ^ 2)).sub
      ((hasDerivAt_id (0 : ℂ)).const_mul (conj w)) using 1
    ring
  have hd : HasDerivAt (fun z : ℂ ↦ (R : ℂ) * (z - w)) (R : ℂ) 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).sub_const w).const_mul (R : ℂ) using 1
    ring
  rw [canonicalFactor_def, logDeriv_div]
  · simp only [logDeriv_apply, hn.deriv, hd.deriv, mul_zero, sub_zero, zero_sub, mul_neg]
    field_simp
    ring
  · simp only [mul_zero, sub_zero, ne_eq, pow_eq_zero_iff (by decide : 2 ≠ 0)]
    exact hRc
  · exact mul_ne_zero hRc (sub_ne_zero.mpr (Ne.symm hw))
  · exact hn.differentiableAt
  · exact hd.differentiableAt

theorem logDeriv_canonicalProduct_zero {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    logDeriv (canonicalProduct f R) 0 =
      ∑ w ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        (divisor f (ball 0 R) w : ℂ) * (-1 / w + conj w / (R : ℂ) ^ 2) := by
  classical
  let S := hf.meromorphicOn.divisor_ball_support_finite.toFinset
  have hdiv0 := divisor_zero_of_ne_zero hf (mem_closedBall_self hR.le) hf0
  have hwprop : ∀ w ∈ S, w ∈ ball (0 : ℂ) R ∧ w ≠ 0 := by
    intro w hw
    have hws := hf.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp hw
    exact ⟨(divisor f (ball 0 R)).supportWithinDomain hws,
      fun he ↦ hws (he ▸ hdiv0)⟩
  have ha : ∀ w ∈ S, AnalyticAt ℂ (canonicalFactor R w) 0 := by
    intro w hw
    exact analyticOnNhd_canonicalFactor R w 0 (Ne.symm (hwprop w hw).2)
  have hn : ∀ w ∈ S, canonicalFactor R w 0 ≠ 0 := by
    intro w hw
    exact canonicalFactor_ne_zero (hwprop w hw).1 (mem_closedBall_self hR.le)
      (Ne.symm (hwprop w hw).2)
  rw [canonicalProduct_eq_prod hf.meromorphicOn]
  have he : (∏ w ∈ S, canonicalFactor R w ^ (-divisor f (ball 0 R) w)) =
      fun z ↦ ∏ w ∈ S, canonicalFactor R w z ^ (-divisor f (ball 0 R) w) := by
    ext z
    simp only [Finset.prod_apply, Pi.pow_apply]
  rw [he]
  rw [logDeriv_prod (f := fun w z : ℂ ↦
    canonicalFactor R w z ^ (-divisor f (ball 0 R) w)) (x := (0 : ℂ))
    (fun w hw ↦ zpow_ne_zero _ (hn w hw))
    (fun w hw ↦ ((ha w hw).zpow (hn w hw)).differentiableAt)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [logDeriv_fun_zpow (ha w hw).differentiableAt,
    logDeriv_canonicalFactor_zero hR.ne' (hwprop w hw).2]
  push_cast
  ring

/-- An explicit local zero detector. The finite sum contains the actual
zeros of `f`, with their multiplicities given by its divisor. -/
theorem logDeriv_sub_zero_sum_bound {f : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0 : f 0 ≠ 0) (hM : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ Real.exp A * ‖f 0‖) :
    ‖logDeriv f 0 -
      ∑ w ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        (divisor f (ball 0 R) w : ℂ) * (-1 / w + conj w / (R : ℂ) ^ 2)‖ ≤
      4 * A / R := by
  obtain ⟨g, D, hg⟩ := exists_analytic_canonicalResidual hR hf hf0
  have h0 : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have hdiv0 := divisor_zero_of_ne_zero hf h0 hf0
  have hp := analyticAt_canonicalProduct h0 hdiv0
  have he := (logDeriv_congr_nhds (canonicalDecomp_eventuallyEq_at hR hf D h0 hdiv0)).eq_of_nhds
  rw [logDeriv_mul 0 (canonicalProduct_ne_zero h0 hdiv0) (D.ne_zero 0 (mem_ball_self hR))
    hp.differentiableAt (hg 0 h0).differentiableAt,
    logDeriv_canonicalProduct_zero hR hf hf0] at he
  rw [he, add_sub_cancel_left]
  apply logarithmic_derivative_bound_on_ball hR hA
    (hg.mono ball_subset_closedBall).differentiableOn D.ne_zero
  intro z hz
  calc
    ‖g z‖ ≤ Real.exp A * ‖f 0‖ := norm_canonicalResidual_le hR hf D hM
      (ball_subset_closedBall hz)
    _ ≤ Real.exp A * ‖g 0‖ := mul_le_mul_of_nonneg_left
      (norm_canonicalResidual_zero_ge hR hf D hf0) (Real.exp_pos A).le

end Erdos421
