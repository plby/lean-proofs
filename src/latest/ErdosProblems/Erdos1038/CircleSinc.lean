import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.Deriv.MeanValue



/-!
# Monotonicity of the sinc function on the circle range

The circle calibration repeatedly uses that `sin x / x` is strictly
decreasing on `(0, π)`.  This file proves that fact by differentiating the
positive auxiliary function `sin x - x cos x`.
-/

open Set Filter
open scoped Topology

namespace Erdos1038

noncomputable section

def sincNumerator (x : ℝ) : ℝ := Real.sin x - x * Real.cos x

@[simp]
lemma sincNumerator_zero : sincNumerator 0 = 0 := by
  simp [sincNumerator]

lemma hasDerivAt_sincNumerator (x : ℝ) :
    HasDerivAt sincNumerator (x * Real.sin x) x := by
  have h := Real.hasDerivAt_sin x |>.sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))
  convert! h using 1
  simp [id_eq]

theorem sincNumerator_strictMonoOn :
    StrictMonoOn sincNumerator (Icc (0 : ℝ) Real.pi) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
  · exact (Real.continuous_sin.sub
      (continuous_id.mul Real.continuous_cos)).continuousOn
  · intro x hx
    rw [interior_Icc, mem_Ioo] at hx
    rw [(hasDerivAt_sincNumerator x).deriv]
    exact mul_pos hx.1 (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)

theorem sincNumerator_pos {x : ℝ} (hx0 : 0 < x) (hxpi : x ≤ Real.pi) :
    0 < sincNumerator x := by
  rw [← sincNumerator_zero]
  exact sincNumerator_strictMonoOn
    ⟨le_rfl, Real.pi_pos.le⟩ ⟨hx0.le, hxpi⟩ hx0

lemma hasDerivAt_sinc_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.sinc (-sincNumerator x / x ^ 2) x := by
  have hquot := (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx.ne'
  have heq : Real.sinc =ᶠ[𝓝 x] (fun y ↦ Real.sin y / y) := by
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hx.ne'] with y hy
    exact Real.sinc_of_ne_zero hy
  have hquot' := hquot.congr_of_eventuallyEq heq
  convert! hquot' using 1
  simp [sincNumerator]
  ring

theorem sinc_strictAntiOn_Icc_zero_pi :
    StrictAntiOn Real.sinc (Icc (0 : ℝ) Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 Real.pi)
  · exact Real.continuous_sinc.continuousOn
  · intro x hx
    rw [interior_Icc, mem_Ioo] at hx
    rw [(hasDerivAt_sinc_of_pos hx.1).deriv]
    exact div_neg_of_neg_of_pos
      (neg_neg_of_pos (sincNumerator_pos hx.1 hx.2.le)) (sq_pos_of_pos hx.1)

theorem sinc_strictAntiOn_Ioc_zero_pi :
    StrictAntiOn Real.sinc (Ioc (0 : ℝ) Real.pi) :=
  sinc_strictAntiOn_Icc_zero_pi.mono Ioc_subset_Icc_self

theorem sinc_antitoneOn_Icc_zero_pi :
    AntitoneOn Real.sinc (Icc (0 : ℝ) Real.pi) :=
  sinc_strictAntiOn_Icc_zero_pi.antitoneOn

lemma sinc_pos_of_mem_Ioo_zero_pi {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) Real.pi) :
    0 < Real.sinc x := by
  rw [Real.sinc_of_ne_zero hx.1.ne']
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2) hx.1

end

end Erdos1038
