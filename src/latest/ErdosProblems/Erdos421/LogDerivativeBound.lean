import ErdosProblems.Erdos421.HolomorphicLog
import Mathlib.Analysis.Complex.BorelCaratheodory

/-! # Logarithmic-derivative control from a norm bound on a nonvanishing disk -/

namespace Erdos421

open Metric Filter Topology

theorem norm_deriv_zero_le_of_re_bound {g : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hg : DifferentiableOn ℂ g (ball 0 R)) (hg0 : g 0 = 0)
    (hreal : ∀ z ∈ ball 0 R, (g z).re ≤ A) :
    ‖deriv g 0‖ ≤ 4 * A / R := by
  apply norm_deriv_le_of_lip' (by positivity)
  filter_upwards [ball_mem_nhds (0 : ℂ) (by linarith : 0 < R / 2)] with z hz
  have hzsmall : ‖z‖ < R / 2 := by simpa only [mem_ball, dist_zero_right] using hz
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by linarith)
  have hb := Complex.borelCaratheodory_zero hA hg hreal hR hzR hg0
  rw [hg0, sub_zero, sub_zero]
  calc
    _ ≤ 2 * A * ‖z‖ / (R - ‖z‖) := hb
    _ ≤ 2 * A * ‖z‖ / (R / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    _ = _ := by ring

/-- This general analytic estimate will be applied to a residual function
after its zeros have been removed. No nonvanishing assertion for zeta is
assumed by the development. -/
theorem logarithmic_derivative_bound_on_ball {f : ℂ → ℂ} {c : ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hf : DifferentiableOn ℂ f (ball c R))
    (hzero : ∀ z ∈ ball c R, f z ≠ 0)
    (hbound : ∀ z ∈ ball c R, ‖f z‖ ≤ Real.exp A * ‖f c‖) :
    ‖deriv f c / f c‖ ≤ 4 * A / R := by
  obtain ⟨g, hgc, hg, he⟩ := exists_normalized_log_on_ball hR hf hzero
  have hc : c ∈ ball c R := mem_ball_self hR
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hzero c hc)
  have hreal : ∀ z ∈ ball c R, (g z).re ≤ A := by
    intro z hz
    have hnorm := congrArg norm (he z hz)
    rw [Complex.norm_exp, norm_div] at hnorm
    apply Real.exp_le_exp.mp
    rw [hnorm]
    exact (div_le_iff₀ hfc).mpr (hbound z hz)
  let G : ℂ → ℂ := fun z ↦ g (c + z)
  have htrans : ∀ z ∈ ball (0 : ℂ) R, c + z ∈ ball c R := by
    intro z hz
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hG : DifferentiableOn ℂ G (ball 0 R) := by
    intro z hz
    exact ((hg (c + z) (htrans z hz)).differentiableAt.comp z
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
  have hG0 : G 0 = 0 := by simpa only [G, add_zero] using hgc
  have hb := norm_deriv_zero_le_of_re_bound hR hA hG hG0
    (fun z hz ↦ hreal (c + z) (htrans z hz))
  have hd : HasDerivAt G (deriv f c / f c) 0 := by
    have hg0 : HasDerivAt g (deriv f c / f c) (c + 0) := by
      simpa only [add_zero] using hg c hc
    have h := hg0.comp (0 : ℂ) ((hasDerivAt_const (0 : ℂ) c).add (hasDerivAt_id 0))
    convert! h using 1
    simp only [zero_add, mul_one]
  rwa [hd.deriv] at hb

end Erdos421
