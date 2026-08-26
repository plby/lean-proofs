/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The common quadratic characteristic-function expansion of signs and Gaussians.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Characteristic
import ErdosProblems.Erdos521.Moments
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Distributions.Gaussian.Real

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

theorem sign_gaussian_charFun_isLittleO :
    (fun t : ℝ ↦ charFun signLaw t - charFun (gaussianReal 0 1) t) =o[𝓝 0] fun t ↦ t ^ 2 := by
  have hs := taylor_charFun_two (P := sequenceLaw) (X := fun ε : ℕ → ℝ ↦ ε 0)
    (measurable_pi_apply 0).aemeasurable (integral_coordinate 0) (integral_coordinate_sq 0)
  rw [sequenceLaw_map_eval] at hs
  have hγsq : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
    rw [variance_eq_integral (X := fun x : ℝ ↦ x) measurable_id.aemeasurable] at h
    simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] using h
  have hg : (fun t : ℝ ↦ charFun (gaussianReal 0 1) t - (1 - (t : ℂ) ^ 2 / 2)) =o[𝓝 0]
      fun t ↦ t ^ 2 := by
    simpa only [Measure.map_id'] using taylor_charFun_two (P := gaussianReal 0 1) (X := fun x : ℝ ↦ x)
      measurable_id.aemeasurable (by simp) hγsq
  exact (hs.sub hg).congr_left (fun _ ↦ by ring)

theorem sign_gaussian_charFun_small {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
      ‖charFun signLaw t - charFun (gaussianReal 0 1) t‖ ≤ η * t ^ 2 := by
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp (sign_gaussian_charFun_isLittleO.def hη)
  refine ⟨r, hr, ?_⟩
  intro t ht
  have h := hbound (y := t) (by simpa only [Real.dist_eq, sub_zero] using ht)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using h

end Erdos521
