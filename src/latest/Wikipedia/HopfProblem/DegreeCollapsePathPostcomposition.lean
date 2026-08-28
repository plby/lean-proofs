import Wikipedia.HopfProblem.DegreeCollapsePathOperators
import Wikipedia.HopfProblem.DegreeCollapseUniformRemainder

/-!
# Differentiating nonlinear postcomposition on compact path spaces

The actual derivative applies the original derivative pointwise. A uniform
quadratic remainder on a compact model ball gives the required Fréchet
remainder estimate in the path sup norm.
-/

noncomputable section

open Set Filter Function Asymptotics
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuous coefficient path for the pointwise derivative of postcomposition. -/
def pathDerivative (f : C(E, F)) (hf : ContDiff ℝ ∞ f) (u : C(K, E)) : C(K, E →L[ℝ] F) :=
  ⟨fun t => fderiv ℝ f (u t), (hf.continuous_fderiv (by simp)).comp u.continuous⟩

theorem hasFDerivAt_pathPostcomposition (f : C(E, F)) (hf : ContDiff ℝ ∞ f) (u : C(K, E)) :
    HasFDerivAt (fun v : C(K, E) => f.comp v) (pathOperator (pathDerivative f hf u)) u := by
  obtain ⟨C, hC, hrem⟩ := exists_quadratic_remainder_bound hf (‖u‖ + 1)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  let δ := min 1 (ε / C)
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε hC)
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, E)) hδ] with h hh
  have hhnorm : ‖h‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hhnorm (min_le_left _ _)
  have hhε : C * ‖h‖ ≤ ε := by
    have hhdiv : ‖h‖ < ε / C := lt_of_lt_of_le hhnorm (min_le_right _ _)
    have hh' := (lt_div_iff₀ hC).mp hhdiv
    nlinarith
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg h))).mpr
  intro t
  change ‖f (u t + h t) - f (u t) - fderiv ℝ f (u t) (h t)‖ ≤ ε * ‖h‖
  have hxu : ‖u t‖ ≤ ‖u‖ + 1 := (u.norm_coe_le_norm t).trans (by linarith)
  have hyu : ‖u t + h t‖ ≤ ‖u‖ + 1 :=
    (norm_add_le _ _).trans (by linarith [u.norm_coe_le_norm t, h.norm_coe_le_norm t])
  have hr := hrem (u t) (u t + h t) hxu hyu
  simp only [add_sub_cancel_left] at hr
  calc
    _ ≤ C * ‖h t‖ ^ 2 := hr
    _ ≤ C * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h.norm_coe_le_norm t)) hC.le
    _ ≤ ε * ‖h‖ := by
      have hh' := mul_le_mul_of_nonneg_right hhε (norm_nonneg h)
      simpa only [pow_two, mul_assoc] using hh'

theorem fderiv_pathPostcomposition (f : C(E, F)) (hf : ContDiff ℝ ∞ f) (u : C(K, E)) :
    fderiv ℝ (fun v : C(K, E) => f.comp v) u = pathOperator (pathDerivative f hf u) :=
  (hasFDerivAt_pathPostcomposition f hf u).fderiv

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
