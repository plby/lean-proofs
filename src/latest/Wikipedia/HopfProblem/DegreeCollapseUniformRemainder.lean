import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A uniform quadratic derivative remainder on a finite-dimensional ball

The second derivative is bounded on the actual compact ball. Two mean
value estimates give a quadratic remainder uniform in both endpoints.
This supplies Fréchet differentiability of nonlinear postcomposition on
the Banach space of continuous paths.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness gives one quadratic remainder bound throughout each compact model ball. -/
theorem exists_quadratic_remainder_bound {f : E → F} (hf : ContDiff ℝ ∞ f) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : E, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdcont : Continuous (fderiv ℝ (fderiv ℝ f)) := hdf.continuous_fderiv (by simp)
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    hdcont.continuousOn
  let C := max C₀ 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (z : E) (hz : z ∈ closedBall (0 : E) R) :
      ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C := by
    exact (hC₀ z hz).trans (by dsimp [C]; linarith [le_max_left C₀ 0])
  have hlip {x z : E} (hx : x ∈ closedBall (0 : E) R) (hz : z ∈ closedBall (0 : E) R) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖z - x‖ :=
    (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf.differentiable (by simp) z) hbound hx hz
  refine ⟨C, hC, ?_⟩
  intro x y hx hy
  have hxR : x ∈ closedBall (0 : E) R := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hyR : y ∈ closedBall (0 : E) R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hseg : segment ℝ x y ⊆ closedBall (0 : E) R := (convex_closedBall _ _).segment_subset hxR hyR
  have hdist : segment ℝ x y ⊆ closedBall x ‖y - x‖ := by
    apply (convex_closedBall x ‖y - x‖).segment_subset
    · exact mem_closedBall_self (norm_nonneg _)
    · simp only [mem_closedBall, dist_eq_norm, le_refl]
  have hh := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf.differentiable (by simp) z)
    (fun z hz => (hlip hxR (hseg hz)).trans (mul_le_mul_of_nonneg_left
      (show ‖z - x‖ ≤ ‖y - x‖ from by simpa only [mem_closedBall, dist_eq_norm] using hdist hz)
      hC.le)) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using hh

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
