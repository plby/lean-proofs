import Wikipedia.HopfProblem.StandardSixSphereCircleModelCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth scalar and normalization formulas for the standard sphere model

All smoothness statements use the original Euclidean structures and, for
maps from a manifold, its given model with corners and charted space.
The denominator is positive everywhere; normalization is used only off zero.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel

variable {n : WithTop ℕ∞}

/-- The denominator of the inverse complement chart is smooth everywhere. -/
theorem contDiff_denominator :
    ContDiff ℝ n (fun a : Base => Real.sqrt (1 + ‖a‖ ^ 2)) := by
  apply (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt
  intro a
  exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg ‖a‖))

/-- Its reciprocal is smooth, without a condition on the base coordinate. -/
theorem contDiff_inverseScale :
    ContDiff ℝ n (fun a : Base => (Real.sqrt (1 + ‖a‖ ^ 2))⁻¹) := by
  apply contDiff_denominator.inv
  intro a
  exact (Real.sqrt_pos.mpr
    (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg ‖a‖))).ne'

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The inverse norm is smooth at every nonzero vector. -/
theorem contDiffAt_invNorm {x : F} (hx : x ≠ 0) :
    ContDiffAt ℝ n (fun y : F => ‖y‖⁻¹) x :=
  (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)

/-- Ambient smoothness of radial normalization away from the origin. -/
theorem contDiffAt_normalize {x : F} (hx : x ≠ 0) :
    ContDiffAt ℝ n (fun y : F => ‖y‖⁻¹ • y) x :=
  (contDiffAt_invNorm hx).smul contDiffAt_id

theorem contDiffOn_normalize :
    ContDiffOn ℝ n (fun y : F => ‖y‖⁻¹ • y) {y | y ≠ 0} :=
  fun _ hy => (contDiffAt_normalize hy).contDiffWithinAt

end InnerProductSpace

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {f : M → F} {s : Set M} {x : M}

/-- The norm of a nonvanishing smooth vector-valued map is smooth locally. -/
theorem contMDiffWithinAt_norm_of_ne_zero
    (hf : ContMDiffWithinAt I 𝓘(ℝ, F) n f s x) (hx : f x ≠ 0) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) n (fun p => ‖f p‖) s x :=
  (contDiffAt_norm ℝ hx).comp_contMDiffWithinAt hf

theorem contMDiffAt_norm_of_ne_zero
    (hf : ContMDiffAt I 𝓘(ℝ, F) n f x) (hx : f x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n (fun p => ‖f p‖) x :=
  (contDiffAt_norm ℝ hx).comp_contMDiffAt hf

theorem contMDiff_norm_of_ne_zero
    (hf : ContMDiff I 𝓘(ℝ, F) n f) (h0 : ∀ p, f p ≠ 0) :
    ContMDiff I 𝓘(ℝ, ℝ) n (fun p => ‖f p‖) :=
  fun p => contMDiffAt_norm_of_ne_zero (hf p) (h0 p)

/-- The reciprocal norm uses the given atlas on the source. -/
theorem contMDiffAt_invNorm_of_ne_zero
    (hf : ContMDiffAt I 𝓘(ℝ, F) n f x) (hx : f x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n (fun p => ‖f p‖⁻¹) x :=
  (contDiffAt_invNorm hx).comp_contMDiffAt hf

theorem contMDiff_invNorm_of_ne_zero
    (hf : ContMDiff I 𝓘(ℝ, F) n f) (h0 : ∀ p, f p ≠ 0) :
    ContMDiff I 𝓘(ℝ, ℝ) n (fun p => ‖f p‖⁻¹) :=
  fun p => contMDiffAt_invNorm_of_ne_zero (hf p) (h0 p)

/-- Normalize a smooth nonzero vector-valued map, as an ambient map. -/
theorem contMDiffAt_normalize_of_ne_zero
    (hf : ContMDiffAt I 𝓘(ℝ, F) n f x) (hx : f x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun p => ‖f p‖⁻¹ • f p) x :=
  (contDiffAt_normalize hx).comp_contMDiffAt hf

theorem contMDiff_normalize_of_ne_zero
    (hf : ContMDiff I 𝓘(ℝ, F) n f) (h0 : ∀ p, f p ≠ 0) :
    ContMDiff I 𝓘(ℝ, F) n (fun p => ‖f p‖⁻¹ • f p) :=
  fun p => contMDiffAt_normalize_of_ne_zero (hf p) (h0 p)

end Manifold

end Wikipedia.HopfProblem.StandardSixSphereCircleModel
