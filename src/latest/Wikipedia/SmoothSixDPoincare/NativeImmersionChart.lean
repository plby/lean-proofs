import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Detecting injective native derivatives in a fixed target chart

The differential of a partial diffeomorphism is invertible. Consequently,
injectivity of the derivative of the actual coordinate expression is
equivalent to injectivity of the original manifold derivative.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {E G F H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

/-- Chart differentiation neither creates nor removes a kernel in the native derivative. -/
theorem injective_fderiv_chart_iff (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : E → N} {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) J f x)
    (hx : f x ∈ c.source) :
    Function.Injective (fderiv ℝ (c ∘ f) x) ↔
      Function.Injective (mfderiv 𝓘(ℝ, E) J f x) := by
  have hderiv : fderiv ℝ (c ∘ f) x =
      (mfderiv J 𝓘(ℝ, F) c (f x)).comp (mfderiv 𝓘(ℝ, E) J f x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf]
  have hc : Function.Injective (mfderiv J 𝓘(ℝ, F) c (f x)) :=
    ((c.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv
      (by simp)).injective
  rw [hderiv]
  constructor
  · intro h v w hvw
    exact h (congrArg (mfderiv J 𝓘(ℝ, F) c (f x)) hvw)
  · exact fun h => hc.comp h

/-- A fixed smooth target chart preserves the kernel of the derivative, vector by vector. -/
theorem fderiv_chart_eq_zero_iff (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : E → N} {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) J f x)
    (hx : f x ∈ c.source) (v : E) :
    fderiv ℝ (c ∘ f) x v = 0 ↔ mfderiv 𝓘(ℝ, E) J f x v = 0 := by
  have hderiv : fderiv ℝ (c ∘ f) x =
      (mfderiv J 𝓘(ℝ, F) c (f x)).comp (mfderiv 𝓘(ℝ, E) J f x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf]
  have hc : Function.Injective (mfderiv J 𝓘(ℝ, F) c (f x)) :=
    ((c.isLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ hx).mfderivToContinuousLinearEquiv
      (by simp)).injective
  rw [hderiv]
  change (mfderiv J 𝓘(ℝ, F) c (f x)) (mfderiv 𝓘(ℝ, E) J f x v) = 0 ↔ _
  constructor
  · intro h
    apply hc
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
