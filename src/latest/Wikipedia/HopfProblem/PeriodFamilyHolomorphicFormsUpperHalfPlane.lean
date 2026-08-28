import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsGeometry

/-!
# Manifold and scalar derivatives on the actual upper half-plane

The singleton chart of the upper half-plane is the original inclusion
into the complex plane, with inverse `ofComplex`.  Its manifold derivative
therefore agrees with the ordinary derivative used by the holomorphic
differential coefficients, including the full complex-linear map.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

open TriangleHolomorphicDifferentials

/-- In the genuine upper-half-plane chart, the manifold derivative is
the ordinary Fréchet derivative of the original scalar extension. -/
theorem mfderiv_eq_fderiv_ofComplex {f : ℍ → ℂ} {z : ℍ}
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f z) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f z = fderiv ℂ (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) := by
  simpa [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    chartAt_self_eq, UpperHalfPlane.ofComplex] using hf.mfderiv

/-- Evaluation on the coordinate tangent vector `1` is exactly the
already defined scalar derivative. -/
theorem mfderiv_chart_scalar {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (z : ℍ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f z (1 : ℂ) = scalarDeriv f z :=
  congrArg (fun L : ℂ →L[ℂ] ℂ => L 1)
    (mfderiv_eq_fderiv_ofComplex ((hf z).mdifferentiableAt (by simp)))

theorem mfderiv_chart_apply {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (z : ℍ) (v : ℂ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f z v = scalarDeriv f z * v := by
  rw [mfderiv_eq_fderiv_ofComplex ((hf z).mdifferentiableAt (by simp))]
  change fderiv ℂ (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) v =
    deriv (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) * v
  exact fderiv_eq_deriv_mul

/-- The full manifold derivative is multiplication by the scalar
derivative, in the unchanged tangent-space coordinates. -/
theorem mfderiv_chart_linear {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (z : ℍ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f z = scalarDeriv f z • ContinuousLinearMap.id ℂ ℂ := by
  apply ContinuousLinearMap.ext
  intro v
  exact mfderiv_chart_apply hf z v

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
