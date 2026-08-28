import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorExistence
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorUniqueness

/-!
# Existence and uniqueness of the affine μ solution

The properties below are the actual holomorphicity, two source affine
equations, and analytic regularity in the actual exponential cusp chart.
Existence is supplied by the constructed local sections and the proved
Cousin correction; uniqueness is supplied by actual analytic division,
quotient descent, and compact-curve vanishing.

The sphere identification and the homogeneous generator remain explicit
inputs of this intermediate theorem.  Their existence is not encoded in
the solution predicate or postulated as a cohomological vanishing result.
-/

noncomputable section

open Filter UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

attribute [local instance] triangleCompactifiedChartedSpace

/-- The genuine analytic and affine conditions on a special μ function. -/
structure IsSolution (τ : ℍ → ℍ) (μ : ℍ → ℂ) : Prop where
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ
  generatorOne : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ)
  generatorTwo : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)
  cuspRegular : CuspRegular μ

/-- The actual affine μ problem has a unique solution once the supplied
normalized sphere identification and the genuine homogeneous generator
are available.  All local sections, overlap functions, corrections,
division germs, and compact extensions are constructed in the proof. -/
theorem exists_unique_solution_from_generator
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
    {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hFc : MuGenerator.Homogeneous τ F)
    (hFzero : ∀ z : ℍ, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (hForder₁ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 2)
    (hForder₂ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1)
    (hFcusp : ∃ v : ℂ → ℂ, AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧
      ∀ᶠ z in atImInfty, F z = (Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z)) :
    ∃! μ : ℍ → ℂ, IsSolution τ μ := by
  obtain ⟨μ, hμ, _, hμ₁, hμ₂, hμc⟩ :=
    exists_holomorphic_affine_cuspRegular π hπ hτ hτa F hF hFc hFzero hFcusp
  refine ⟨μ, ⟨hμ, hμ₁, hμ₂, hμc⟩, ?_⟩
  intro μ' hμ'
  exact affine_eq_of_cuspRegular hτa hτ hμ'.holomorphic hμ
    hμ'.generatorOne hμ'.generatorTwo hμ₁ hμ₂ hμ'.cuspRegular hμc
    hF hFc.1 hFc.2 hFzero hForder₁ hForder₂ hFcusp

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
