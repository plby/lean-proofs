import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSolution
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersCore
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorConstruction
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorCusp

/-!
# The μ solution from the genuine Eisenstein generator

For a supplied normalized analytic sphere identification and a supplied
genuine modular lift `τ`, the actual modular forms construct the required
homogeneous generator from a root of `E₆ ∘ τ`.  Its two elliptic orders,
complete zero set, affine laws, and simple cusp pole discharge every
generator input of the proved global μ construction and uniqueness theorem.

The supplied root is a holomorphic function satisfying its actual square
equation.  A subsequent theorem constructs this root from the branching
orders of the supplied quotient uniformization, rather than assuming it.
-/

noncomputable section

open Function Filter UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

attribute [local instance] triangleCompactifiedChartedSpace

/-- The normalized sphere coordinate identifies the generator's entire
zero set with the two actual triangle elliptic orbits. -/
theorem generator_zero_iff_orbits
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
    {τ : ℍ → ℍ} (hJ : ∀ z, modularJ (τ z) = 1728 * BetaTorsor.finiteProjection π z)
    (r : MuGenerator.Root τ) (z : ℍ) :
    r.generator z = 0 ↔ triangleOrbitProjection z = triangleOrbitCenterOne ∨
      triangleOrbitProjection z = triangleOrbitCenterTwo := by
  rw [r.generator_eq_zero_iff_normalized_source hJ,
    SourceOrders.finiteProjection_eq_zero_iff π hπ h₀,
    SourceOrders.finiteProjection_eq_one_iff π hπ h₁]

/-- Actual μ existence and uniqueness, using the genuine modular forms
and the exact local and cusp behaviour of the supplied modular lift.
No line-bundle isomorphism, Cousin cocycle, or torsor section is assumed. -/
theorem exists_unique_solution_of_root
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
    {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hJ : ∀ z, modularJ (τ z) = 1728 * BetaTorsor.finiteProjection π z)
    (r : MuGenerator.Root τ)
    (ho₁ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - rho)
      (Triangle.centerOne : ℂ) = 1)
    (ho₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq : ∀ᶠ z in atImInfty,
      Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z)) :
    ∃! μ : ℍ → ℂ, IsSolution τ μ :=
  exists_unique_solution_from_generator π hπ hτ hτa r.generator
    (r.generator_holomorphic hτa) (r.generator_homogeneous hτa hτ ho₂)
    (generator_zero_iff_orbits π hπ h₀ h₁ hJ r)
    (r.generator_order_centerOne_of_tau_order hτa hτ ho₁)
    (r.generator_order_centerTwo_of_tau_order hτa hτ ho₂)
    (r.exists_cusp_unit hu hu0 hq)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
