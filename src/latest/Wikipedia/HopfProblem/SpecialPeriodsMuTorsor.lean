import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorFromRoot
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrders
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorBounded

/-!
# The actual global μ problem for a supplied normalized uniformization

Given an actual normalized biholomorphism of the compact triangle quotient
with the Riemann sphere and a genuine holomorphic modular lift `τ`, the
affine μ problem has a unique solution with the source's boundedness at
the distinguished cusp.  Its analytic extension in the actual cusp chart
is also constructed.

The source orders three and four are proved from the actual quotient
charts and the supplied biholomorphism.  They construct the global square
root and the genuine Eisenstein homogeneous generator.  Thus no root,
homogeneous generator, vanishing order, local section, overlap cocycle,
line-bundle isomorphism, or cohomological vanishing is an input here.

The supplied global uniformization and modular lift are still explicit
inputs: this file does not assert that either already exists.  The cusp
q-parameter identity is the exact expansion of that supplied lift.
-/

noncomputable section

open Function Filter UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

attribute [local instance] triangleCompactifiedChartedSpace

/-- Analytic cusp regularity and the original boundedness condition agree
for holomorphic functions satisfying the source's actual two affine laws. -/
theorem isSolution_iff_bounded {τ : ℍ → ℍ} {μ : ℍ → ℂ} (hτ : TauCovariant τ) :
    IsSolution τ μ ↔
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ ∧
      (∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ)) ∧
      (∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) ∧
      IsBoundedAtImInfty μ := by
  constructor
  · intro h
    exact ⟨h.holomorphic, h.generatorOne, h.generatorTwo, h.cuspRegular.bounded⟩
  · rintro ⟨hμ, h₁, h₂, hb⟩
    exact ⟨hμ, h₁, h₂,
      cuspRegular_of_bounded hμ (affine_cusp_invariant hτ h₁ h₂) hb⟩

/-- **Global μ existence and uniqueness from the actual normalized
uniformization and a genuine modular lift.** The homogeneous generator
and every analytic gluing input are constructed inside the proof. -/
theorem exists_unique_solution
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
    {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hJ : ∀ z, modularJ (τ z) = 1728 * BetaTorsor.finiteProjection π z)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq : ∀ᶠ z in atImInfty,
      Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z)) :
    ∃! μ : ℍ → ℂ, IsSolution τ μ := by
  have hJ' : ∀ z, modularJ (τ z) = SourceOrders.sourceJ π z := hJ
  obtain ⟨F, ⟨r, rfl⟩, hF, hFc, _, hF₁, hF₂⟩ :=
    MuGenerator.exists_homogeneous_generator_of_modular_equation hτa hτ hJ'
      (SourceOrders.sourceJ_order_of_eq_zero π hπ h₀)
      (SourceOrders.sourceJ_sub_1728_order_of_eq π hπ h₁)
  exact exists_unique_solution_from_generator π hπ hτ hτa r.generator hF hFc
    (generator_zero_iff_orbits π hπ h₀ h₁ hJ r) hF₁ hF₂
    (r.exists_cusp_unit hu hu0 hq)

/-- The same existence-and-uniqueness conclusion with exactly the source's
holomorphicity, affine laws, and boundedness condition, rather than a
stronger regularity premise. -/
theorem exists_unique_bounded_solution
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
    {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hJ : ∀ z, modularJ (τ z) = 1728 * BetaTorsor.finiteProjection π z)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq : ∀ᶠ z in atImInfty,
      Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z)) :
    ∃! μ : ℍ → ℂ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ ∧
      (∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ)) ∧
      (∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) ∧
      IsBoundedAtImInfty μ := by
  obtain ⟨μ, hμ, huniq⟩ := exists_unique_solution π hπ h₀ h₁ hτ hτa hJ hu hu0 hq
  exact ⟨μ, (isSolution_iff_bounded hτ).mp hμ,
    fun ν hν => huniq ν ((isSolution_iff_bounded hτ).mpr hν)⟩

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
