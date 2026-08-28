import Wikipedia.HopfProblem.SpecialPeriodsConstructionCuspData

/-!
# The complete admissible period map from the actual normalized quotient

A genuine normalized biholomorphism of the constructed compact triangle
quotient with the Riemann sphere is the only input.  The three holomorphic
functions, their full generator laws, their analytic cusp corrections,
the global discriminant bound, and a single admissible imaginary shift
have all been constructed in the imported modules.

The result is the actual `HolomorphicPeriodMap` used by the torus-family
construction, together with actual admissible cusp-family data.  Their
period matrices agree throughout one common positive-radius cusp region.
No global period function, cusp growth, compactness premise, descended
discriminant, or negativity assumption remains as an input.

Existence of the normalized sphere equivalence itself is not asserted here.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- The genuine holomorphic map into the admissible period domain,
constructed from the normalized actual quotient biholomorphism alone. -/
def periodMapOfSphere : HolomorphicPeriodMap ℂ ℍ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods

/-- The shift has not changed the constructed normalized modular lift. -/
theorem periodMapOfSphere_tau (z : ℍ) :
    ((periodMapOfSphere π hπ h₀ h₁).point z).val.τ =
      (TriangleSource.tauOfSphere π hπ h₀ h₁ z : ℂ) := by
  change ((periodFunctionsOfSphere π hπ h₀ h₁).data.tau z : ℂ) = _
  rw [periodFunctionsOfSphere_tau]

/-- The first source generator equation holds in the actual period domain. -/
theorem periodMapOfSphere_generator₁ (z : ℍ) :
    (periodMapOfSphere π hπ h₀ h₁).point (Triangle.generatorOneSL • z) =
      ((periodMapOfSphere π hπ h₀ h₁).point z).step₁ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods_generator₁ z

/-- The second source generator equation holds in the actual period domain. -/
theorem periodMapOfSphere_generator₂ (z : ℍ) :
    (periodMapOfSphere π hπ h₀ h₁).point (Triangle.generatorTwoSL • z) =
      ((periodMapOfSphere π hπ h₀ h₁).point z).step₂ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods_generator₂ z

/-- The full cusp equation follows from the actual triangle-group word. -/
theorem periodMapOfSphere_cusp (z : ℍ) :
    (periodMapOfSphere π hπ h₀ h₁).point
        (triangleGeometricRepresentation triangleCuspGenerator z) =
      ((periodMapOfSphere π hπ h₀ h₁).point z).step₀ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods_cusp z

/-- The source's modular equation is retained exactly. -/
theorem periodMapOfSphere_modular (z : ℍ) :
    modularJ (ofComplex ((periodMapOfSphere π hπ h₀ h₁).point z).val.τ) =
      1728 * BetaTorsor.finiteProjection π z := by
  rw [periodMapOfSphere_tau, ofComplex_apply]
  exact TriangleSource.tauOfSphere_modular π hπ h₀ h₁ z

theorem periodMapOfSphere_centerOne :
    ((periodMapOfSphere π hπ h₀ h₁).point Triangle.centerOne).val.τ =
      (rhoPoint : ℂ) := by
  rw [periodMapOfSphere_tau, TriangleSource.tauOfSphere_centerOne]

theorem periodMapOfSphere_centerTwo :
    ((periodMapOfSphere π hπ h₀ h₁).point Triangle.centerTwo).val.τ = Complex.I := by
  rw [periodMapOfSphere_tau, TriangleSource.tauOfSphere_centerTwo]
  rfl

/-- Global strict negativity is a conclusion of the actual compact-descent
argument and the single constructed imaginary shift. -/
theorem periodMapOfSphere_discriminant_neg (z : ℍ) :
    ((periodMapOfSphere π hπ h₀ h₁).point z).val.discriminant < 0 :=
  ((periodMapOfSphere π hπ h₀ h₁).point z).property.2

/-- The middle period has a genuine analytic cusp germ. -/
theorem periodMapOfSphere_mu_cusp :
    MuTorsor.CuspRegular (fun z => ((periodMapOfSphere π hπ h₀ h₁).point z).val.μ) :=
  (periodFunctionsOfSphere π hπ h₀ h₁).mu_cusp

/-- The shifted third period plus tau has a genuine analytic cusp germ. -/
theorem periodMapOfSphere_beta_cusp : MuTorsor.CuspRegular
    (fun z => ((periodMapOfSphere π hπ h₀ h₁).point z).val.β +
      ((periodMapOfSphere π hπ h₀ h₁).point z).val.τ) :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods_beta_cusp

/-- Actual positive-radius cusp-family data, including holomorphic matrix
entries and the quantitative small-drift estimate, for the same periods. -/
def cuspDataOfSphere : CuspFamily.Data :=
  (periodFunctionsOfSphere π hπ h₀ h₁).cuspData

/-- The full triple, not only its lattice or its discriminant, agrees
with the genuine cusp model throughout the chosen small cusp region. -/
theorem cuspDataOfSphere_periodPoint (z : ℍ)
    (hz : ‖Triangle.cuspQ z‖ < (cuspDataOfSphere π hπ h₀ h₁).radius) :
    ((periodMapOfSphere π hπ h₀ h₁).point z).val =
      cuspPeriodPoint (cuspDataOfSphere π hπ h₀ h₁).μ
        (cuspDataOfSphere π hπ h₀ h₁).b (cuspDataOfSphere π hπ h₀ h₁).h
        ((z : ℂ) / Triangle.width) :=
  (periodFunctionsOfSphere π hπ h₀ h₁).cuspData_periodPoint z hz

/-- The constructed analytic correction is exactly the correction in
the original period matrix, with the source's normalization and signs. -/
theorem cuspDataOfSphere_leftBlock (z : ℍ)
    (hz : ‖Triangle.cuspQ z‖ < (cuspDataOfSphere π hπ h₀ h₁).radius) :
    ((periodMapOfSphere π hπ h₀ h₁).point z).val.leftBlock =
      CuspUniformization.logarithmicPeriod (cuspDataOfSphere π hπ h₀ h₁).correction
        ((z : ℂ) / Triangle.width) :=
  (periodFunctionsOfSphere π hπ h₀ h₁).cuspData_leftBlock z hz

/-- In the original source coordinate the period block is its explicit
logarithmic term plus the constructed holomorphic correction matrix. -/
theorem cuspDataOfSphere_leftBlock_expanded (z : ℍ)
    (hz : ‖Triangle.cuspQ z‖ < (cuspDataOfSphere π hπ h₀ h₁).radius) :
    ((periodMapOfSphere π hπ h₀ h₁).point z).val.leftBlock =
      ((z : ℂ) / Triangle.width) • B₀.map (Int.castRingHom ℂ) +
        (cuspDataOfSphere π hπ h₀ h₁).correction (Triangle.cuspQ z) :=
  (periodFunctionsOfSphere π hπ h₀ h₁).cuspData_leftBlock_expanded z hz

include hπ h₀ h₁ in
/-- **The full admissible global period-map construction.** The sole
input is the actual normalized sphere equivalence.  In particular the
global period functions, their generator equations, the discriminant
inequality, and the compatible analytic cusp data are all conclusions. -/
theorem exists_admissible_periodMap_of_sphere :
    ∃ (P : HolomorphicPeriodMap ℂ ℍ) (C : CuspFamily.Data),
      (∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁) ∧
      (∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂) ∧
      (∀ z : ℍ, P.point (triangleGeometricRepresentation triangleCuspGenerator z) =
        (P.point z).step₀) ∧
      (∀ z : ℍ, modularJ (ofComplex (P.point z).val.τ) =
        1728 * BetaTorsor.finiteProjection π z) ∧
      (∀ z : ℍ, (P.point z).val.discriminant < 0) ∧
      ∀ z : ℍ, ‖Triangle.cuspQ z‖ < C.radius →
        (P.point z).val = cuspPeriodPoint C.μ C.b C.h ((z : ℂ) / Triangle.width) := by
  exact ⟨periodMapOfSphere π hπ h₀ h₁, cuspDataOfSphere π hπ h₀ h₁,
    periodMapOfSphere_generator₁ π hπ h₀ h₁,
    periodMapOfSphere_generator₂ π hπ h₀ h₁,
    periodMapOfSphere_cusp π hπ h₀ h₁,
    periodMapOfSphere_modular π hπ h₀ h₁,
    periodMapOfSphere_discriminant_neg π hπ h₀ h₁,
    cuspDataOfSphere_periodPoint π hπ h₀ h₁⟩

end Wikipedia.HopfProblem.SpecialPeriods.Construction
