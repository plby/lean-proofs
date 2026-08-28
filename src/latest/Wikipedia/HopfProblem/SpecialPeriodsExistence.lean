import Wikipedia.HopfProblem.TriangleUniformization
import Wikipedia.HopfProblem.SpecialPeriodsConstruction

/-!
# Unconditional existence of the special admissible period functions

The normalized triangle uniformization has now been constructed. Applying
the modular lifting and affine Cousin constructions, followed by the
proved uniform imaginary shift, gives the actual global period map with
no geometric or analytic existence input. The same construction supplies
its positive-radius small-drift cusp model and exact logarithmic periods.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods

open Triangle Construction

attribute [local instance] triangleCompactifiedChartedSpace

/-- The actual normalized source coordinate on the upper half-plane. -/
def specialSourceCoordinate : ℍ → ℂ := BetaTorsor.finiteProjection triangleSphereUniformization

/-- The actual holomorphic admissible period map, with no supplied input. -/
def specialPeriodMap : HolomorphicPeriodMap ℂ ℍ :=
  periodMapOfSphere triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo

/-- The first special period function. -/
def specialTau (z : ℍ) : ℂ := (specialPeriodMap.point z).val.τ

/-- The unique bounded-cusp middle period function constructed above. -/
def specialMu (z : ℍ) : ℂ := (specialPeriodMap.point z).val.μ

/-- A third period function after one uniformly admissible imaginary shift. -/
def specialBeta (z : ℍ) : ℂ := (specialPeriodMap.point z).val.β

theorem specialTau_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω specialTau :=
  specialPeriodMap.holomorphic_tau

theorem specialMu_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω specialMu :=
  specialPeriodMap.holomorphic_mu

theorem specialBeta_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω specialBeta :=
  specialPeriodMap.holomorphic_beta

theorem specialTau_im_pos (z : ℍ) : 0 < (specialTau z).im :=
  (specialPeriodMap.point z).property.1

/-- The full first-generator identity in the genuine period domain. -/
theorem specialPeriodMap_generator₁ (z : ℍ) :
    specialPeriodMap.point (generatorOneSL • z) = (specialPeriodMap.point z).step₁ :=
  periodMapOfSphere_generator₁ triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo z

/-- The full second-generator identity in the genuine period domain. -/
theorem specialPeriodMap_generator₂ (z : ℍ) :
    specialPeriodMap.point (generatorTwoSL • z) = (specialPeriodMap.point z).step₂ :=
  periodMapOfSphere_generator₂ triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo z

theorem specialPeriodMap_cusp (z : ℍ) :
    specialPeriodMap.point (triangleGeometricRepresentation triangleCuspGenerator z) =
      (specialPeriodMap.point z).step₀ :=
  periodMapOfSphere_cusp triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo z

/-- The first generator's three scalar equations, including its affine terms. -/
theorem specialPeriods_generator₁ (z : ℍ) :
    specialTau (generatorOneSL • z) = (specialTau z - 1) / specialTau z ∧
    specialMu (generatorOneSL • z) = (1 - specialMu z) / specialTau z ∧
    specialBeta (generatorOneSL • z) =
      specialBeta z + 2 - 6 * (1 - specialMu z) ^ 2 / specialTau z := by
  have h := congrArg Subtype.val (specialPeriodMap_generator₁ z)
  exact ⟨congrArg PeriodPoint.τ h, congrArg PeriodPoint.μ h, congrArg PeriodPoint.β h⟩

/-- The second middle-period equation is `1 + μ/τ`, with its literal parentheses. -/
theorem specialPeriods_generator₂ (z : ℍ) :
    specialTau (generatorTwoSL • z) = -1 / specialTau z ∧
    specialMu (generatorTwoSL • z) = 1 + specialMu z / specialTau z ∧
    specialBeta (generatorTwoSL • z) =
      specialBeta z - 3 - 6 * specialMu z ^ 2 / specialTau z := by
  have h := congrArg Subtype.val (specialPeriodMap_generator₂ z)
  exact ⟨congrArg PeriodPoint.τ h, congrArg PeriodPoint.μ h, congrArg PeriodPoint.β h⟩

theorem specialPeriodMap_modular (z : ℍ) :
    modularJ (ofComplex (specialTau z)) = 1728 * specialSourceCoordinate z :=
  periodMapOfSphere_modular triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo z

@[simp] theorem specialTau_centerOne : specialTau centerOne = (rhoPoint : ℂ) :=
  periodMapOfSphere_centerOne triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo

@[simp] theorem specialTau_centerTwo : specialTau centerTwo = Complex.I :=
  periodMapOfSphere_centerTwo triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo

/-- Strict admissibility holds everywhere, after the single constructed shift. -/
theorem specialPeriodMap_discriminant_neg (z : ℍ) :
    (specialPeriodMap.point z).val.discriminant < 0 :=
  (specialPeriodMap.point z).property.2

theorem specialPeriods_discriminant_neg (z : ℍ) :
    (specialBeta z).im - 6 * (specialMu z).im ^ 2 / (specialTau z).im < 0 :=
  specialPeriodMap_discriminant_neg z

theorem specialMu_cusp : MuTorsor.CuspRegular specialMu :=
  periodMapOfSphere_mu_cusp triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo

theorem specialBeta_add_tau_cusp :
    MuTorsor.CuspRegular (fun z => specialBeta z + specialTau z) :=
  periodMapOfSphere_beta_cusp triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo

/-- The actual analytic cusp correction and small-drift radius for these periods. -/
def specialCuspData : CuspFamily.Data :=
  cuspDataOfSphere triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo

theorem specialCuspData_periodPoint (z : ℍ)
    (hz : ‖cuspQ z‖ < specialCuspData.radius) :
    (specialPeriodMap.point z).val =
      cuspPeriodPoint specialCuspData.μ specialCuspData.b specialCuspData.h
        ((z : ℂ) / width) :=
  cuspDataOfSphere_periodPoint triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo z hz

theorem specialCuspData_leftBlock (z : ℍ)
    (hz : ‖cuspQ z‖ < specialCuspData.radius) :
    (specialPeriodMap.point z).val.leftBlock =
      CuspUniformization.logarithmicPeriod specialCuspData.correction ((z : ℂ) / width) :=
  cuspDataOfSphere_leftBlock triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo z hz

theorem specialCuspData_leftBlock_expanded (z : ℍ)
    (hz : ‖cuspQ z‖ < specialCuspData.radius) :
    (specialPeriodMap.point z).val.leftBlock =
      ((z : ℂ) / width) • B₀.map (Int.castRingHom ℂ) + specialCuspData.correction (cuspQ z) :=
  cuspDataOfSphere_leftBlock_expanded triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo z hz

/-- The special admissible global period map and its compatible cusp
data exist unconditionally; every displayed property is a conclusion. -/
theorem exists_special_admissible_periodMap :
    ∃ (P : HolomorphicPeriodMap ℂ ℍ) (C : CuspFamily.Data),
      (∀ z : ℍ, P.point (generatorOneSL • z) = (P.point z).step₁) ∧
      (∀ z : ℍ, P.point (generatorTwoSL • z) = (P.point z).step₂) ∧
      (∀ z : ℍ, P.point (triangleGeometricRepresentation triangleCuspGenerator z) =
        (P.point z).step₀) ∧
      (∀ z : ℍ, modularJ (ofComplex (P.point z).val.τ) =
        1728 * specialSourceCoordinate z) ∧
      (∀ z : ℍ, (P.point z).val.discriminant < 0) ∧
      ∀ z : ℍ, ‖cuspQ z‖ < C.radius →
        (P.point z).val = cuspPeriodPoint C.μ C.b C.h ((z : ℂ) / width) :=
  exists_admissible_periodMap_of_sphere triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo

end Wikipedia.HopfProblem.SpecialPeriods
