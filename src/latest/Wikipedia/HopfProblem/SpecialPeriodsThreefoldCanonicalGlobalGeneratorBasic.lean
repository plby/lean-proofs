import Wikipedia.HopfProblem.SpecialPeriodsUniquenessTau
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrders
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorFromRoot
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorOrdersTranslated

/-!
# The actual global homogeneous generator

The normalized quotient sphere and its actual special period supply all
hypotheses of the Eisenstein-root construction.  This file retains the
resulting function `F` from Lemma 3.10 as a named global holomorphic
function.  Its zeros, elliptic orders, and covariance laws are proved for
the actual special period map, with no generator supplied as an input.
-/

noncomputable section

open Set Filter UpperHalfPlane ModularForm
open scoped Topology Manifold ContDiff OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalGenerator

open Triangle MuGenerator MuTorsor.SourceOrders

attribute [local instance] triangleCompactifiedChartedSpace

theorem modular_source_equation (z : ℍ) :
    modularJ (specialTauHalfPlane z) = sourceJ triangleSphereUniformization z :=
  specialTauHalfPlane_modular z

/-- The order-four branching of the actual sphere coordinate forces even
zeros of the genuine Eisenstein pullback. -/
theorem finiteEvenZeros : MuGenerator.FiniteEvenZeros specialTauHalfPlane := by
  apply MuGenerator.finiteEvenZeros_of_modular_equation
    (specialTauHalfPlane_holomorphic.mdifferentiable (by simp)) modular_source_equation
  intro z hz
  refine ⟨1, ?_⟩
  simpa only [Nat.mul_one, Nat.cast_ofNat] using
    sourceJ_sub_1728_order_of_eq triangleSphereUniformization
      triangleSphereUniformization_cusp triangleSphereUniformization_centerTwo z hz

/-- The actual first elliptic lift has order one. -/
theorem tau_order_centerOne :
    analyticOrderAt
      (fun z : ℂ => (specialTauHalfPlane (ofComplex z) : ℂ) - rho)
      (centerOne : ℂ) = 1 := by
  have hz := sourceJ_centerOne triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
  have ho := sourceJ_order_centerOne triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
  have h := ModularGermLift.native_modularJ_lift_order_of_zero
    (specialTauHalfPlane_holomorphic.mdifferentiable (by simp)) modular_source_equation
    (a := centerOne) (n := 1) hz
    (by simpa only [Nat.mul_one, Nat.cast_ofNat] using ho)
  simpa only [specialTauHalfPlane_centerOne, coe_rhoPoint, Nat.cast_one] using h

/-- The actual second elliptic lift has order two. -/
theorem tau_order_centerTwo :
    analyticOrderAt
      (fun z : ℂ => (specialTauHalfPlane (ofComplex z) : ℂ) - Complex.I)
      (centerTwo : ℂ) = 2 := by
  have hz := sourceJ_centerTwo triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerTwo
  have ho := sourceJ_sub_1728_order_centerTwo triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerTwo
  have h := ModularGermLift.native_modularJ_lift_order_of_1728
    (specialTauHalfPlane_holomorphic.mdifferentiable (by simp)) modular_source_equation
    (a := centerTwo) (n := 2) hz (by simpa using ho)
  simpa only [specialTauHalfPlane_centerTwo, coe_I, Nat.cast_ofNat] using h

/-- The proved analytic root construction applied to the actual special
period.  There is no independent square-root existence hypothesis. -/
def root : MuGenerator.Root specialTauHalfPlane :=
  MuGenerator.root specialTauHalfPlane
    (specialTauHalfPlane_holomorphic.mdifferentiable (by simp)) finiteEvenZeros

theorem root_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω root := root.holomorphic

theorem root_square (z : ℍ) : root z ^ 2 = E₆ (specialTauHalfPlane z) :=
  root.square z

/-- The source's global function, formed from genuine modular forms. -/
def generator : ℍ → ℂ := root.generator

theorem generator_formula (z : ℍ) :
    generator z = E₄ (specialTauHalfPlane z) ^ 2 * root z /
      discriminant (specialTauHalfPlane z) := rfl

theorem generator_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω generator :=
  root.generator_holomorphic specialTauHalfPlane_holomorphic

theorem generator_analyticAt (z : ℍ) :
    AnalyticAt ℂ (generator ∘ ofComplex) (z : ℂ) :=
  root.generator_analyticAt specialTauHalfPlane_holomorphic z

theorem generator_homogeneous : MuGenerator.Homogeneous specialTauHalfPlane generator :=
  root.generator_homogeneous specialTauHalfPlane_holomorphic
    specialTauHalfPlane_covariant tau_order_centerTwo

theorem generator_generator₁ (z : ℍ) :
    generator (generatorOneSL • z) = -generator z / specialTau z := by
  simpa only [specialTauHalfPlane_coe] using generator_homogeneous.1 z

theorem generator_generator₂ (z : ℍ) :
    generator (generatorTwoSL • z) = generator z / specialTau z := by
  simpa only [specialTauHalfPlane_coe] using generator_homogeneous.2 z

/-- The source's actual clockwise cusp word fixes the generator. -/
theorem generator_cusp (z : ℍ) :
    generator (triangleGeometricRepresentation triangleCuspGenerator z) = generator z := by
  have hprod (w : ℍ) :
      generator (triangleGeometricRepresentation (triangleGenerator₁ * triangleGenerator₂) w) =
        generator w := by
    rw [map_mul, Equiv.Perm.mul_apply, triangleGeometricRepresentation_generator₁_apply,
      triangleGeometricRepresentation_generator₂_apply, generator_homogeneous.1,
      generator_homogeneous.2, specialTauHalfPlane_covariant.2]
    field_simp [(specialTauHalfPlane w).ne_zero]
    simp only [mul_div_cancel_right₀ _ (specialTauHalfPlane w).ne_zero]
  have hp := hprod (triangleGeometricRepresentation triangleCuspGenerator z)
  have he : triangleGeometricRepresentation (triangleGenerator₁ * triangleGenerator₂)
      (triangleGeometricRepresentation triangleCuspGenerator z) = z := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, triangle_generators_cusp_relation, map_one]
    rfl
  rw [he] at hp
  exact hp.symm

theorem generator_eq_zero_iff_orbits (z : ℍ) :
    generator z = 0 ↔ triangleOrbitProjection z = triangleOrbitCenterOne ∨
      triangleOrbitProjection z = triangleOrbitCenterTwo :=
  MuTorsor.generator_zero_iff_orbits triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo specialTauHalfPlane_modular root z

theorem generator_ne_zero_iff_regular (z : ℍ) :
    generator z ≠ 0 ↔ z ∈ triangleRegularLocus := by
  rw [← triangleOrbitProjection_mem_regularDomain_iff, triangleOrbitRegularDomain_mem_iff]
  simpa only [not_or] using not_congr (generator_eq_zero_iff_orbits z)

theorem generator_ne_zero_regular (z : TriangleRegularPoint) : generator z.val ≠ 0 :=
  (generator_ne_zero_iff_regular z.val).mpr z.property

theorem generator_order_centerOne :
    analyticOrderAt (generator ∘ ofComplex) (centerOne : ℂ) = 2 :=
  root.generator_order_centerOne_of_tau_order specialTauHalfPlane_holomorphic
    specialTauHalfPlane_covariant tau_order_centerOne

theorem generator_order_centerTwo :
    analyticOrderAt (generator ∘ ofComplex) (centerTwo : ℂ) = 1 :=
  root.generator_order_centerTwo_of_tau_order specialTauHalfPlane_holomorphic
    specialTauHalfPlane_covariant tau_order_centerTwo

theorem generator_order_translated_centerOne (g : TriangleGroup) :
    analyticOrderAt (generator ∘ ofComplex)
      (triangleGeometricRepresentation g centerOne : ℂ) = 2 :=
  root.generator_order_translated_centerOne specialTauHalfPlane_holomorphic
    specialTauHalfPlane_covariant tau_order_centerOne tau_order_centerTwo g

theorem generator_order_translated_centerTwo (g : TriangleGroup) :
    analyticOrderAt (generator ∘ ofComplex)
      (triangleGeometricRepresentation g centerTwo : ℂ) = 1 :=
  root.generator_order_translated_centerTwo specialTauHalfPlane_holomorphic
    specialTauHalfPlane_covariant tau_order_centerTwo g

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalGenerator
