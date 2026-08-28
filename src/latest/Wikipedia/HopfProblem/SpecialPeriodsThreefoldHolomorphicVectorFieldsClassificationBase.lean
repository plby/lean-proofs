import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularFibreTopology
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlasAgreement

/-!
# The actual base component on the regular vector cover

The projection from the original regular upper-half-plane domain to the
sphere is locally biholomorphic. The genuine projection square therefore
identifies its vertical tangent kernel with the two fibre directions of
the original period-vector cover.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open Triangle HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace HolomorphicForms.RegularCover.cover_isManifold
  triangleCompactifiedChartedSpace

/-- The original regular upper-half-plane representative maps locally
biholomorphically to the actual sphere base. -/
theorem regularSphereValue_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω Threefold.regularSphereValue := by
  intro z
  have h := (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) triangleRegularDomain z).comp
    (K := 𝓘(ℂ)) (P := TriangleCompactifiedOrbitSpace)
    (triangleCompactifiedProjection_isLocalDiffeomorphAt_of_regular z.property)
  exact h.comp (K := 𝓘(ℂ)) (P := RiemannSphere)
    (triangleSphereUniformization.isLocalDiffeomorph (triangleCompactifiedProjection z.val))

theorem regularCover_projectionSphere (x : Cover) :
    Threefold.projectionSphere (globalCover x) = Threefold.regularSphereValue x.1 := by
  change triangleSphereUniformization
      (Threefold.projection (Threefold.regularFamilyInclusion
        (data.quotient (data.periods.quotientMap x)))) =
    triangleSphereUniformization (triangleCompactifiedProjection x.1.val)
  rw [Threefold.regularFamilyInclusion_projection]
  exact congrArg triangleSphereUniformization
    (Threefold.regularFamilyProjectionToBase_quotient specialPeriodMap
      specialPeriodMap_generator₁ specialPeriodMap_generator₂ (data.periods.quotientMap x))

/-- This assertion uses the actual differentials of both maps, before
any coefficient normal form is introduced. -/
theorem baseComponent_eq_zero_of_projection (x : Cover) (u : ℂ × ComplexPlane₂)
    (hu : mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (globalCover x)
      (mfderiv IF IF globalCover x u) = 0) : u.1 = 0 := by
  have hf : HasMFDerivAt IF 𝓘(ℂ) (Prod.fst : Cover → TriangleRegularPoint) x
      (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact hasMFDerivAt_fst x
  have hb := (regularSphereValue_isLocalDiffeomorph.contMDiff.mdifferentiable (by simp)
    x.1).hasMFDerivAt
  have he : Threefold.projectionSphere ∘ globalCover =
      Threefold.regularSphereValue ∘ (Prod.fst : Cover → TriangleRegularPoint) :=
    funext regularCover_projectionSphere
  have hz := (mfderiv_comp_apply x
    (Threefold.projectionSphere_holomorphic.mdifferentiable (by simp) (globalCover x))
    (globalCover_holomorphic.mdifferentiable (by simp) x) u).trans hu
  rw [he, (hb.comp x hf).mfderiv] at hz
  apply ((regularSphereValue_isLocalDiffeomorph x.1).mfderivToContinuousLinearEquiv
    (by simp)).injective
  change mfderiv 𝓘(ℂ) 𝓘(ℂ) Threefold.regularSphereValue x.1 u.1 =
    mfderiv 𝓘(ℂ) 𝓘(ℂ) Threefold.regularSphereValue x.1 0
  rw [map_zero]
  exact hz

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
