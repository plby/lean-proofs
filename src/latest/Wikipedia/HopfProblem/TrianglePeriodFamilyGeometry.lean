import Wikipedia.HopfProblem.TrianglePeriodFamilyFibres
import Wikipedia.HopfProblem.TrianglePeriodFamilyLocal
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegular

/-!
# The descended family on the actual regular triangle quotient

An admissible holomorphic period map on the actual upper half-plane,
with the two source transformation laws, restricts to the proved regular
triangle domain.  All geometric covering hypotheses are discharged by
the actual triangle action.  The resulting proper holomorphic torus
family and zero section are constructed from the supplied periods.

This theorem does not assert existence of the source's global special
period functions; that is a separate analytic construction.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods

/-- Restriction of the actual supplied periods to the actual regular
open subset of the upper half-plane. -/
def regularPeriods (P : HolomorphicPeriodMap ℂ ℍ) :
    HolomorphicPeriodMap ℂ TriangleRegularPoint where
  point z := P.point z.val
  holomorphic_tau := P.holomorphic_tau.comp (contMDiff_subtype_val (U := triangleRegularDomain))
  holomorphic_mu := P.holomorphic_mu.comp (contMDiff_subtype_val (U := triangleRegularDomain))
  holomorphic_beta := P.holomorphic_beta.comp (contMDiff_subtype_val (U := triangleRegularDomain))

@[simp] theorem regularPeriods_point (P : HolomorphicPeriodMap ℂ ℍ)
    (z : TriangleRegularPoint) : (regularPeriods P).point z = P.point z.val := rfl

/-- The actual regular family input is constructed using the proved
holomorphic geometric action and just the two generator period laws. -/
def regularData (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Data ℂ TriangleRegularPoint where
  periods := regularPeriods P
  base_holomorphic := triangleRegularAction_holomorphic
  covariance₁ z := by
    change P.point (triangleGeometricRepresentation triangleGenerator₁ z.val) = _
    rw [triangleGeometricRepresentation_generator₁_apply]
    exact h₁ z.val
  covariance₂ z := by
    change P.point (triangleGeometricRepresentation triangleGenerator₂ z.val) = _
    rw [triangleGeometricRepresentation_generator₂_apply]
    exact h₂ z.val

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The regular covering required by the quotient construction is the
already proved actual triangle covering, not an extra hypothesis. -/
theorem regularCovering :
    IsQuotientCoveringMap (regularData P h₁ h₂).baseQuotient TriangleGroup :=
  triangleRegularProject_covering

/-- The selected base atlas is literally the established atlas on the
actual regular triangle orbit quotient. -/
theorem regularBase_chartedSpace_eq :
    (regularData P h₁ h₂).baseChartedSpace (regularCovering P h₁ h₂) =
      triangleRegularQuotientChartedSpace := rfl

/-- The actual regular family is locally identified with the full
varying-period family over the selected base inverse branch. -/
def regularLocalBiholomorph (z : TriangleRegularPoint) :
    let D := regularData P h₁ h₂
    let hq := regularCovering P h₁ h₂
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (D.upstairsPatch hq z) (D.downstairsPatch hq z) ω :=
  (regularData P h₁ h₂).localBiholomorph (regularCovering P h₁ h₂) z

/-- These full analytic local models cover the actual descended family. -/
theorem regularFamily_localModels_cover (y : (regularData P h₁ h₂).Space) :
    ∃ z : TriangleRegularPoint,
      y ∈ (regularData P h₁ h₂).downstairsPatch (regularCovering P h₁ h₂) z := by
  let D := regularData P h₁ h₂
  let hq := regularCovering P h₁ h₂
  obtain ⟨z, hz⟩ := D.baseQuotient_surjective (D.projection y)
  refine ⟨z, ?_⟩
  change D.projection y ∈ D.basePatch hq z
  rw [← hz]
  exact DiagonalQuotient.baseQuotient_mem_patch hq z

/-- Theorem 3.4(v), as a construction from supplied global admissible
holomorphic periods: the actual regular triangle quotient carries the
proper surjective holomorphic torus submersion with its actual section.
There are no remaining geometric covering or quotient-manifold hypotheses. -/
theorem regularFamily_construction :
    let D := regularData P h₁ h₂
    let hq := regularCovering P h₁ h₂
    letI := D.baseChartedSpace hq
    letI := D.chartedSpace hq
    T2Space D.Space ∧ SecondCountableTopology D.Space ∧
      IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.Space ∧
      IsProperMap D.projection ∧ Function.Surjective D.projection ∧
      ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ ℂ) ω D.projection ∧
      Manifold.IsSubmersionOfComplement ComplexPlane₂
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
        D.projection ∧
      ContMDiff (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.zeroSection ∧
      Function.LeftInverse D.projection D.zeroSection := by
  let D := regularData P h₁ h₂
  let hq := regularCovering P h₁ h₂
  let := D.baseChartedSpace hq
  let := D.chartedSpace hq
  exact ⟨D.spaceT2Space_of_properlyDiscontinuous hq, D.spaceSecondCountable hq,
    D.isManifold hq, D.projection_proper hq, D.projection_surjective,
    D.projection_holomorphic hq, D.projection_submersion hq,
    D.zeroSection_holomorphic hq, D.projection_zeroSection⟩

/-- Each actual regular fibre is parametrized by its original complex
period torus as a closed holomorphic smooth embedding. -/
theorem regularFibre_closed_holomorphic_embedding (z : TriangleRegularPoint) :
    let D := regularData P h₁ h₂
    let hq := regularCovering P h₁ h₂
    letI := D.chartedSpace hq
    range (D.fibreInclusion z) = D.projection ⁻¹' {D.baseQuotient z} ∧
      IsClosedEmbedding (D.fibreInclusion z) ∧
      ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (D.fibreInclusion z) ∧
      Manifold.IsSmoothEmbedding (modelWithCornersSelf ℂ ComplexPlane₂)
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (D.fibreInclusion z) := by
  let D := regularData P h₁ h₂
  let hq := regularCovering P h₁ h₂
  let := D.chartedSpace hq
  let := D.spaceT2Space_of_properlyDiscontinuous hq
  exact ⟨D.fibreInclusion_range hq z, D.fibreInclusion_isClosedEmbedding hq z,
    D.fibreInclusion_holomorphic hq z, D.fibreInclusion_isSmoothEmbedding hq z⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily
