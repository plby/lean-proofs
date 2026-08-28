import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry

/-!
# The genuine regular-family zero section inside the global threefold

The already constructed zero section of the original period family is
followed by the actual regular-piece inclusion.  Its projection and its
holomorphy are computed using the original quotient and glued atlases.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] triangleCompactifiedChartedSpace chartedSpace
  specialRegularFamilyChartedSpace

/-- The actual original zero section, included in the constructed global
threefold over the genuine regular compact-base patch. -/
def regularZeroSection : regularPatch → Space :=
  regularFamilyInclusion ∘ regularFamilyZeroSection specialPeriodMap
    specialPeriodMap_generator₁ specialPeriodMap_generator₂

@[simp] theorem regularZeroSection_apply (b : regularPatch) :
    regularZeroSection b = regularFamilyInclusion
      (regularFamilyZeroSection specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂ b) := rfl

/-- The actual compact-base projection of this section is the original
point, not merely a homotopic or locally identified base point. -/
@[simp] theorem projection_regularZeroSection (b : regularPatch) :
    projection (regularZeroSection b) = (b : TriangleCompactifiedOrbitSpace) := by
  rw [regularZeroSection_apply, regularFamilyInclusion_projection]
  exact congrArg (fun q : regularPatch => (q : TriangleCompactifiedOrbitSpace))
    (regularFamilyProjection_zeroSection specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ b)

@[simp] theorem projectionSphere_regularZeroSection (b : regularPatch) :
    projectionSphere (regularZeroSection b) = triangleSphereUniformization b :=
  congrArg triangleSphereUniformization (projection_regularZeroSection b)

theorem regularZeroSection_holomorphic : ContMDiff 𝓘(ℂ) IF ω regularZeroSection :=
  regularFamilyInclusion_holomorphic.comp
    (regularFamilyZeroSection_holomorphic specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂)

theorem regularZeroSection_continuous : Continuous regularZeroSection :=
  regularZeroSection_holomorphic.continuous

theorem regularZeroSection_isEmbedding : IsEmbedding regularZeroSection :=
  regularFamilyInclusion_isOpenEmbedding.isEmbedding.comp
    (regularFamilyZeroSection_isClosedEmbedding specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂).isEmbedding

theorem regularZeroSection_injective : Injective regularZeroSection :=
  regularZeroSection_isEmbedding.injective

theorem regularZeroSection_mem_regularLocus (b : regularPatch) :
    regularZeroSection b ∈ regularLocus := by
  rw [mem_regularLocus, projection_regularZeroSection]
  exact b.property

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
