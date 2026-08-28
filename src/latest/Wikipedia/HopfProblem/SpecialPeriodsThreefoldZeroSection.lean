import Wikipedia.HopfProblem.SpecialPeriodsThreefoldZeroSectionBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldZeroSectionRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreFunctions

/-!
# The actual holomorphic zero section over the regular sphere base

The genuine zero section of the period family is expressed over the
three-punctured sphere by restricting the constructed normalized sphere
uniformization. Both the global map into the threefold and its restriction
to the preimage of any base open set are holomorphic for the existing
native atlases. No submersion-section existence principle is assumed.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] triangleCompactifiedChartedSpace chartedSpace

/-- The original regular-family zero section, with its base expressed
in the actual normalized sphere coordinate. -/
def sphereRegularZeroSection : sphereRegularPatch → Space :=
  regularZeroSection ∘ regularSphereBiholomorph.symm

@[simp] theorem sphereRegularZeroSection_apply (b : sphereRegularPatch) :
    sphereRegularZeroSection b = regularZeroSection (regularSphereBiholomorph.symm b) := rfl

/-- The section lies above exactly the specified sphere point. -/
@[simp] theorem projectionSphere_sphereRegularZeroSection (b : sphereRegularPatch) :
    projectionSphere (sphereRegularZeroSection b) = (b : RiemannSphere) := by
  rw [sphereRegularZeroSection_apply, projectionSphere_regularZeroSection,
    regularSphereBiholomorph_symm_val]
  exact triangleSphereUniformization.apply_symm_apply (b : RiemannSphere)

theorem sphereRegularZeroSection_holomorphic :
    ContMDiff 𝓘(ℂ) IF ω sphereRegularZeroSection :=
  regularZeroSection_holomorphic.comp regularSphereBiholomorph.symm.contMDiff

theorem sphereRegularZeroSection_continuous : Continuous sphereRegularZeroSection :=
  sphereRegularZeroSection_holomorphic.continuous

theorem sphereRegularZeroSection_isEmbedding : IsEmbedding sphereRegularZeroSection :=
  regularZeroSection_isEmbedding.comp regularSphereBiholomorph.symm.toHomeomorph.isEmbedding

theorem sphereRegularZeroSection_injective : Injective sphereRegularZeroSection :=
  sphereRegularZeroSection_isEmbedding.injective

theorem sphereRegularZeroSection_mem_regularLocus (b : sphereRegularPatch) :
    sphereRegularZeroSection b ∈ regularLocus :=
  regularZeroSection_mem_regularLocus (regularSphereBiholomorph.symm b)

/-- The actual regular part of an arbitrary open subset of the sphere,
as an open subset of that original base open set. -/
def sphereRegularPart (U : Opens RiemannSphere) : Opens U :=
  ⟨{b : U | (b : RiemannSphere) ∈ sphereRegularPatch},
    sphereRegularPatch.isOpen.preimage continuous_subtype_val⟩

@[simp] theorem mem_sphereRegularPart (U : Opens RiemannSphere) (b : U) :
    b ∈ sphereRegularPart U ↔ (b : RiemannSphere) ∈ sphereRegularPatch := Iff.rfl

/-- Forget only the additional open-set membership; the sphere point
and its genuine regular-base coordinate remain unchanged. -/
def sphereRegularPartInclusion (U : Opens RiemannSphere) :
    sphereRegularPart U → sphereRegularPatch :=
  fun b => ⟨(b.val : RiemannSphere), b.property⟩

@[simp] theorem sphereRegularPartInclusion_val (U : Opens RiemannSphere)
    (b : sphereRegularPart U) :
    (sphereRegularPartInclusion U b : RiemannSphere) = (b.val : RiemannSphere) := rfl

/-- This inclusion is analytic, using the original open-submanifold
atlases at analytic order rather than only smooth order. -/
theorem sphereRegularPartInclusion_holomorphic (U : Opens RiemannSphere) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (sphereRegularPartInclusion U) := by
  have hval : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun b : sphereRegularPart U => (b.val : RiemannSphere)) :=
    (contMDiff_subtype_val (U := U)).comp
      (contMDiff_subtype_val (U := sphereRegularPart U))
  intro b
  have h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun c : sphereRegularPart U => (sphereRegularPartInclusion U c : RiemannSphere)) b ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sphereRegularPartInclusion U) b :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (hval b)

/-- Restrict the genuine section to the regular part of a base open set
and retain its literal codomain in the preimage of that open set. -/
def sphereRegularZeroSectionOn (U : Opens RiemannSphere) :
    sphereRegularPart U → basePreimage U := fun b =>
  ⟨sphereRegularZeroSection (sphereRegularPartInclusion U b), by
    change projectionSphere (sphereRegularZeroSection (sphereRegularPartInclusion U b)) ∈ U
    rw [projectionSphere_sphereRegularZeroSection, sphereRegularPartInclusion_val]
    exact b.val.property⟩

@[simp] theorem sphereRegularZeroSectionOn_val (U : Opens RiemannSphere)
    (b : sphereRegularPart U) :
    (sphereRegularZeroSectionOn U b : Space) =
      sphereRegularZeroSection (sphereRegularPartInclusion U b) := rfl

@[simp] theorem projectionSphere_sphereRegularZeroSectionOn (U : Opens RiemannSphere)
    (b : sphereRegularPart U) :
    projectionSphere (sphereRegularZeroSectionOn U b : Space) =
      (b.val : RiemannSphere) :=
  projectionSphere_sphereRegularZeroSection (sphereRegularPartInclusion U b)

/-- The same exact section equation with its values in the original
base open set, not only after forgetting the subtype. -/
@[simp] theorem sphereRegularZeroSectionOn_projection (U : Opens RiemannSphere)
    (b : sphereRegularPart U) :
    (⟨projectionSphere (sphereRegularZeroSectionOn U b : Space),
      (sphereRegularZeroSectionOn U b).property⟩ : U) = b.val :=
  Subtype.ext (projectionSphere_sphereRegularZeroSectionOn U b)

/-- Holomorphy of the actual restricted section into the literal open
preimage, proved at analytic order for its unchanged ambient atlas. -/
theorem sphereRegularZeroSectionOn_holomorphic (U : Opens RiemannSphere) :
    ContMDiff 𝓘(ℂ) IF ω (sphereRegularZeroSectionOn U) := by
  have hval : ContMDiff 𝓘(ℂ) IF ω
      (sphereRegularZeroSection ∘ sphereRegularPartInclusion U) :=
    sphereRegularZeroSection_holomorphic.comp (sphereRegularPartInclusion_holomorphic U)
  intro b
  have h : ContMDiffAt 𝓘(ℂ) IF ω
      (fun c : sphereRegularPart U => (sphereRegularZeroSectionOn U c : Space)) b ↔
      ContMDiffAt 𝓘(ℂ) IF ω (sphereRegularZeroSectionOn U) b :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (hval b)

theorem sphereRegularZeroSectionOn_continuous (U : Opens RiemannSphere) :
    Continuous (sphereRegularZeroSectionOn U) :=
  (sphereRegularZeroSectionOn_holomorphic U).continuous

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
