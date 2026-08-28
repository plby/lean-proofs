import Wikipedia.HopfProblem.DegreeCollapseSevenPrimitiveCoreDual
import Wikipedia.HopfProblem.DegreeCollapseSurgeryRelativeFourDetection

/-!
# A primitive positive attaching core has zero actual meridian

The normalized core class generates actual relative fourth cohomology.
Local integral evaluation detects relative fourth homology, and the
constructed primitive unit dual makes the original absolute-to-relative
map surjective. Exactness then makes the actual exterior inclusion an
isomorphism on H3 and kills its original meridian. There is no finite-H3
or zero-H4 hypothesis on the positive half or the closed ambient space.
-/

noncomputable section

open CategoryTheory Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization FirstHurewicz
open SingularMayerVietoris SingularCohomologyFree SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] [SimplyConnectedSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)
  {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)

include C in
theorem coreThomHalf_evaluation_injective :
    Injective (cohomologyEvaluation
      (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4 (coreThomHalf A hA T)) :=
  SurgeryRelativeFour.generator_evaluation_injective (halfBoundaryPair A hA T)
    (coreThomHalf A hA T) (coreThomHalf_generates A hA T C)

theorem coreThomHalf_toRelative_evaluation (z : SingularHomology (OldPositiveHalf A T) 4) :
    cohomologyEvaluation (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4
        (coreThomHalf A hA T) (RelativeSingularHomology.toRelative (halfExteriorRange A hA T) 4 z) =
      singularEvaluation (OldPositiveHalf A T) 4
        ((HomologicalComplex.homologyMap
          (RelativeIntegralCap.toAbsoluteMap (halfExteriorRange A hA T)) 4).hom
          (coreThomHalf A hA T)) z :=
  (cohomologyEvaluation_naturality (RelativeSingularHomology.projection
    (halfExteriorRange A hA T)) 4 (coreThomHalf A hA T) z).symm

variable [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
  [Subsingleton (SingularHomology B 4)]
  (σ : SingularHomology (OldPositiveHalf A T) 3 →ₗ[ℤ] ℤ)
  (hσ : σ (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
    (unitSphereTopClass 2)) = 1)

include C hσ in
theorem primitive_toRelative_surjective :
    Surjective (RelativeSingularHomology.toRelative (halfExteriorRange A hA T) 4) := by
  obtain ⟨z, hz⟩ := exists_primitive_core_unit_dual A hA T C σ hσ
  have hu : cohomologyEvaluation (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4
      (coreThomHalf A hA T)
      (RelativeSingularHomology.toRelative (halfExteriorRange A hA T) 4 z) = 1 :=
    (coreThomHalf_toRelative_evaluation A hA T z).trans hz
  intro x
  let k := cohomologyEvaluation (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4
    (coreThomHalf A hA T) x
  refine ⟨k • z, coreThomHalf_evaluation_injective A hA T C ?_⟩
  rw [map_zsmul, map_zsmul, hu]
  change k • (1 : ℤ) = k
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

include C hσ in
theorem primitive_relative_connecting_zero
    (x : RelativeSingularHomology.Homology (halfExteriorRange A hA T) 4) :
    RelativeSingularHomology.connecting (halfExteriorRange A hA T) 3 x = 0 := by
  obtain ⟨z, rfl⟩ := primitive_toRelative_surjective A hA T C σ hσ x
  exact (RelativeSingularHomology.exact_at_relative (halfExteriorRange A hA T) 3).le ⟨z, rfl⟩

include C hσ in
theorem primitive_halfOldInclusion_bijective :
    Bijective (singularHomologyMap (halfOldInclusion A hA T) 3) := by
  have hi : Injective (singularHomologyMap
      (subtypeInclusion (halfExteriorRange A hA T)) 3) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨w, hw⟩ := (RelativeSingularHomology.exact_at_subspace
      (halfExteriorRange A hA T) 3).ge hx
    exact hw.symm.trans (primitive_relative_connecting_zero A hA T C σ hσ w)
  refine ⟨?_, halfOldInclusion_surjective A hA T⟩
  intro x y hxy
  apply (IntegralEmbeddingRange.rangeMap_homology_bijective (halfOldInclusion A hA T)
    (halfOldInclusion_isEmbedding A hA T) 3).1
  apply hi
  rw [IntegralEmbeddingRange.inclusion_rangeMap_homology,
    IntegralEmbeddingRange.inclusion_rangeMap_homology]
  exact hxy

include C hσ in
theorem primitive_halfMeridianClass_zero (s : Sphere 3) :
    halfMeridianClass A hA T s = 0 := by
  apply (primitive_halfOldInclusion_bijective A hA T C σ hσ).1
  rw [map_zero]
  exact SurgeryExteriorSequence.Seven.inclusion_meridian (halfBoundaryPair A hA T) s
    (unitSphereTopClass 2)

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
