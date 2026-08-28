import Wikipedia.HopfProblem.DegreeCollapseIntegralEmbeddingRange
import Wikipedia.HopfProblem.DegreeCollapseSevenMeridianCocycle

/-!
# The normalized meridian class in the actual relative pair

The exterior is its literal closed embedded range in the original old
half. The constructed original cocycle descends through that actual
relative-chain quotient. A constructed original relative cycle has
evaluation one and its actual connecting class is the original meridian.
-/

noncomputable section

open Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization FirstHurewicz
open SingularMayerVietoris SingularCohomologyFree IntegralTorsionEvaluation SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

abbrev halfExteriorRange : Set (OldPositiveHalf A T) := Set.range (halfOldInclusion A hA T)

theorem halfOldInclusion_isEmbedding : IsEmbedding (halfOldInclusion A hA T) :=
  (halfBoundaryPair A hA T).oldExterior_closed.isEmbedding

variable [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)]

def relativeMeridianCocycle (s : Sphere 3) :
    RelativeIntegralCap.Cocycle (halfExteriorRange A hA T) 4 :=
  IntegralRelativeCocycleLift.relativeCocycle (halfExteriorRange A hA T) 4
    (meridianCocycle A hA T s)
    (IntegralEmbeddingRange.restriction_range_zero (halfOldInclusion A hA T)
      (halfOldInclusion_isEmbedding A hA T) 4 (meridianCocycle A hA T s).val
      (meridianCocycle_restriction_zero A hA T s))

def relativeMeridianClass (s : Sphere 3) :
    RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4 :=
  cocycleClass (RelativeIntegralCap.cochainComplex (halfExteriorRange A hA T)) 4
    (relativeMeridianCocycle A hA T s)

theorem relativeMeridianCocycle_toAbsolute (s : Sphere 3) :
    mapCocycles (RelativeIntegralCap.toAbsoluteMap (halfExteriorRange A hA T)) 4
      (relativeMeridianCocycle A hA T s) = meridianCocycle A hA T s :=
  IntegralRelativeCocycleLift.relativeCocycle_toAbsolute (halfExteriorRange A hA T) 4
    (meridianCocycle A hA T s) _

theorem relativeMeridianClass_toAbsolute (s : Sphere 3) :
    (HomologicalComplex.homologyMap
      (RelativeIntegralCap.toAbsoluteMap (halfExteriorRange A hA T)) 4).hom
      (relativeMeridianClass A hA T s) = meridianCohomologyClass A hA T s :=
  IntegralRelativeCocycleLift.relativeClass_toAbsolute (halfExteriorRange A hA T) 4
    (meridianCocycle A hA T s) _

theorem relativeMeridianCocycle_quotientMap (s : Sphere 3) (B : Chains (OldPositiveHalf A T) 4) :
    (relativeMeridianCocycle A hA T s).val
      (RelativeSingularHomology.quotientMap (halfExteriorRange A hA T) 4 B) =
    (meridianCocycle A hA T s).val B :=
  IntegralRelativeCocycleLift.relativeCocycle_quotientMap (halfExteriorRange A hA T) 4
    (meridianCocycle A hA T s) _ B

theorem exists_relative_meridian_cycle (s : Sphere 3) :
    ∃ w : ModuleHomology.Cycle (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4,
      cohomologyEvaluation (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4
        (relativeMeridianClass A hA T s)
        (ModuleHomology.cycleClass
          (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4 w)
          = 1 ∧
      RelativeSingularHomology.connecting (halfExteriorRange A hA T) 3
        (ModuleHomology.cycleClass
          (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4 w) =
      singularHomologyMap (IntegralEmbeddingRange.rangeMap (halfOldInclusion A hA T)) 3
        (halfMeridianClass A hA T s) := by
  obtain ⟨z, B, hz, hB, hunit⟩ := exists_normalized_meridian_chain A hA T s
  refine ⟨IntegralEmbeddingRange.rangeCycle (halfOldInclusion A hA T) 3 z B hB, ?_, ?_⟩
  · change cohomologyEvaluation _ 4
      (cocycleClass _ 4 (relativeMeridianCocycle A hA T s)) _ = 1
    rw [cohomologyEvaluation_cocycle_cycle]
    change (relativeMeridianCocycle A hA T s).val
      (RelativeSingularHomology.quotientMap (halfExteriorRange A hA T) 4 B) = 1
    rw [relativeMeridianCocycle_quotientMap]
    exact hunit
  · have he := IntegralEmbeddingRange.connecting_rangeCycle (halfOldInclusion A hA T) 3 z B hB
    rw [hz] at he
    exact he

theorem relativeMeridianClass_ne_zero (s : Sphere 3) : relativeMeridianClass A hA T s ≠ 0 := by
  obtain ⟨w, hw, _⟩ := exists_relative_meridian_cycle A hA T s
  intro h
  rw [h, map_zero, LinearMap.zero_apply] at hw
  exact zero_ne_one hw

theorem relativeMeridianClass_primitive (s : Sphere 3) (k : ℤ)
    (c : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4)
    (h : relativeMeridianClass A hA T s = k • c) : IsUnit k := by
  obtain ⟨w, hw, _⟩ := exists_relative_meridian_cycle A hA T s
  rw [h, map_zsmul] at hw
  change k • cohomologyEvaluation
    (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4 c
    (ModuleHomology.cycleClass
      (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4 w) = 1 at hw
  rw [zsmul_eq_mul] at hw
  exact isUnit_iff_dvd_one.mpr ⟨_, hw.symm⟩

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
