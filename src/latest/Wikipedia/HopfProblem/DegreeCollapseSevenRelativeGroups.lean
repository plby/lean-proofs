import Wikipedia.HopfProblem.DegreeCollapseIntegralEmbeddingRangeHomology
import Wikipedia.HopfProblem.DegreeCollapseSevenRelativeMeridian
import Wikipedia.NoExoticSixSphere.RelativeIntegralChainsFree

/-!
# The original relative meridian generates the degree-four pair groups

The genuine surgery sequence makes the exterior inclusion injective
in degree two. Together with its proved degree-three surjectivity this
kills the actual relative H3. The original connecting map and meridian
kernel then generate relative H4. Original integral cohomology evaluation
shows that the normalized relative meridian class generates relative H4
cohomology as well.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorSequence.Seven

open SingularMayerVietoris Wikipedia.SmoothSixDPoincare NoExoticSixSphere

theorem inclusion_second_injective
    {R X Y : Type} [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (d : SurgeryBoundaryPair (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4)) R X Y) :
    Injective (singularHomologyMap (inclusion d) 2) := by
  let : Subsingleton (SingularHomology (Sphere 3 × Sphere 3) 2) := corner_second_homology
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hp : (a, 0) ∈ LinearMap.ker (rightMap d 2) := by
    change rightMap d 2 (a, 0) = 0
    rw [rightMap_apply, map_zero, add_zero]
    exact ha
  obtain ⟨c, hc⟩ := (exact_at_exterior_core d 2).ge hp
  have hc0 : c = 0 := Subsingleton.elim _ _
  rw [hc0, map_zero] at hc
  exact (congrArg Prod.fst hc).symm

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorSequence.Seven

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization FirstHurewicz
open SingularMayerVietoris SingularCohomologyFree SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

theorem relative_third_homology_subsingleton :
    Subsingleton (RelativeSingularHomology.Homology (halfExteriorRange A hA T) 3) :=
  IntegralEmbeddingRange.relative_homology_subsingleton (halfOldInclusion A hA T)
    (halfOldInclusion_isEmbedding A hA T) 2 (halfOldInclusion_surjective A hA T)
    (SurgeryExteriorSequence.Seven.inclusion_second_injective (halfBoundaryPair A hA T))

variable [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)]

def relativeMeridianEvaluation (s : Sphere 3) :
    RelativeSingularHomology.Homology (halfExteriorRange A hA T) 4 →ₗ[ℤ] ℤ :=
  cohomologyEvaluation (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4
    (relativeMeridianClass A hA T s)

theorem relativeMeridianEvaluation_bijective (s : Sphere 3) :
    Bijective (relativeMeridianEvaluation A hA T s) := by
  obtain ⟨w, hunit, hδ⟩ := exists_relative_meridian_cycle A hA T s
  let W := ModuleHomology.cycleClass
    (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4 w
  have hgen (x : RelativeSingularHomology.Homology (halfExteriorRange A hA T) 4) :
      ∃ k : ℤ, k • W = x :=
    IntegralEmbeddingRange.relative_class_multiple (halfOldInclusion A hA T)
      (halfOldInclusion_isEmbedding A hA T) 3 (halfMeridianClass A hA T s)
      (halfOldInclusion_addKernel A hA T s) W hδ x
  have heval (k : ℤ) : relativeMeridianEvaluation A hA T s (k • W) = k := by
    rw [map_zsmul]
    change k • cohomologyEvaluation
      (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4
      (relativeMeridianClass A hA T s) W = k
    rw [hunit, zsmul_eq_mul, mul_one, Int.cast_id]
  constructor
  · intro x y hxy
    obtain ⟨k, rfl⟩ := hgen x
    obtain ⟨l, rfl⟩ := hgen y
    rw [heval, heval] at hxy
    rw [hxy]
  · intro k
    exact ⟨k • W, heval k⟩

def relativeMeridianHomologyEquiv (s : Sphere 3) :
    RelativeSingularHomology.Homology (halfExteriorRange A hA T) 4 ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective (relativeMeridianEvaluation A hA T s)
    (relativeMeridianEvaluation_bijective A hA T s)

theorem relativeMeridianHomologyEquiv_toLinearMap (s : Sphere 3) :
    (relativeMeridianHomologyEquiv A hA T s).toLinearMap =
      relativeMeridianEvaluation A hA T s := rfl

theorem relativeMeridianClass_generates (s : Sphere 3)
    (c : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4) :
    ∃ k : ℤ, k • relativeMeridianClass A hA T s = c := by
  let K := RelativeSingularHomology.complex (halfExteriorRange A hA T)
  let (j : ℕ) : Module.Free ℤ (K.X j) :=
    RelativeSingularHomology.chains_free (halfExteriorRange A hA T) j
  let : Subsingleton (K.homology 3) := relative_third_homology_subsingleton A hA T
  let : Module.Free ℤ (K.homology 3) := Module.Free.of_subsingleton ℤ _
  obtain ⟨w, hunit, hδ⟩ := exists_relative_meridian_cycle A hA T s
  let W := ModuleHomology.cycleClass K 4 w
  let k := cohomologyEvaluation K 4 c W
  refine ⟨k, LocalEvaluation.cohomologyEvaluation_succ_injective K 3 ?_⟩
  ext x
  obtain ⟨l, rfl⟩ := IntegralEmbeddingRange.relative_class_multiple (halfOldInclusion A hA T)
    (halfOldInclusion_isEmbedding A hA T) 3 (halfMeridianClass A hA T s)
    (halfOldInclusion_addKernel A hA T s) W hδ x
  simp only [map_zsmul]
  change l • (k • cohomologyEvaluation K 4 (relativeMeridianClass A hA T s) W) = l • k
  rw [hunit]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
