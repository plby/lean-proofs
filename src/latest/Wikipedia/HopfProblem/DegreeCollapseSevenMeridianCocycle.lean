import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionSingularNormalization
import Wikipedia.HopfProblem.DegreeCollapseSevenMeridianCharacter

/-!
# A normalized original integral cocycle for the actual meridian character

The original exterior inclusion is injective on points. Its actual
meridian character and rational coordinate therefore construct a degree
four integral cocycle vanishing on every original exterior chain. Its
original torsion evaluation is exactly that character, and its rational
primitive takes value one on the original meridian. No finiteness of
the exterior homology or normalized-cochain premise is used.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization FirstHurewicz
open SingularMayerVietoris SingularCohomologyFree IntegralTorsionEvaluation SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

theorem halfOldInclusion_injective : Injective (halfOldInclusion A hA T) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun p : OldPositiveHalf A T ↦ p.val) h

variable [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)]

theorem exists_meridianCocycle (s : Sphere 3) :
    ∃ c : Cocycle (singularCochainComplex (OldPositiveHalf A T)) 4,
      (singularTorsionEvaluation (OldPositiveHalf A T) 3
        (cocycleClass (singularCochainComplex (OldPositiveHalf A T)) 4 c)).toAddMonoidHom =
          meridianCharacter A hA T s ∧
      c.val.comp (inducedChain (halfOldInclusion A hA T) 4) = 0 ∧
      ∀ z : ModuleHomology.Cycle (singularComplex (HalfExterior A hA T)) 3,
        rationalPrimitive (singularComplex (OldPositiveHalf A T)) 3 c
          (inducedChain (halfOldInclusion A hA T) 3 z.val) =
        meridianRationalCoordinate A hA T s
          (ModuleHomology.cycleClass (singularComplex (HalfExterior A hA T)) 3 z) :=
  exists_singular_normalized_cocycle (halfOldInclusion A hA T)
    (halfOldInclusion_injective A hA T) 3 (meridianCharacter A hA T s)
    (meridianRationalCoordinate A hA T s) (meridianCharacter_oldInclusion A hA T s)

def meridianCocycle (s : Sphere 3) :
    Cocycle (singularCochainComplex (OldPositiveHalf A T)) 4 :=
  (exists_meridianCocycle A hA T s).choose

def meridianCohomologyClass (s : Sphere 3) : SingularCohomology (OldPositiveHalf A T) 4 :=
  cocycleClass (singularCochainComplex (OldPositiveHalf A T)) 4 (meridianCocycle A hA T s)

theorem meridianCohomologyClass_evaluation (s : Sphere 3) :
    (singularTorsionEvaluation (OldPositiveHalf A T) 3
      (meridianCohomologyClass A hA T s)).toAddMonoidHom = meridianCharacter A hA T s :=
  (exists_meridianCocycle A hA T s).choose_spec.1

theorem meridianCocycle_restriction_zero (s : Sphere 3) :
    (meridianCocycle A hA T s).val.comp (inducedChain (halfOldInclusion A hA T) 4) = 0 :=
  (exists_meridianCocycle A hA T s).choose_spec.2.1

theorem meridianCocycle_rational_cycle (s : Sphere 3)
    (z : ModuleHomology.Cycle (singularComplex (HalfExterior A hA T)) 3) :
    rationalPrimitive (singularComplex (OldPositiveHalf A T)) 3 (meridianCocycle A hA T s)
      (inducedChain (halfOldInclusion A hA T) 3 z.val) =
    meridianRationalCoordinate A hA T s
      (ModuleHomology.cycleClass (singularComplex (HalfExterior A hA T)) 3 z) :=
  (exists_meridianCocycle A hA T s).choose_spec.2.2 z

theorem meridianCocycle_rational_meridian (s : Sphere 3)
    (z : ModuleHomology.Cycle (singularComplex (HalfExterior A hA T)) 3)
    (hz : ModuleHomology.cycleClass (singularComplex (HalfExterior A hA T)) 3 z =
      halfMeridianClass A hA T s) :
    rationalPrimitive (singularComplex (OldPositiveHalf A T)) 3 (meridianCocycle A hA T s)
      (inducedChain (halfOldInclusion A hA T) 3 z.val) = 1 := by
  rw [meridianCocycle_rational_cycle, hz, meridianRationalCoordinate_meridian]

theorem meridianCocycle_bounding_meridian (s : Sphere 3)
    (z : ModuleHomology.Cycle (singularComplex (HalfExterior A hA T)) 3)
    (hz : ModuleHomology.cycleClass (singularComplex (HalfExterior A hA T)) 3 z =
      halfMeridianClass A hA T s)
    (b : Chains (OldPositiveHalf A T) 4)
    (hb : ((singularComplex (OldPositiveHalf A T)).d 4 3).hom b =
      inducedChain (halfOldInclusion A hA T) 3 z.val) :
    (meridianCocycle A hA T s).val b = 1 := by
  have he := rationalPrimitive_boundary (singularComplex (OldPositiveHalf A T)) 3
    (meridianCocycle A hA T s) b
  rw [hb, meridianCocycle_rational_meridian A hA T s z hz] at he
  exact_mod_cast he.symm

theorem exists_normalized_meridian_chain (s : Sphere 3) :
    ∃ (z : ModuleHomology.Cycle (singularComplex (HalfExterior A hA T)) 3)
      (b : Chains (OldPositiveHalf A T) 4),
      ModuleHomology.cycleClass (singularComplex (HalfExterior A hA T)) 3 z =
        halfMeridianClass A hA T s ∧
      ((singularComplex (OldPositiveHalf A T)).d 4 3).hom b =
        inducedChain (halfOldInclusion A hA T) 3 z.val ∧
      (meridianCocycle A hA T s).val b = 1 := by
  obtain ⟨z, hz⟩ := ModuleHomology.cycleClass_surjective
    (singularComplex (HalfExterior A hA T)) 3 (halfMeridianClass A hA T s)
  have hμ : singularHomologyMap (halfOldInclusion A hA T) 3 (halfMeridianClass A hA T s) = 0 := by
    change halfMeridianClass A hA T s ∈
      (singularHomologyMap (halfOldInclusion A hA T) 3).toAddMonoidHom.ker
    rw [halfOldInclusion_addKernel]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, one_zsmul _⟩
  have hbound : ModuleHomology.cycleClass (singularComplex (OldPositiveHalf A T)) 3
      (ModuleHomology.mapCycles (singularChainMap (halfOldInclusion A hA T)) 3 z) = 0 := by
    rw [← ModuleHomology.homologyMap_cycleClass, hz]
    exact hμ
  obtain ⟨b, hb⟩ := (ModuleHomology.cycleClass_eq_zero_iff
    (singularComplex (OldPositiveHalf A T)) 3 _).mp hbound
  rw [ModuleHomology.mapCycles_val] at hb
  exact ⟨z, b, hz, hb, meridianCocycle_bounding_meridian A hA T s z hz b hb⟩

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
