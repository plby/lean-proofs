import Wikipedia.HopfProblem.DegreeCollapseSevenCoreSupportedCap
import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenLinking

/-!
# The original meridian character and the closed linking pairing

For the actual half inclusion, forgetting the extended relative meridian
class pulls back to the original normalized meridian cohomology class.
Original torsion-evaluation naturality therefore identifies its evaluation
with the original exterior character. The proved local core cap theorem
supplies one integer unit, independent of the second homology argument.
Finiteness is used on the half and closed manifold, never on the exterior.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization FirstHurewicz
open SingularMayerVietoris SingularCohomologyFree SphereHomology IntegralTorsionEvaluation

local instance : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

theorem halfToClosed_attachingSphere :
    (halfToClosed A T).comp (halfBoundaryPair A hA T).attachingSphere =
      (closedBoundaryPair A hA).attachingSphere := by
  ext s
  rfl

theorem halfToClosed_attachingClass :
    singularHomologyMap (halfToClosed A T) 3
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2)) =
    singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3 (unitSphereTopClass 2) := by
  have he := PeriodTorusHigherHomology.singularHomologyMap_comp
    (halfBoundaryPair A hA T).attachingSphere (halfToClosed A T) 3
  rw [halfToClosed_attachingSphere] at he
  exact (LinearMap.congr_fun he (unitSphereTopClass 2)).symm

variable [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)]

theorem relativeMeridianClass_absolute_pullback (s : Sphere 3)
    (γ : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4)
    (hγ : halfToClosedCohomologyPullback A hA T 4 γ = relativeMeridianClass A hA T s) :
    singularCohomologyPullback (halfToClosed A T) 4
      ((HomologicalComplex.homologyMap
        (RelativeIntegralCap.toAbsoluteMap (closedExteriorRange A hA)) 4).hom γ) =
      meridianCohomologyClass A hA T s := by
  have he := RelativeIntegralCap.cohomologyForget_pullback (halfToClosed A T)
    (halfToClosed_mapsTo A hA T) 4 γ
  change (HomologicalComplex.homologyMap
    (RelativeIntegralCap.toAbsoluteMap (halfExteriorRange A hA T)) 4).hom
      (halfToClosedCohomologyPullback A hA T 4 γ) = _ at he
  rw [hγ, relativeMeridianClass_toAbsolute] at he
  exact he.symm

variable [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)]
  [Finite (SingularHomology M 3)]

theorem relativeMeridianClass_torsionEvaluation (s : Sphere 3)
    (γ : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4)
    (hγ : halfToClosedCohomologyPullback A hA T 4 γ = relativeMeridianClass A hA T s)
    (b : SingularHomology (OldPositiveHalf A T) 3) :
    letI : Subsingleton (SingularHomology M 4) :=
      IntegralSevenDuality.fourth_homology_subsingleton (E := Vector 7) M;
    singularTorsionEvaluation M 3
      ((HomologicalComplex.homologyMap
        (RelativeIntegralCap.toAbsoluteMap (closedExteriorRange A hA)) 4).hom γ)
      (singularHomologyMap (halfToClosed A T) 3 b) = meridianCharacter A hA T s b := by
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := Vector 7) M
  have he := singularTorsionEvaluation_naturality (halfToClosed A T)
    ((HomologicalComplex.homologyMap
      (RelativeIntegralCap.toAbsoluteMap (closedExteriorRange A hA)) 4).hom γ) b
  rw [relativeMeridianClass_absolute_pullback A hA T s γ hγ] at he
  exact he.symm.trans (congrArg
    (fun χ : SingularHomology (OldPositiveHalf A T) 3 →+ RationalResidue.Value ↦ χ b)
    (meridianCohomologyClass_evaluation A hA T s))

theorem meridianCharacter_linking_of_relativeClass (s : Sphere 3)
    (γ : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4)
    (hγ : halfToClosedCohomologyPullback A hA T 4 γ = relativeMeridianClass A hA T s)
    (hgen : ∀ c : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4,
      ∃ k : ℤ, k • γ = c) :
    ∃ k : ℤ, IsUnit k ∧ ∀ b : SingularHomology (OldPositiveHalf A T) 3,
      k • IntegralSevenLinking.linking (E := Vector 7) M
        (singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3 (unitSphereTopClass 2))
        (singularHomologyMap (halfToClosed A T) 3 b) = meridianCharacter A hA T s b := by
  obtain ⟨k, hk, hcap⟩ := exteriorGenerator_cap_unit A hA γ hgen
  refine ⟨k, hk, ?_⟩
  intro b
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := Vector 7) M
  have he := IntegralSevenLinking.linking_original_cap (E := Vector 7) M
    ((HomologicalComplex.homologyMap
      (RelativeIntegralCap.toAbsoluteMap (closedExteriorRange A hA)) 4).hom γ)
    (singularHomologyMap (halfToClosed A T) 3 b)
  rw [hcap, map_zsmul, LinearMap.smul_apply] at he
  exact he.trans (relativeMeridianClass_torsionEvaluation A hA T s γ hγ b)

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
