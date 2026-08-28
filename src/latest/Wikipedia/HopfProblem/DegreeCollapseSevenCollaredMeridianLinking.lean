import Wikipedia.HopfProblem.DegreeCollapseSevenCollaredRelativeComparison
import Wikipedia.HopfProblem.DegreeCollapseSevenMeridianLinking

/-!
# The original meridian character equals the closed linking value for a collared half

The actual relative pullback is already proved bijective. Extend the
original normalized meridian class through it and retain its generation
property. The original local core cap theorem then gives one integer
unit relating the original meridian character to the closed pairing on
every half class. No relative-class or comparison hypothesis is supplied.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris SphereHomology

local instance : Fact (Module.finrank ℝ (Vector 7) = 7) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)
  {B : Type} [TopologicalSpace B] (C : TimeCollar T.time B)
  [Subsingleton (SingularHomology (OldPositiveHalf A T) 4)]
  [Finite (SingularHomology (OldPositiveHalf A T) 3)]

def collaredClosedMeridianClass (s : Sphere 3) :
    RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4 :=
  extendRelativeClass A hA T (collaredHalfToClosedCohomologyPullback_bijective A hA T C)
    (relativeMeridianClass A hA T s)

theorem collaredClosedMeridianClass_pullback (s : Sphere 3) :
    halfToClosedCohomologyPullback A hA T 4 (collaredClosedMeridianClass A hA T C s) =
      relativeMeridianClass A hA T s :=
  extendRelativeClass_pullback A hA T
    (collaredHalfToClosedCohomologyPullback_bijective A hA T C) (relativeMeridianClass A hA T s)

theorem collaredClosedMeridianClass_generates (s : Sphere 3)
    (c : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4) :
    ∃ k : ℤ, k • collaredClosedMeridianClass A hA T C s = c :=
  extendRelativeClass_generates A hA T
    (collaredHalfToClosedCohomologyPullback_bijective A hA T C)
    (relativeMeridianClass A hA T s) (relativeMeridianClass_generates A hA T s) c

variable [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)]
  [Finite (SingularHomology M 3)]

include C in
theorem collaredMeridianCharacter_linking (s : Sphere 3) :
    ∃ k : ℤ, IsUnit k ∧ ∀ b : SingularHomology (OldPositiveHalf A T) 3,
      k • IntegralSevenLinking.linking (E := Vector 7) M
        (singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3 (unitSphereTopClass 2))
        (singularHomologyMap (halfToClosed A T) 3 b) = meridianCharacter A hA T s b :=
  meridianCharacter_linking_of_relativeClass A hA T s (collaredClosedMeridianClass A hA T C s)
    (collaredClosedMeridianClass_pullback A hA T C s)
    (collaredClosedMeridianClass_generates A hA T C s)

include C in
theorem collaredMeridianCharacter_core_ne_zero_iff (s : Sphere 3) :
    meridianCharacter A hA T s
      (singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2)) ≠ 0 ↔
    IntegralSevenLinking.linking (E := Vector 7) M
      (singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3 (unitSphereTopClass 2))
      (singularHomologyMap (closedBoundaryPair A hA).attachingSphere 3 (unitSphereTopClass 2)) ≠ 0 := by
  obtain ⟨k, hk, he⟩ := collaredMeridianCharacter_linking A hA T C s
  have hb := he (singularHomologyMap
    (halfBoundaryPair A hA T).attachingSphere 3 (unitSphereTopClass 2))
  rw [halfToClosed_attachingClass] at hb
  rw [← hb]
  rcases Int.isUnit_iff.mp hk with rfl | rfl
  · simp only [one_smul]
  · simp only [neg_one_smul, neg_ne_zero]

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
