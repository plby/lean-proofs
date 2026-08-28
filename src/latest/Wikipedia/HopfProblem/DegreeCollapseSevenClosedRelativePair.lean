import Wikipedia.HopfProblem.DegreeCollapseSevenRelativeGroups
import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeEvaluationComparison

/-!
# The original half-to-closed pair maps for a framed seven-dimensional attachment

These are the actual inclusion-induced maps on relative homology and
cohomology. Their evaluation square is the original cochain evaluation.
The proved vanishing of the half's relative H3 transfers to the closed pair
and gives a cohomology isomorphism from the corresponding homology maps.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
namespace FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization FirstHurewicz
open SingularMayerVietoris SingularCohomologyFree

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

abbrev closedExteriorRange : Set M := range (closedBoundaryPair A hA).oldExterior

def halfToClosed : C(OldPositiveHalf A T, M) := ⟨Subtype.val, continuous_subtype_val⟩

theorem halfToClosed_mapsTo :
    MapsTo (halfToClosed A T) (halfExteriorRange A hA T) (closedExteriorRange A hA) := by
  rintro x ⟨r, rfl⟩
  exact ⟨r.val, rfl⟩

abbrev halfToClosedPairMap (k : ℕ) :
    RelativeSingularHomology.Homology (halfExteriorRange A hA T) k →ₗ[ℤ]
      RelativeSingularHomology.Homology (closedExteriorRange A hA) k :=
  RelativeSingularHomology.map (halfToClosed A T) (halfToClosed_mapsTo A hA T) k

abbrev halfToClosedCohomologyPullback (k : ℕ) :
    RelativeIntegralCap.Cohomology (closedExteriorRange A hA) k →ₗ[ℤ]
      RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) k :=
  RelativeIntegralCap.cohomologyPullback (halfToClosed A T) (halfToClosed_mapsTo A hA T) k

theorem halfToClosed_evaluation (k : ℕ)
    (c : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) k)
    (z : RelativeSingularHomology.Homology (halfExteriorRange A hA T) k) :
    cohomologyEvaluation (RelativeSingularHomology.complex (halfExteriorRange A hA T)) k
      (halfToClosedCohomologyPullback A hA T k c) z =
    cohomologyEvaluation (RelativeSingularHomology.complex (closedExteriorRange A hA)) k c
      (halfToClosedPairMap A hA T k z) :=
  cohomologyEvaluation_naturality
    (RelativeSingularHomology.mapChain (halfToClosed A T) (halfToClosed_mapsTo A hA T)) k c z

theorem closed_relative_third_homology_subsingleton
    (h3 : Surjective (halfToClosedPairMap A hA T 3)) :
    Subsingleton (RelativeSingularHomology.Homology (closedExteriorRange A hA) 3) := by
  let := relative_third_homology_subsingleton A hA T
  exact h3.subsingleton

theorem halfToClosedCohomologyPullback_bijective
    (h3 : Surjective (halfToClosedPairMap A hA T 3))
    (h4 : Bijective (halfToClosedPairMap A hA T 4)) :
    Bijective (halfToClosedCohomologyPullback A hA T 4) := by
  let := relative_third_homology_subsingleton A hA T
  exact RelativeIntegralCap.cohomologyPullback_succ_bijective
    (halfToClosed A T) (halfToClosed_mapsTo A hA T) 3 h3 h4

def extendRelativeClass (h : Bijective (halfToClosedCohomologyPullback A hA T 4))
    (c : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4) :
    RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4 :=
  (LinearEquiv.ofBijective (halfToClosedCohomologyPullback A hA T 4) h).symm c

theorem extendRelativeClass_pullback (h : Bijective (halfToClosedCohomologyPullback A hA T 4))
    (c : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4) :
    halfToClosedCohomologyPullback A hA T 4 (extendRelativeClass A hA T h c) = c :=
  (LinearEquiv.ofBijective (halfToClosedCohomologyPullback A hA T 4) h).apply_symm_apply c

theorem extendRelativeClass_evaluation (h : Bijective (halfToClosedCohomologyPullback A hA T 4))
    (c : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4)
    (z : RelativeSingularHomology.Homology (halfExteriorRange A hA T) 4) :
    cohomologyEvaluation (RelativeSingularHomology.complex (closedExteriorRange A hA)) 4
      (extendRelativeClass A hA T h c) (halfToClosedPairMap A hA T 4 z) =
    cohomologyEvaluation (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4 c z := by
  rw [← halfToClosed_evaluation, extendRelativeClass_pullback]

theorem extendRelativeClass_evaluation_bijective
    (h : Bijective (halfToClosedCohomologyPullback A hA T 4))
    (h4 : Bijective (halfToClosedPairMap A hA T 4))
    (c : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4)
    (hc : Bijective
      (cohomologyEvaluation (RelativeSingularHomology.complex (halfExteriorRange A hA T)) 4 c)) :
    Bijective (cohomologyEvaluation
      (RelativeSingularHomology.complex (closedExteriorRange A hA)) 4
        (extendRelativeClass A hA T h c)) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := h4.2 x
    obtain ⟨b, rfl⟩ := h4.2 y
    rw [extendRelativeClass_evaluation, extendRelativeClass_evaluation] at hxy
    exact congrArg (halfToClosedPairMap A hA T 4) (hc.1 hxy)
  · intro k
    obtain ⟨z, hz⟩ := hc.2 k
    exact ⟨halfToClosedPairMap A hA T 4 z,
      (extendRelativeClass_evaluation A hA T h c z).trans hz⟩

theorem extendRelativeClass_generates (h : Bijective (halfToClosedCohomologyPullback A hA T 4))
    (c : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4)
    (hc : ∀ b : RelativeIntegralCap.Cohomology (halfExteriorRange A hA T) 4,
      ∃ k : ℤ, k • c = b)
    (b : RelativeIntegralCap.Cohomology (closedExteriorRange A hA) 4) :
    ∃ k : ℤ, k • extendRelativeClass A hA T h c = b := by
  obtain ⟨k, hk⟩ := hc (halfToClosedCohomologyPullback A hA T 4 b)
  refine ⟨k, h.1 ?_⟩
  rw [map_zsmul, extendRelativeClass_pullback]
  exact hk

end FramedAttachingProduct.UnitSurgery.ExteriorTwist
end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
