import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryPositiveBoundary
import Wikipedia.NoExoticSixSphere.SuperlevelDifferential

/-!
# The native surgery half has an actual smooth Euclidean embedding

Restrict the constructed surgery embedding to the compact positive half.
The superlevel inclusion has a bijective full tangent map, including at
boundary points, so the half has exactly the same ambient tangent image.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

def halfAmbientMap (p : PositiveHalf A hR T) : Vector (e.ambientDimension + 6) :=
  ambientMap A hR p.val

theorem contMDiff_positiveHalfInclusion : letI := targetChartedSpace A hR;
    letI := positiveHalfChartedSpace A hR T;
    ContMDiff (ProductHalfSpace.model (Vector 6)) (𝓡 7) ∞
      (Subtype.val : PositiveHalf A hR T → Target A hR) := by
  let := targetChartedSpace A hR
  exact (positiveHalfAtlas A hR T).contMDiff_subtype_val

theorem bijective_mfderiv_positiveHalfInclusion (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR; letI := positiveHalfChartedSpace A hR T;
    Bijective (mfderiv (ProductHalfSpace.model (Vector 6)) (𝓡 7)
      (Subtype.val : PositiveHalf A hR T → Target A hR) p) := by
  let := targetChartedSpace A hR
  exact (positiveHalfAtlas A hR T).bijective_mfderiv_subtype_val p

theorem contMDiff_halfAmbientMap : letI := targetChartedSpace A hR;
    letI := positiveHalfChartedSpace A hR T;
    ContMDiff (ProductHalfSpace.model (Vector 6)) (𝓡 (e.ambientDimension + 6)) ∞
      (halfAmbientMap A hR T) := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  exact (contMDiff_ambientMap A hR).comp (contMDiff_positiveHalfInclusion A hR T)

theorem isClosedEmbedding_halfAmbientMap : IsClosedEmbedding (halfAmbientMap A hR T) := by
  let := targetChartedSpace A hR
  have hc : IsClosed {p : Target A hR | 0 ≤ timeFunction A hR T p} :=
    isClosed_le continuous_const (contMDiff_timeFunction A hR T).continuous
  exact (inducedEmbedding A hR).closedEmbedding.comp hc.isClosedEmbedding_subtypeVal

def halfAmbientDerivative (p : PositiveHalf A hR T) :
    (ℝ × Vector 6) →L[ℝ] Vector (e.ambientDimension + 6) :=
  letI := targetChartedSpace A hR
  letI := positiveHalfChartedSpace A hR T
  mfderiv (ProductHalfSpace.model (Vector 6)) (𝓡 (e.ambientDimension + 6))
    (halfAmbientMap A hR T) p

theorem halfAmbientDerivative_eq (p : PositiveHalf A hR T) :
    letI := targetChartedSpace A hR; letI := positiveHalfChartedSpace A hR T;
    halfAmbientDerivative A hR T p = (ambientDerivative A hR p.val).comp
      (mfderiv (ProductHalfSpace.model (Vector 6)) (𝓡 7)
        (Subtype.val : PositiveHalf A hR T → Target A hR) p) := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  exact mfderiv_comp p ((contMDiff_ambientMap A hR).mdifferentiableAt (by simp))
    ((contMDiff_positiveHalfInclusion A hR T).mdifferentiableAt (by simp))

theorem injective_halfAmbientDerivative (p : PositiveHalf A hR T) :
    Injective (halfAmbientDerivative A hR T p) := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  rw [halfAmbientDerivative_eq]
  exact (injective_ambientDerivative A hR p.val).comp
    (bijective_mfderiv_positiveHalfInclusion A hR T p).injective

theorem range_halfAmbientDerivative (p : PositiveHalf A hR T) :
    (halfAmbientDerivative A hR T p).range = (ambientDerivative A hR p.val).range := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  rw [halfAmbientDerivative_eq]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    (bijective_mfderiv_positiveHalfInclusion A hR T p).surjective)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
