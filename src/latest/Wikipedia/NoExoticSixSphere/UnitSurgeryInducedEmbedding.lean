import Wikipedia.NoExoticSixSphere.UnitSurgeryTraceBoundary
import Wikipedia.NoExoticSixSphere.RoundedTraceOriginalFrameStabilization

/-!
# The actual Euclidean embedding of canonical surgery from its boundary comparison

The surgery target retains its independently constructed atlas. Its inclusion
is the actual complementary boundary inclusion composed with the checked
inverse comparison diffeomorphism. The differential has the same range as
the actual native boundary differential.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def boundaryPoint (p : Target A hR) : Boundary A := ((comparisonEquiv A hR).symm p).val

theorem contMDiff_boundaryPoint : letI := boundaryChartedSpace A;
    letI := targetChartedSpace A hR;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (boundaryPoint A hR) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact (_root_.contMDiff_subtype_val (I := 𝓡 6) (U := otherBoundaryPart A)).comp
    (contMDiff_comparisonEquiv_symm A hR)

theorem isLocalDiffeomorphAt_boundaryPoint (p : Target A hR) :
    letI := boundaryChartedSpace A; letI := targetChartedSpace A hR;
    IsLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞ (boundaryPoint A hR) p := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact ((comparisonDiffeomorph A hR).symm.isLocalDiffeomorph p).comp
    (𝓡 6) (Boundary A)
    (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 6) (otherBoundaryPart A) _)

theorem isClosedEmbedding_boundaryPoint : Topology.IsClosedEmbedding (boundaryPoint A hR) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact (isClosed_otherBoundaryPart A).isClosedEmbedding_subtypeVal.comp
    (comparisonDiffeomorph A hR).symm.toHomeomorph.isClosedEmbedding

def ambientMap (p : Target A hR) : Vector (e.ambientDimension + 6) :=
  (boundaryPoint A hR p).val.val

theorem contMDiff_ambientMap : letI := targetChartedSpace A hR;
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞ (ambientMap A hR) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact (contMDiff_boundaryAmbientInclusion A).comp (contMDiff_boundaryPoint A hR)

def ambientDerivative (p : Target A hR) : Vector 6 →L[ℝ] Vector (e.ambientDimension + 6) :=
  letI := targetChartedSpace A hR
  mfderiv (𝓡 6) (𝓡 (e.ambientDimension + 6)) (ambientMap A hR) p

theorem ambientDerivative_eq (p : Target A hR) : letI := boundaryChartedSpace A;
    letI := targetChartedSpace A hR;
    ambientDerivative A hR p = (boundaryAmbientDerivative A (boundaryPoint A hR p)).comp
      (mfderiv (𝓡 6) (𝓡 6) (boundaryPoint A hR) p) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  exact mfderiv_comp p ((contMDiff_boundaryAmbientInclusion A).mdifferentiableAt (by simp))
    ((contMDiff_boundaryPoint A hR).mdifferentiableAt (by simp))

theorem range_ambientDerivative (p : Target A hR) :
    (ambientDerivative A hR p).range =
      (boundaryAmbientDerivative A (boundaryPoint A hR p)).range := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  rw [ambientDerivative_eq]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    ((isLocalDiffeomorphAt_boundaryPoint A hR p).mfderivToContinuousLinearEquiv
      (by simp)).surjective)

theorem injective_ambientDerivative (p : Target A hR) : Injective (ambientDerivative A hR p) := by
  let := boundaryChartedSpace A
  let := targetChartedSpace A hR
  rw [ambientDerivative_eq]
  exact (injective_boundaryAmbientDerivative A (boundaryPoint A hR p)).comp
    ((isLocalDiffeomorphAt_boundaryPoint A hR p).mfderivToContinuousLinearEquiv (by simp)).injective

def inducedEmbedding : letI := targetChartedSpace A hR; EuclideanEmbedding 6 (Target A hR) := by
  let := targetChartedSpace A hR
  exact
    { ambientDimension := e.ambientDimension + 6
      toFun := ambientMap A hR
      smooth := contMDiff_ambientMap A hR
      closedEmbedding := (isClosedEmbedding_boundaryAmbient A).comp
        (isClosedEmbedding_boundaryPoint A hR)
      injective_mfderiv := injective_ambientDerivative A hR }

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
