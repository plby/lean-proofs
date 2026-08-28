import Wikipedia.NoExoticSixSphere.RoundedTraceParametrizedEndFrames

/-! # The original endpoint embedding in its retained original manifold atlas -/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace.OriginalEnd

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem contMDiff_boundaryMap : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (originalEndBoundaryMap A) := by
  let := boundaryChartedSpace A
  exact (_root_.contMDiff_subtype_val (I := 𝓡 6) (U := topBoundaryPart A)).comp
    (contMDiff_originalBoundaryHomeomorph A)

theorem isLocalDiffeomorphAt_boundaryMap (m : M) : letI := boundaryChartedSpace A;
    IsLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞ (originalEndBoundaryMap A) m := by
  let := boundaryChartedSpace A
  exact ((originalBoundaryDiffeomorph A).isLocalDiffeomorph m).comp (𝓡 6) (Boundary A)
    (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 6) (topBoundaryPart A) _)

theorem isClosedEmbedding_boundaryMap : IsClosedEmbedding (originalEndBoundaryMap A) :=
  (isClosed_topBoundaryPart A).isClosedEmbedding_subtypeVal.comp
    (originalBoundaryHomeomorph A).isClosedEmbedding

def ambientMap (m : M) : Vector (e.ambientDimension + 6) := (originalEndBoundaryMap A m).val.val

theorem ambientMap_eq (m : M) : ambientMap A m =
    e.heightCylinder (m, UnroundedTrace.height A) := rfl

theorem contMDiff_ambientMap :
    ContMDiff (𝓡 6) (𝓡 (e.ambientDimension + 6)) ∞ (ambientMap A) := by
  let := boundaryChartedSpace A
  exact (contMDiff_boundaryAmbientInclusion A).comp (contMDiff_boundaryMap A)

def ambientDerivative (m : M) : Vector 6 →L[ℝ] Vector (e.ambientDimension + 6) :=
  mfderiv (𝓡 6) (𝓡 (e.ambientDimension + 6)) (ambientMap A) m

theorem ambientDerivative_eq (m : M) : letI := boundaryChartedSpace A;
    ambientDerivative A m = (boundaryAmbientDerivative A (originalEndBoundaryMap A m)).comp
      (mfderiv (𝓡 6) (𝓡 6) (originalEndBoundaryMap A) m) := by
  let := boundaryChartedSpace A
  exact mfderiv_comp m ((contMDiff_boundaryAmbientInclusion A).mdifferentiableAt (by simp))
    ((contMDiff_boundaryMap A).mdifferentiableAt (by simp))

theorem range_ambientDerivative (m : M) :
    (ambientDerivative A m).range =
      (boundaryAmbientDerivative A (originalEndBoundaryMap A m)).range := by
  let := boundaryChartedSpace A
  rw [ambientDerivative_eq]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    ((isLocalDiffeomorphAt_boundaryMap A m).mfderivToContinuousLinearEquiv (by simp)).surjective)

theorem injective_ambientDerivative (m : M) : Injective (ambientDerivative A m) := by
  let := boundaryChartedSpace A
  rw [ambientDerivative_eq]
  exact (injective_boundaryAmbientDerivative A (originalEndBoundaryMap A m)).comp
    ((isLocalDiffeomorphAt_boundaryMap A m).mfderivToContinuousLinearEquiv (by simp)).injective

def embedding : EuclideanEmbedding 6 M where
  ambientDimension := e.ambientDimension + 6
  toFun := ambientMap A
  smooth := contMDiff_ambientMap A
  closedEmbedding := (isClosedEmbedding_boundaryAmbient A).comp (isClosedEmbedding_boundaryMap A)
  injective_mfderiv := injective_ambientDerivative A

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace.OriginalEnd
