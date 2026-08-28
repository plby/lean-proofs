import Wikipedia.HopfProblem.DegreeCollapseRetainedExteriorFrames
import Wikipedia.HopfProblem.DegreeCollapseStabilizedFrameSum

/-!
# The retained native sphere frame is an actual constant recoordination of a block

Compose the actual normal-model reindexing, the negative height reflection,
and the fixed normal/tangent column permutation. The resulting constant
source equivalence identifies the complete native sphere-frame operator
with the original operator stabilized by six identity columns.
No claim about the separate source-dependent twist is used here.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open StabilizedSpanningDisk SphereThreeTangentFrame Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def normalCoordinates : Vector ((e.ambientDimension + 6) - 6) ≃L[ℝ]
    Vector ((e.ambientDimension - 6) + 6) := by
  let := UnitSurgery.targetChartedSpace A hR
  exact (UnitSurgery.normalModelCoordinates A hR).toContinuousLinearEquiv.trans
    (FrameStabilization.negativeEndCoordinates (e.ambientDimension - 6))

def frameSourceCoordinates : Vector (((e.ambientDimension + 6) - 6) + 3) ≃L[ℝ]
    Vector (((e.ambientDimension - 6) + 3) + 6) :=
  FrameStabilization.sourceCoordinates (k := e.ambientDimension - 6) (n := 3) (m := 6)
    (normalCoordinates A hR)

theorem normalCoordinates_apply (w : Vector ((e.ambientDimension + 6) - 6)) :
    letI := UnitSurgery.targetChartedSpace A hR;
    normalCoordinates A hR w = FrameStabilization.negativeEndCoordinates
      (e.ambientDimension - 6) (UnitSurgery.normalModelCoordinates A hR w) := rfl

theorem normalCoordinates_clm : letI := UnitSurgery.targetChartedSpace A hR;
    (normalCoordinates A hR).toContinuousLinearMap =
      (FrameStabilization.negativeEndCoordinates (e.ambientDimension - 6)).toContinuousLinearMap.comp
        (UnitSurgery.normalModelCoordinates A hR).toContinuousLinearMap := by
  let := UnitSurgery.targetChartedSpace A hR
  exact FrameStabilization.isometry_trans_clm (UnitSurgery.normalModelCoordinates A hR)
    (FrameStabilization.negativeEndCoordinates (e.ambientDimension - 6))

variable (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (hB : B.chart.target ⊆ retainedExterior A)

theorem retained_normal_block (s : Sphere 3) : letI := UnitSurgery.targetChartedSpace A hR;
    ((UnitSurgery.inducedEmbedding A hR).normalFrameOnSphere (UnitSurgery.normalFraming A hR)
      (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB)) s).val =
      (Stiefel.BlockSum.operator 6
        (a.orthonormal (FramedSurgery.coreMap (E := Vector 4) B s)).val).comp
          (normalCoordinates A hR).toContinuousLinearMap := by
  let := UnitSurgery.targetChartedSpace A hR
  rw [retained_normalFrameOnSphere, FrameStabilization.append_negative_height_eq_block]
  rw [normalCoordinates_clm, ContinuousLinearMap.comp_assoc]
  rfl

theorem retained_frame_block (s : Sphere 3) : letI := UnitSurgery.targetChartedSpace A hR;
    (UnitSurgery.inducedEmbedding A hR).sphereFrameOperator (UnitSurgery.normalFraming A hR)
      (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB)) s =
      (Stiefel.BlockSum.operator 6
        (e.sphereFrameOperator a (FramedSurgery.coreMap (E := Vector 4) B) s)).comp
          (frameSourceCoordinates A hR).toContinuousLinearMap := by
  let := UnitSurgery.targetChartedSpace A hR
  change OperatorSum.operator _ _ = _
  rw [retained_normal_block, retained_framedDerivative]
  exact FrameStabilization.operatorSum_stabilized_recoordinate
    (a.orthonormal (FramedSurgery.coreMap (E := Vector 4) B s)).val
    (framedDerivative (e.toFun ∘ FramedSurgery.coreMap (E := Vector 4) B) s)
    (normalCoordinates A hR)

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention
