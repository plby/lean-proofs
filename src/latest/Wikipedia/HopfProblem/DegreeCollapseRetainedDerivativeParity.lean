import Wikipedia.HopfProblem.DegreeCollapseRetainedFrameStabilization
import Wikipedia.NoExoticSixSphere.ImmersedSphereDerivativeParity

/-!
# Retention preserves the actual untwisted derivative-frame obstruction

The full native retained frame is the original frame with six identity
columns, followed by a constructed constant source equivalence. The exact
operator-extension criterion is invariant under that coordinate change
and reflects block stabilization. Hence the genuine derivative parity is
preserved. This is not yet the source-twisted geometric disk parity.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open Stiefel DiskBoundary Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (hB : B.chart.target ⊆ retainedExterior A)

def originalFrame : C(Sphere 3, Monomorphism.Space e.ambientDimension
    ((e.ambientDimension - 6) + 3)) :=
  e.sphereFrameOperatorMap a (FramedSurgery.coreMap (E := Vector 4) B)
    (FramedSurgery.contMDiff_coreMap (E := Vector 4) B) (FramedCore.injective_core_derivative B)

def nativeFrame : C(Sphere 3, Monomorphism.Space (e.ambientDimension + 6)
    (((e.ambientDimension + 6) - 6) + 3)) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  exact (UnitSurgery.inducedEmbedding A hR).sphereFrameOperatorMap (UnitSurgery.normalFraming A hR)
    (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB))
    (FramedSurgery.contMDiff_coreMap (E := Vector 4) (roundedFace A hR B hB))
    (FramedCore.injective_core_derivative (roundedFace A hR B hB))

theorem nativeFrame_recoordinate (s : Sphere 3) :
    nativeFrame A hR B hB s = Monomorphism.recoordinate
      (ContinuousLinearEquiv.refl ℝ (Vector (e.ambientDimension + 6)))
      (frameSourceCoordinates A hR) (Monomorphism.blockMap 6 (originalFrame (a := a) B s)) := by
  let := UnitSurgery.targetChartedSpace A hR
  apply Subtype.ext
  change (UnitSurgery.inducedEmbedding A hR).sphereFrameOperator (UnitSurgery.normalFraming A hR)
      (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB)) s =
    (BlockSum.operator 6 (e.sphereFrameOperator a (FramedSurgery.coreMap (E := Vector 4) B) s)).comp
      (frameSourceCoordinates A hR).toContinuousLinearMap
  exact retained_frame_block A hR B hB s

theorem nativeFrame_extends_iff : Extends (nativeFrame A hR B hB) ↔
    Extends (originalFrame (a := a) B) := by
  have hcoords := Monomorphism.extends_recoordinate_iff
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector (e.ambientDimension + 6)))
    (fun _ ↦ frameSourceCoordinates A hR)
    continuous_const continuous_const continuous_const continuous_const
    ((Monomorphism.blockMap 6).comp (originalFrame (a := a) B))
    (nativeFrame A hR B hB) (nativeFrame_recoordinate A hR B hB)
  refine hcoords.trans (Monomorphism.extends_blockMap_iff (by omega) ?_ 6 _)
  have hdim := e.dimension_le_ambient (FramedSurgery.coreMap (E := Vector 4) B (pole 3))
  omega

theorem retained_derivativeParity : letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    (UnitSurgery.inducedEmbedding A hR).sphereDerivativeParity (UnitSurgery.normalFraming A hR)
      (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB))
      (FramedSurgery.contMDiff_coreMap (E := Vector 4) (roundedFace A hR B hB))
      (FramedCore.injective_core_derivative (roundedFace A hR B hB)) =
    e.sphereDerivativeParity a (FramedSurgery.coreMap (E := Vector 4) B)
      (FramedSurgery.contMDiff_coreMap (E := Vector 4) B) (FramedCore.injective_core_derivative B) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  apply zmodTwo_eq_of_zero_iff
  unfold EuclideanEmbedding.sphereDerivativeParity
  rw [Monomorphism.sphereParityOfDimension_zero_iff, Monomorphism.sphereParityOfDimension_zero_iff]
  exact nativeFrame_extends_iff A hR B hB

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention
