import Wikipedia.HopfProblem.DegreeCollapseRoundedExteriorRepresentative
import Wikipedia.NoExoticSixSphere.UnitSurgeryNormalFraming
import Wikipedia.NoExoticSixSphere.SphereProductFrameCancellation

/-!
# Exact ambient and normal operators on retained exterior spheres

On a representative outside the full rounding tube, the native surgery
embedding is the original embedding with six zero coordinates appended.
Its genuine induced normal frame is already orthonormal, so the frame used
by sphere parity is exactly the original normal frame, five graph axes,
and the negative height column, with the actual normal-model reindexing.
The original quaternionic tangent-frame derivative is retained explicitly.
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
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (hB : B.chart.target ⊆ retainedExterior A)

theorem retained_ambient (s : Sphere 3) : letI := UnitSurgery.targetChartedSpace A hR;
    (UnitSurgery.inducedEmbedding A hR).toFun
      (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB) s) =
      appendZeroMap e.ambientDimension 6 (e.toFun (FramedSurgery.coreMap (E := Vector 4) B s)) := by
  let := UnitSurgery.targetChartedSpace A hR
  change UnitSurgery.ambientMap A hR
    (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB) s) = _
  rw [roundedFace_core, UnitSurgery.ambientMap_exterior, e.heightCylinder_zero]
  rfl

theorem retained_ambient_map : letI := UnitSurgery.targetChartedSpace A hR;
    (UnitSurgery.inducedEmbedding A hR).toFun ∘
      FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB) =
      (appendZeroMap e.ambientDimension 6) ∘ (e.toFun ∘ FramedSurgery.coreMap (E := Vector 4) B) :=
  funext (retained_ambient A hR B hB)

theorem retained_framedDerivative (s : Sphere 3) : letI := UnitSurgery.targetChartedSpace A hR;
    framedDerivative ((UnitSurgery.inducedEmbedding A hR).toFun ∘
      FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB)) s =
      (appendZeroMap e.ambientDimension 6).comp
        (framedDerivative (e.toFun ∘ FramedSurgery.coreMap (E := Vector 4) B) s) := by
  let := UnitSurgery.targetChartedSpace A hR
  change framedDerivative (UnitSurgery.ambientMap A hR ∘
    FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB)) s = _
  have he : UnitSurgery.ambientMap A hR ∘
      FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB) =
      (appendZeroMap e.ambientDimension 6) ∘
        (e.toFun ∘ FramedSurgery.coreMap (E := Vector 4) B) := retained_ambient_map A hR B hB
  rw [he]
  have hg := e.smooth.comp (FramedSurgery.contMDiff_coreMap (E := Vector 4) B)
  rw [framedDerivative_outer_comp_at _ _ s (appendZeroMap e.ambientDimension 6).differentiableAt
    (hg.mdifferentiableAt (by simp)), (appendZeroMap e.ambientDimension 6).fderiv]

theorem retained_normalFrameOnSphere (s : Sphere 3) :
    letI := UnitSurgery.targetChartedSpace A hR;
    ((UnitSurgery.inducedEmbedding A hR).normalFrameOnSphere (UnitSurgery.normalFraming A hR)
      (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB)) s).val =
      (OrthogonalFrameAppend.operator
        (boundaryFrameOperator (a.orthonormal (FramedSurgery.coreMap (E := Vector 4) B s)).val)
        (-heightUnit e.ambientDimension)).comp
          (UnitSurgery.normalModelCoordinates A hR).toContinuousLinearMap := by
  let := UnitSurgery.targetChartedSpace A hR
  change Stiefel.Orthonormalization.operator (UnitSurgery.normalFraming A hR).ambient
    (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB) s) = _
  rw [Stiefel.Orthonormalization.operator_eq_self _ _ (UnitSurgery.normalFraming_norm A hR _),
    UnitSurgery.normalFraming_ambient, roundedFace_core, UnitSurgery.inducedNormalFrame_exterior]
  rfl

theorem retained_sphereFrameOperator (s : Sphere 3) :
    letI := UnitSurgery.targetChartedSpace A hR;
    (UnitSurgery.inducedEmbedding A hR).sphereFrameOperator (UnitSurgery.normalFraming A hR)
      (FramedSurgery.coreMap (E := Vector 4) (roundedFace A hR B hB)) s =
      OperatorSum.operator
        ((OrthogonalFrameAppend.operator
          (boundaryFrameOperator (a.orthonormal (FramedSurgery.coreMap (E := Vector 4) B s)).val)
          (-heightUnit e.ambientDimension)).comp
            (UnitSurgery.normalModelCoordinates A hR).toContinuousLinearMap)
        ((appendZeroMap e.ambientDimension 6).comp
          (framedDerivative (e.toFun ∘ FramedSurgery.coreMap (E := Vector 4) B) s)) := by
  let := UnitSurgery.targetChartedSpace A hR
  change OperatorSum.operator _ _ = _
  rw [retained_normalFrameOnSphere, retained_framedDerivative]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative.NativeRetention
