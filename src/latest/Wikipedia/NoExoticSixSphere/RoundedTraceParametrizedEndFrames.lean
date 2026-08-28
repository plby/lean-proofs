import Wikipedia.NoExoticSixSphere.RoundedTraceParametrizedEndCollapse
import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryFrameNormalization
import Wikipedia.NoExoticSixSphere.RoundedTraceOriginalFrameStabilization
import Wikipedia.NoExoticSixSphere.UnitSurgeryInducedFrame

/-!
# Endpoint tube formulas and frame homotopies in the retained parametrizations

The original end uses the original manifold, and the surgery end uses its
independent canonical atlas. Their actual tube frames normalize to the
proved induced frames. At the original end both the last-column reflection
and the fixed stabilization permutation are explicit.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def originalEndBoundaryMap : C(M, Boundary A) :=
  ⟨fun m ↦ (originalBoundaryHomeomorph A m).val,
    continuous_subtype_val.comp (originalBoundaryHomeomorph A).continuous⟩

def originalEndFrameHomotopy :
    ((boundaryVerticalFrameMap A).comp (originalEndBoundaryMap A)).Homotopy
      ((boundaryUnitFrameMap A).comp (originalEndBoundaryMap A)) :=
  (boundaryFrameHomotopy A).comp (ContinuousMap.Homotopy.refl (originalEndBoundaryMap A))

theorem originalEndFrameHomotopy_final (m : M) (v : TimeGraphFrameSpace (e := e)) :
    originalEndFrameHomotopy A (1, m) v = BlockSum.operator 6 (a.orthonormal m).val
      (StabilizedSpanningDisk.endColumnPermutation (e.ambientDimension - 6)
        (boundaryFrameCoordinates (e := e) (boundaryLastReflection (e := e) v))) := by
  let := boundaryChartedSpace A
  have hp : (originalEndBoundaryMap A m).val ∈ topEnd A := (topEndHomeomorph A m).property
  change boundaryFrameFamily A 1 (originalEndBoundaryMap A m) v = _
  rw [boundaryFrameFamily_one, boundaryUnitFrame_top A _ hp]
  change inducedBoundaryFrame A (originalBoundaryDiffeomorph A m).val
    (boundaryFrameCoordinates (e := e) (boundaryLastReflection (e := e) v)) = _
  rw [inducedBoundaryFrame_original_stabilization]
  rfl

theorem SlabTubeData.originalEndTube_apply (D : SlabTubeData A)
    (q : M × TimeGraphFrameSpace (e := e)) :
    D.originalEndTube q = e.heightCylinder (q.1, UnroundedTrace.height A) +
      boundaryVerticalFrame A (originalEndBoundaryMap A q.1)
        (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) D.radius q.2) :=
  D.endTube_apply true (topEndHomeomorph A q.1, q.2)

variable [T2Space M] (hR : A.radius = 2)

def surgeryEndBoundaryMap : C(UnitSurgery.Target A hR, Boundary A) :=
  ⟨UnitSurgery.boundaryPoint A hR, by
    let := boundaryChartedSpace A
    let := UnitSurgery.targetChartedSpace A hR
    exact (UnitSurgery.contMDiff_boundaryPoint A hR).continuous⟩

def surgeryEndFrameHomotopy :
    ((boundaryVerticalFrameMap A).comp (surgeryEndBoundaryMap A hR)).Homotopy
      ((boundaryUnitFrameMap A).comp (surgeryEndBoundaryMap A hR)) :=
  (boundaryFrameHomotopy A).comp (ContinuousMap.Homotopy.refl (surgeryEndBoundaryMap A hR))

theorem surgeryEndFrameHomotopy_final (p : UnitSurgery.Target A hR)
    (v : TimeGraphFrameSpace (e := e)) :
    surgeryEndFrameHomotopy A hR (1, p) v =
      UnitSurgery.inducedNormalFrame A hR p (boundaryFrameCoordinates (e := e) v) := by
  have hp : (surgeryEndBoundaryMap A hR p).val ∈ otherEnd A :=
    (surgeryEndBaseHomeomorph A hR p).property
  change boundaryFrameFamily A 1 (surgeryEndBoundaryMap A hR p) v = _
  rw [boundaryFrameFamily_one, boundaryUnitFrame_other A _ hp]
  rfl

theorem SlabTubeData.surgeryEndTube_apply (D : SlabTubeData A)
    (q : UnitSurgery.Target A hR × TimeGraphFrameSpace (e := e)) :
    D.surgeryEndTube hR q = UnitSurgery.ambientMap A hR q.1 +
      boundaryVerticalFrame A (surgeryEndBoundaryMap A hR q.1)
        (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) D.radius q.2) :=
  D.endTube_apply false (surgeryEndBaseHomeomorph A hR q.1, q.2)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
