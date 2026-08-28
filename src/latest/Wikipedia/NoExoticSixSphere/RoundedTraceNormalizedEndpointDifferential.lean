import Wikipedia.NoExoticSixSphere.RoundedTraceEndpointCollapseNormalization
import Wikipedia.NoExoticSixSphere.RadialCompressionLinearCoordinates

/-!
# The actual fiber derivatives of the normalized endpoint tubes

Every time has exactly the interpolated frame, multiplied by the positive
tube radius. At the final time this is the signed unit frame. The original
end retains both the last-coordinate reflection and the fixed permutation.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem hasFDerivAt_normalizedEndpointTube_fiber
    {N : Type*} [TopologicalSpace N] (b : C(N, Boundary A))
    (τ : N × TimeGraphFrameSpace (e := e) → Vector (e.ambientDimension + 6))
    (j : N → Vector (e.ambientDimension + 6)) (r : ℝ) (hr : 0 < r)
    (hτ : ∀ q, τ q = j q.1 + boundaryVerticalFrame A (b q.1)
      (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) r q.2))
    (t : I) (p : N) :
    HasFDerivAt (fun v ↦ normalizedEndpointTube A b τ t (p, v))
      (r • boundaryFrameHomotopy A (t, b p)) 0 := by
  have hf : (fun v ↦ normalizedEndpointTube A b τ t (p, v)) =
      (fun v ↦ j p + boundaryVerticalFrame A (b p)
        (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) r
          (boundaryFiberCoordinates A (t, b p) v))) :=
    funext (fun v ↦ hτ (p, boundaryFiberCoordinates A (t, b p) v))
  have hB : (boundaryVerticalFrame A (b p)).comp
      (boundaryFiberCoordinates A (t, b p)).toContinuousLinearMap =
        boundaryFrameHomotopy A (t, b p) := by
    apply ContinuousLinearMap.ext
    intro v
    exact boundaryVerticalFrame_fiberCoordinates A t (b p) v
  rw [hf]
  have hd := hasFDerivAt_framedCompression_linearCoordinates (j p)
    (boundaryVerticalFrame A (b p)) (boundaryFiberCoordinates A (t, b p)).toContinuousLinearMap r hr
  rw [hB] at hd
  convert hd using 1 <;> rfl

namespace SlabTubeData

variable {A} (D : SlabTubeData A)

theorem hasFDerivAt_normalizedOriginalEndTube_fiber (t : I) (m : M) :
    HasFDerivAt (fun v ↦
      normalizedEndpointTube A (originalEndBoundaryMap A) D.originalEndTube t (m, v))
        (D.radius • originalEndFrameHomotopy A (t, m)) 0 :=
  hasFDerivAt_normalizedEndpointTube_fiber A (originalEndBoundaryMap A) D.originalEndTube
    (fun p ↦ e.heightCylinder (p, UnroundedTrace.height A)) D.radius D.radius_pos
      (originalEndTube_apply A D) t m

theorem fderiv_normalizedOriginalEndTube_final (m : M) (v : TimeGraphFrameSpace (e := e)) :
    fderiv ℝ (fun w ↦
      normalizedEndpointTube A (originalEndBoundaryMap A) D.originalEndTube 1 (m, w)) 0 v =
        D.radius • BlockSum.operator 6 (a.orthonormal m).val
          (StabilizedSpanningDisk.endColumnPermutation (e.ambientDimension - 6)
            (boundaryFrameCoordinates (e := e) (boundaryLastReflection (e := e) v))) := by
  rw [(D.hasFDerivAt_normalizedOriginalEndTube_fiber 1 m).fderiv]
  change D.radius • originalEndFrameHomotopy A (1, m) v = _
  rw [originalEndFrameHomotopy_final]

variable [T2Space M] (hR : A.radius = 2)

theorem hasFDerivAt_normalizedSurgeryEndTube_fiber (t : I) (p : UnitSurgery.Target A hR) :
    HasFDerivAt (fun v ↦ normalizedEndpointTube A (surgeryEndBoundaryMap A hR)
      (D.surgeryEndTube hR) t (p, v)) (D.radius • surgeryEndFrameHomotopy A hR (t, p)) 0 :=
  hasFDerivAt_normalizedEndpointTube_fiber A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
    (UnitSurgery.ambientMap A hR) D.radius D.radius_pos (surgeryEndTube_apply A hR D) t p

theorem fderiv_normalizedSurgeryEndTube_final (p : UnitSurgery.Target A hR)
    (v : TimeGraphFrameSpace (e := e)) :
    fderiv ℝ (fun w ↦ normalizedEndpointTube A (surgeryEndBoundaryMap A hR)
      (D.surgeryEndTube hR) 1 (p, w)) 0 v = D.radius •
        UnitSurgery.inducedNormalFrame A hR p (boundaryFrameCoordinates (e := e) v) := by
  rw [(D.hasFDerivAt_normalizedSurgeryEndTube_fiber hR 1 p).fderiv]
  change D.radius • surgeryEndFrameHomotopy A hR (1, p) v = _
  rw [surgeryEndFrameHomotopy_final]

end SlabTubeData

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
