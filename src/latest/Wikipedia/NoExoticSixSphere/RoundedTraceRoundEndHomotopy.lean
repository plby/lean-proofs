import Wikipedia.NoExoticSixSphere.RoundedTraceRoundEndpointCollapse

/-!
# The trace compares actual round framed collapses at its two ends

The radius at each end is chosen internally from compactness. The final
original frame retains its last-column reflection and stabilization
permutation; the surgery frame is the canonical induced frame in its
independently constructed atlas.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  {A : FramedAttachingProduct e a f}

namespace SlabTubeData

variable (D : SlabTubeData A)

def originalRoundRadius : ℝ := D.radius * endpointRoundScale A (originalEndBoundaryMap A)

theorem originalRoundRadius_pos : 0 < D.originalRoundRadius :=
  mul_pos D.radius_pos (endpointRoundScale_pos A (originalEndBoundaryMap A))

def roundOriginalEndTube := roundEndpointTube A (originalEndBoundaryMap A) D.originalEndTube

theorem isOpenEmbedding_roundOriginalEndTube : IsOpenEmbedding D.roundOriginalEndTube :=
  isOpenEmbedding_roundEndpointTube A (originalEndBoundaryMap A) D.originalEndTube
    D.isOpenEmbedding_originalEndTube

theorem roundOriginalEndTube_apply (q : M × TimeGraphFrameSpace (e := e)) :
    D.roundOriginalEndTube q = e.heightCylinder (q.1, UnroundedTrace.height A) +
      BlockSum.operator 6 (a.orthonormal q.1).val
        (StabilizedSpanningDisk.endColumnPermutation (e.ambientDimension - 6)
          (boundaryFrameCoordinates (e := e) (boundaryLastReflection (e := e)
            (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
              D.originalRoundRadius q.2)))) := by
  let v := OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
    D.originalRoundRadius q.2
  have hB := originalEndFrameHomotopy_final A q.1 v
  change boundaryFrameFamily A 1 (originalEndBoundaryMap A q.1) v = _ at hB
  rw [boundaryFrameFamily_one] at hB
  exact (roundEndpointTube_formula A (originalEndBoundaryMap A) D.originalEndTube
    (fun m ↦ e.heightCylinder (m, UnroundedTrace.height A)) D.radius D.radius_pos
      (originalEndTube_apply A D) q).trans
        (congrArg (fun w ↦ e.heightCylinder (q.1, UnroundedTrace.height A) + w) hB)

variable [T2Space M] (hR : A.radius = 2)

def surgeryRoundRadius : ℝ :=
  letI := UnitSurgery.compactSpace_target A hR
  D.radius * endpointRoundScale A (surgeryEndBoundaryMap A hR)

theorem surgeryRoundRadius_pos : 0 < D.surgeryRoundRadius hR := by
  let := UnitSurgery.compactSpace_target A hR
  exact mul_pos D.radius_pos (endpointRoundScale_pos A (surgeryEndBoundaryMap A hR))

def roundSurgeryEndTube :=
  letI := UnitSurgery.compactSpace_target A hR
  roundEndpointTube A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)

theorem isOpenEmbedding_roundSurgeryEndTube : IsOpenEmbedding (D.roundSurgeryEndTube hR) := by
  let := UnitSurgery.compactSpace_target A hR
  exact isOpenEmbedding_roundEndpointTube A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
    (D.isOpenEmbedding_surgeryEndTube hR)

theorem roundSurgeryEndTube_apply (q : UnitSurgery.Target A hR × TimeGraphFrameSpace (e := e)) :
    D.roundSurgeryEndTube hR q = UnitSurgery.ambientMap A hR q.1 +
      UnitSurgery.inducedNormalFrame A hR q.1 (boundaryFrameCoordinates (e := e)
        (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
          (D.surgeryRoundRadius hR) q.2)) := by
  let := UnitSurgery.compactSpace_target A hR
  let v := OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
    (D.surgeryRoundRadius hR) q.2
  have hB := surgeryEndFrameHomotopy_final A hR q.1 v
  change boundaryFrameFamily A 1 (surgeryEndBoundaryMap A hR q.1) v = _ at hB
  rw [boundaryFrameFamily_one] at hB
  exact (roundEndpointTube_formula A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
    (UnitSurgery.ambientMap A hR) D.radius D.radius_pos (surgeryEndTube_apply A hR D) q).trans
      (congrArg (fun w ↦ UnitSurgery.ambientMap A hR q.1 + w) hB)

def roundEndCollapseHomotopy : letI := UnitSurgery.compactSpace_target A hR;
    (roundEndpointCollapse A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
      (D.isOpenEmbedding_surgeryEndTube hR)).Homotopy
        (roundEndpointCollapse A (originalEndBoundaryMap A) D.originalEndTube
          D.isOpenEmbedding_originalEndTube) :=
  (endpointRoundingHomotopy A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
    (D.isOpenEmbedding_surgeryEndTube hR)).symm.trans
      ((D.normalizedEndCollapseHomotopy hR).trans
        (endpointRoundingHomotopy A (originalEndBoundaryMap A) D.originalEndTube
          D.isOpenEmbedding_originalEndTube))

theorem roundEndCollapseHomotopy_infty (t : I) :
    D.roundEndCollapseHomotopy hR (t, OnePoint.infty) = OnePoint.infty := by
  let := UnitSurgery.compactSpace_target A hR
  rw [roundEndCollapseHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · rw [ContinuousMap.Homotopy.symm_apply, endpointRoundingHomotopy_infty]
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact D.normalizedEndCollapseHomotopy_infty hR _
    · exact endpointRoundingHomotopy_infty A (originalEndBoundaryMap A) D.originalEndTube
        D.isOpenEmbedding_originalEndTube _

theorem roundEndCollapseHomotopy_zero (z : OnePoint (Vector (e.ambientDimension + 6))) :
    D.roundEndCollapseHomotopy hR (0, z) =
      OpenFiberCollapse.collapseOnePoint (D.roundSurgeryEndTube hR) z := by
  let := UnitSurgery.compactSpace_target A hR
  exact (D.roundEndCollapseHomotopy hR).map_zero_left z |>.trans
    (roundEndpointCollapse_apply A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
      (D.isOpenEmbedding_surgeryEndTube hR) z)

theorem roundEndCollapseHomotopy_one (z : OnePoint (Vector (e.ambientDimension + 6))) :
    D.roundEndCollapseHomotopy hR (1, z) =
      OpenFiberCollapse.collapseOnePoint D.roundOriginalEndTube z := by
  let := UnitSurgery.compactSpace_target A hR
  exact (D.roundEndCollapseHomotopy hR).map_one_left z |>.trans
    (roundEndpointCollapse_apply A (originalEndBoundaryMap A) D.originalEndTube
      D.isOpenEmbedding_originalEndTube z)

end SlabTubeData

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
