import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryFiberCoordinates
import Wikipedia.NoExoticSixSphere.RoundedTraceParametrizedEndFrames
import Wikipedia.NoExoticSixSphere.FiberCoordinateCollapse

/-!
# Actual based collapse homotopies for the endpoint frame normalization

Pull the explicit fiber-coordinate changes back to the retained endpoint
parametrizations. They reparametrize the actual open tubes and produce
based collapse homotopies starting at the exact trace collapse endpoints.
These tubes retain the original radial compression, precomposed with the
fiber change; equality with a separately chosen round unit-frame tube is not claimed.
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

section Endpoint

variable {N : Type*} [TopologicalSpace N] (b : C(N, Boundary A))

def endpointFiberCoordinates (q : I × N) :
    TimeGraphFrameSpace (e := e) ≃ₜ TimeGraphFrameSpace (e := e) :=
  (boundaryFiberCoordinates A (q.1, b q.2)).toHomeomorph

theorem continuous_endpointFiberCoordinates :
    Continuous (fun q : (I × N) × TimeGraphFrameSpace (e := e) ↦
      endpointFiberCoordinates A b q.1 q.2) := by
  let F : C((I × Boundary A) × TimeGraphFrameSpace (e := e), TimeGraphFrameSpace (e := e)) :=
    ⟨fun q ↦ boundaryFiberCoordinates A q.1 q.2, continuous_boundaryFiberCoordinates A⟩
  exact (F.comp (((ContinuousMap.id I).prodMap b).prodMap (ContinuousMap.id _))).continuous

theorem continuous_endpointFiberCoordinates_symm :
    Continuous (fun q : (I × N) × TimeGraphFrameSpace (e := e) ↦
      (endpointFiberCoordinates A b q.1).symm q.2) := by
  let F : C((I × Boundary A) × TimeGraphFrameSpace (e := e), TimeGraphFrameSpace (e := e)) :=
    ⟨fun q ↦ (boundaryFiberCoordinates A q.1).symm q.2, continuous_boundaryFiberCoordinates_symm A⟩
  exact (F.comp (((ContinuousMap.id I).prodMap b).prodMap (ContinuousMap.id _))).continuous

variable (τ : N × TimeGraphFrameSpace (e := e) → Vector (e.ambientDimension + 6))

def normalizedEndpointTube (t : I) :=
  OpenFiberCollapse.coordinateTube τ (endpointFiberCoordinates A b) t

theorem normalizedEndpointTube_zero : normalizedEndpointTube A b τ 0 = τ := by
  funext p
  change τ (p.1, boundaryFiberCoordinates A (0, b p.1) p.2) = τ p
  rw [boundaryFiberCoordinates_zero]
  rfl

theorem normalizedEndpointTube_core (t : I) (p : N) :
    normalizedEndpointTube A b τ t (p, 0) = τ (p, 0) := by
  change τ (p, boundaryFiberCoordinates A (t, b p) 0) = τ (p, 0)
  rw [map_zero]

theorem isOpenEmbedding_normalizedEndpointTube (hτ : IsOpenEmbedding τ) (t : I) :
    IsOpenEmbedding (normalizedEndpointTube A b τ t) :=
  OpenFiberCollapse.isOpenEmbedding_coordinateTube τ (endpointFiberCoordinates A b) hτ
    (continuous_endpointFiberCoordinates A b) (continuous_endpointFiberCoordinates_symm A b) t

variable [CompactSpace N] (hτ : IsOpenEmbedding τ)

def endpointCollapseFamily : C(I × OnePoint (Vector (e.ambientDimension + 6)),
    OnePoint (TimeGraphFrameSpace (e := e))) :=
  OpenFiberCollapse.coordinateCollapseFamily τ (endpointFiberCoordinates A b) hτ
    (continuous_endpointFiberCoordinates A b) (continuous_endpointFiberCoordinates_symm A b)

def normalizedEndpointCollapse (t : I) : C(OnePoint (Vector (e.ambientDimension + 6)),
    OnePoint (TimeGraphFrameSpace (e := e))) :=
  (endpointCollapseFamily A b τ hτ).comp
    ((ContinuousMap.const _ t).prodMk (ContinuousMap.id _))

theorem endpointCollapseFamily_apply (t : I) (z : OnePoint (Vector (e.ambientDimension + 6))) :
    endpointCollapseFamily A b τ hτ (t, z) =
      OpenFiberCollapse.collapseOnePoint (normalizedEndpointTube A b τ t) z :=
  OpenFiberCollapse.coordinateCollapseFamily_apply τ (endpointFiberCoordinates A b) hτ
    (continuous_endpointFiberCoordinates A b) (continuous_endpointFiberCoordinates_symm A b) t z

theorem endpointCollapseFamily_infty (t : I) :
    endpointCollapseFamily A b τ hτ (t, OnePoint.infty) = OnePoint.infty := by
  rw [endpointCollapseFamily_apply, OpenFiberCollapse.collapseOnePoint_infty]

theorem endpointCollapseFamily_zero (z : OnePoint (Vector (e.ambientDimension + 6))) :
    endpointCollapseFamily A b τ hτ (0, z) = OpenFiberCollapse.collapseOnePoint τ z := by
  rw [endpointCollapseFamily_apply, normalizedEndpointTube_zero]

theorem endpointCollapseFamily_zero_fiber
    (t : I) (z : OnePoint (Vector (e.ambientDimension + 6))) :
    endpointCollapseFamily A b τ hτ (t, z) = (↑(0 : TimeGraphFrameSpace (e := e))) ↔
      ∃ p : N, (τ (p, 0) : OnePoint _) = z := by
  rw [endpointCollapseFamily_apply, OpenFiberCollapse.collapseOnePoint_eq_coe_iff _
    (isOpenEmbedding_normalizedEndpointTube A b τ hτ t).injective]
  simp only [normalizedEndpointTube_core]

end Endpoint

namespace SlabTubeData

variable {A} (D : SlabTubeData A)

def originalEndNormalizationHomotopy : (D.endCollapse 1).Homotopy
    (normalizedEndpointCollapse A (originalEndBoundaryMap A) D.originalEndTube
      D.isOpenEmbedding_originalEndTube 1) where
  toContinuousMap := endpointCollapseFamily A (originalEndBoundaryMap A) D.originalEndTube
    D.isOpenEmbedding_originalEndTube
  map_zero_left z := (endpointCollapseFamily_zero A (originalEndBoundaryMap A) D.originalEndTube
    D.isOpenEmbedding_originalEndTube z).trans (D.endCollapse_eq_originalEndTube z).symm
  map_one_left _ := rfl

theorem originalEndNormalizationHomotopy_infty (t : I) :
    D.originalEndNormalizationHomotopy (t, OnePoint.infty) = OnePoint.infty :=
  endpointCollapseFamily_infty A (originalEndBoundaryMap A) D.originalEndTube
    D.isOpenEmbedding_originalEndTube t

variable [T2Space M] (hR : A.radius = 2)

def surgeryEndNormalizationHomotopy : letI := UnitSurgery.compactSpace_target A hR;
    (D.endCollapse 0).Homotopy
      (normalizedEndpointCollapse A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
        (D.isOpenEmbedding_surgeryEndTube hR) 1) := by
  let := UnitSurgery.compactSpace_target A hR
  exact {
    toContinuousMap := endpointCollapseFamily A (surgeryEndBoundaryMap A hR)
      (D.surgeryEndTube hR) (D.isOpenEmbedding_surgeryEndTube hR)
    map_zero_left := fun z ↦
      (endpointCollapseFamily_zero A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
        (D.isOpenEmbedding_surgeryEndTube hR) z).trans (D.endCollapse_eq_surgeryEndTube hR z).symm
    map_one_left := fun _ ↦ rfl }

theorem surgeryEndNormalizationHomotopy_infty (t : I) :
    D.surgeryEndNormalizationHomotopy hR (t, OnePoint.infty) = OnePoint.infty := by
  let := UnitSurgery.compactSpace_target A hR
  exact endpointCollapseFamily_infty A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
    (D.isOpenEmbedding_surgeryEndTube hR) t

def normalizedEndCollapseHomotopy : letI := UnitSurgery.compactSpace_target A hR;
    (normalizedEndpointCollapse A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
      (D.isOpenEmbedding_surgeryEndTube hR) 1).Homotopy
        (normalizedEndpointCollapse A (originalEndBoundaryMap A) D.originalEndTube
          D.isOpenEmbedding_originalEndTube 1) :=
  (D.surgeryEndNormalizationHomotopy hR).symm.trans
    (D.collapseHomotopy.trans D.originalEndNormalizationHomotopy)

theorem normalizedEndCollapseHomotopy_infty (t : I) :
    D.normalizedEndCollapseHomotopy hR (t, OnePoint.infty) = OnePoint.infty := by
  rw [normalizedEndCollapseHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · rw [ContinuousMap.Homotopy.symm_apply, D.surgeryEndNormalizationHomotopy_infty]
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact D.collapseHomotopy_infty _
    · exact D.originalEndNormalizationHomotopy_infty _

end SlabTubeData

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
