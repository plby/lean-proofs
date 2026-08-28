import Wikipedia.NoExoticSixSphere.RoundedTraceOriginalEndFraming
import Wikipedia.NoExoticSixSphere.RoundedTraceRoundEndHomotopy
import Wikipedia.NoExoticSixSphere.UnitSurgeryNormalFraming
import Wikipedia.NoExoticSixSphere.FramedTubeCollapseComparison

/-!
# Tube-certified smooth collapses at the two actual trace endpoints

Both Euclidean embeddings and normal framings are actual constructed data.
The original atlas and the independent canonical surgery atlas are retained.
The maps are the certified chosen smooth collapses with the explicit
one-point normal-coordinate changes, not new maps assigned those names.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def originalFramedTubeData :
    (OriginalEnd.embedding A).FramedTubeData (OriginalEnd.normalFraming A) :=
  letI : Nonempty M := ⟨f (pole 3)⟩
  (OriginalEnd.embedding A).framedTubeData (OriginalEnd.normalFraming A)

def originalCertifiedCollapse :
    C(OnePoint (Vector (e.ambientDimension + 6)), OnePoint (TimeGraphFrameSpace (e := e))) :=
  (originalFramedTubeData A).reindexedCollapse (OriginalEnd.normalModelCoordinates A).symm

theorem originalCertifiedCollapse_infty :
    originalCertifiedCollapse A OnePoint.infty = OnePoint.infty :=
  (originalFramedTubeData A).reindexedCollapse_infty (OriginalEnd.normalModelCoordinates A).symm

theorem originalCertifiedCollapse_formula (z : OnePoint (Vector (e.ambientDimension + 6))) :
    letI : Nonempty M := ⟨f (pole 3)⟩;
    originalCertifiedCollapse A z = OnePoint.map (OriginalEnd.normalModelCoordinates A)
      (((OriginalEnd.embedding A).framedCollapseData (OriginalEnd.normalFraming A)).map z) := rfl

variable [T2Space M] (hR : A.radius = 2)

theorem nonempty_surgeryTarget : Nonempty (UnitSurgery.Target A hR) := by
  refine ⟨FramedSurgery.newMap (E := Vector 4) (UnitSurgery.face A hR) 2
    (⟨0, ?_⟩, pole 2)⟩
  change dist (0 : Vector 4) 0 < 1
  simp

def surgeryFiberCoordinates : letI := UnitSurgery.targetChartedSpace A hR;
    TimeGraphFrameSpace (e := e) ≃ₗᵢ[ℝ] (UnitSurgery.inducedEmbedding A hR).NormalModel :=
  (boundaryFrameCoordinates (e := e)).trans (UnitSurgery.normalModelCoordinates A hR).symm

theorem surgeryFraming_coordinates (p : UnitSurgery.Target A hR)
    (v : TimeGraphFrameSpace (e := e)) : letI := UnitSurgery.targetChartedSpace A hR;
    (UnitSurgery.normalFraming A hR).ambient p (surgeryFiberCoordinates A hR v) =
      UnitSurgery.inducedNormalFrame A hR p (boundaryFrameCoordinates (e := e) v) := by
  let := UnitSurgery.targetChartedSpace A hR
  rw [UnitSurgery.normalFraming_ambient]
  change UnitSurgery.inducedNormalFrame A hR p
    (UnitSurgery.normalModelCoordinates A hR
      ((UnitSurgery.normalModelCoordinates A hR).symm (boundaryFrameCoordinates (e := e) v))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

def surgeryFramedTubeData : letI := UnitSurgery.targetChartedSpace A hR;
    (UnitSurgery.inducedEmbedding A hR).FramedTubeData (UnitSurgery.normalFraming A hR) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let := nonempty_surgeryTarget A hR
  exact (UnitSurgery.inducedEmbedding A hR).framedTubeData (UnitSurgery.normalFraming A hR)

def surgeryCertifiedCollapse :
    C(OnePoint (Vector (e.ambientDimension + 6)), OnePoint (TimeGraphFrameSpace (e := e))) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  exact (surgeryFramedTubeData A hR).reindexedCollapse (surgeryFiberCoordinates A hR)

theorem surgeryCertifiedCollapse_infty :
    surgeryCertifiedCollapse A hR OnePoint.infty = OnePoint.infty := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  exact (surgeryFramedTubeData A hR).reindexedCollapse_infty (surgeryFiberCoordinates A hR)

theorem surgeryCertifiedCollapse_formula (z : OnePoint (Vector (e.ambientDimension + 6))) :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI := nonempty_surgeryTarget A hR;
    surgeryCertifiedCollapse A hR z = OnePoint.map (surgeryFiberCoordinates A hR).symm
      (((UnitSurgery.inducedEmbedding A hR).framedCollapseData
        (UnitSurgery.normalFraming A hR)).map z) := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
