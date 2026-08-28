import Wikipedia.NoExoticSixSphere.RoundedTraceCertifiedEndHomotopy

/-!
# The chosen collapse maps agree up to based homotopy in the same normal model

Both endpoint embeddings have the same ambient dimension. Their normal
coordinate reindexings agree exactly, so the common one-point homeomorphism
can be cancelled. The original reflection remains in its actual framing.
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

def chosenOriginalCollapse :
    C(OnePoint (Vector (e.ambientDimension + 6)),
      OnePoint (Vector ((e.ambientDimension + 6) - 6))) :=
  (originalFramedTubeData A).collapseData.map

theorem originalCertifiedCollapse_eq_chosen
    (z : OnePoint (Vector (e.ambientDimension + 6))) :
    originalCertifiedCollapse A z =
      OnePoint.map (OriginalEnd.normalModelCoordinates A) (chosenOriginalCollapse A z) := rfl

variable [T2Space M] (hR : A.radius = 2)

theorem surgeryFiberCoordinates_symm (v : Vector ((e.ambientDimension + 6) - 6)) :
    letI := UnitSurgery.targetChartedSpace A hR;
    (surgeryFiberCoordinates A hR).symm v = OriginalEnd.normalModelCoordinates A v := rfl

def chosenSurgeryCollapse :
    C(OnePoint (Vector (e.ambientDimension + 6)),
      OnePoint (Vector ((e.ambientDimension + 6) - 6))) := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  exact (surgeryFramedTubeData A hR).collapseData.map

theorem surgeryCertifiedCollapse_eq_chosen
    (z : OnePoint (Vector (e.ambientDimension + 6))) :
    surgeryCertifiedCollapse A hR z =
      OnePoint.map (OriginalEnd.normalModelCoordinates A) (chosenSurgeryCollapse A hR z) := rfl

theorem exists_chosenEndCollapse_homotopy :
    ∃ H : (chosenSurgeryCollapse A hR).Homotopy (chosenOriginalCollapse A),
      ∀ t : I, H (t, OnePoint.infty) = OnePoint.infty := by
  obtain ⟨H, hH⟩ := exists_certifiedEndCollapse_homotopy A hR
  let g := (OriginalEnd.normalModelCoordinates A).toHomeomorph.onePointCongr
  let G : C(OnePoint (TimeGraphFrameSpace (e := e)),
      OnePoint (Vector ((e.ambientDimension + 6) - 6))) := ⟨g.symm, g.symm.continuous⟩
  let H' : (chosenSurgeryCollapse A hR).Homotopy (chosenOriginalCollapse A) := {
    toContinuousMap := G.comp H.toContinuousMap
    map_zero_left := fun z ↦ (congrArg G (H.map_zero_left z)).trans (by
      rw [surgeryCertifiedCollapse_eq_chosen]
      exact g.symm_apply_apply (chosenSurgeryCollapse A hR z))
    map_one_left := fun z ↦ (congrArg G (H.map_one_left z)).trans (by
      rw [originalCertifiedCollapse_eq_chosen]
      exact g.symm_apply_apply (chosenOriginalCollapse A z)) }
  refine ⟨H', ?_⟩
  intro t
  change G (H (t, OnePoint.infty)) = OnePoint.infty
  rw [hH]
  rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
