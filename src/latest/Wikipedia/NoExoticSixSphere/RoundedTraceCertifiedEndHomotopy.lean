import Wikipedia.NoExoticSixSphere.RoundedTraceCertifiedEndCollapse

/-!
# The actual trace relates the two chosen tube-certified smooth collapses

The comparison includes the round-tube deformation, radius independence,
and the explicit normal-model coordinate changes. All homotopies fix
infinity. The original manifold atlas and canonical surgery atlas remain
unchanged; this does not assert the missing framed-bordism detection theorem.
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

theorem exists_originalCertifiedRoundHomotopy :
    ∃ H : (originalCertifiedCollapse A).Homotopy
      (roundEndpointCollapse A (originalEndBoundaryMap A) D.originalEndTube
        D.isOpenEmbedding_originalEndTube),
      ∀ t : I, H (t, OnePoint.infty) = OnePoint.infty := by
  have hf (q : M × TimeGraphFrameSpace (e := e)) : D.roundOriginalEndTube q =
      (OriginalEnd.embedding A).toFun q.1 + (OriginalEnd.normalFraming A).ambient q.1
        ((OriginalEnd.normalModelCoordinates A).symm
          (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
            D.originalRoundRadius q.2)) := by
    let w := OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
      D.originalRoundRadius q.2
    have hB := OriginalEnd.normalFraming_ambient A q.1
      ((OriginalEnd.normalModelCoordinates A).symm w)
    rw [LinearIsometryEquiv.apply_symm_apply] at hB
    exact (roundEndpointTube_formula A (originalEndBoundaryMap A) D.originalEndTube
      (fun m ↦ e.heightCylinder (m, UnroundedTrace.height A)) D.radius D.radius_pos
        (originalEndTube_apply A D) q).trans
          (congrArg (fun v ↦ e.heightCylinder (q.1, UnroundedTrace.height A) + v) hB.symm)
  obtain ⟨H, hH⟩ := (originalFramedTubeData A).exists_based_homotopy_to_roundTube
    (OriginalEnd.normalModelCoordinates A).symm D.originalRoundRadius D.originalRoundRadius_pos
      D.roundOriginalEndTube D.isOpenEmbedding_roundOriginalEndTube hf
  let H' : (originalCertifiedCollapse A).Homotopy
      (roundEndpointCollapse A (originalEndBoundaryMap A) D.originalEndTube
        D.isOpenEmbedding_originalEndTube) := {
    toContinuousMap := H.toContinuousMap
    map_zero_left := H.map_zero_left
    map_one_left := fun z ↦ (H.map_one_left z).trans
      (roundEndpointCollapse_apply A (originalEndBoundaryMap A) D.originalEndTube
        D.isOpenEmbedding_originalEndTube z).symm }
  exact ⟨H', hH⟩

variable [T2Space M] (hR : A.radius = 2)

theorem exists_surgeryCertifiedRoundHomotopy : letI := UnitSurgery.compactSpace_target A hR;
    ∃ H : (surgeryCertifiedCollapse A hR).Homotopy
      (roundEndpointCollapse A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
        (D.isOpenEmbedding_surgeryEndTube hR)),
      ∀ t : I, H (t, OnePoint.infty) = OnePoint.infty := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  have hf (q : UnitSurgery.Target A hR × TimeGraphFrameSpace (e := e)) :
      D.roundSurgeryEndTube hR q = (UnitSurgery.inducedEmbedding A hR).toFun q.1 +
        (UnitSurgery.normalFraming A hR).ambient q.1 (surgeryFiberCoordinates A hR
          (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
            (D.surgeryRoundRadius hR) q.2)) := by
    have hB := surgeryFraming_coordinates A hR q.1
      (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e))
        (D.surgeryRoundRadius hR) q.2)
    exact (D.roundSurgeryEndTube_apply hR q).trans
      (congrArg (fun v ↦ UnitSurgery.ambientMap A hR q.1 + v) hB.symm)
  obtain ⟨H, hH⟩ := (surgeryFramedTubeData A hR).exists_based_homotopy_to_roundTube
    (surgeryFiberCoordinates A hR) (D.surgeryRoundRadius hR) (D.surgeryRoundRadius_pos hR)
      (D.roundSurgeryEndTube hR) (D.isOpenEmbedding_roundSurgeryEndTube hR) hf
  let H' : (surgeryCertifiedCollapse A hR).Homotopy
      (roundEndpointCollapse A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
        (D.isOpenEmbedding_surgeryEndTube hR)) := {
    toContinuousMap := H.toContinuousMap
    map_zero_left := H.map_zero_left
    map_one_left := fun z ↦ (H.map_one_left z).trans
      (roundEndpointCollapse_apply A (surgeryEndBoundaryMap A hR) (D.surgeryEndTube hR)
        (D.isOpenEmbedding_surgeryEndTube hR) z).symm }
  exact ⟨H', hH⟩

include D in
theorem exists_certifiedEndHomotopy :
    ∃ H : (surgeryCertifiedCollapse A hR).Homotopy (originalCertifiedCollapse A),
      ∀ t : I, H (t, OnePoint.infty) = OnePoint.infty := by
  let := UnitSurgery.compactSpace_target A hR
  obtain ⟨Ho, ho⟩ := D.exists_originalCertifiedRoundHomotopy
  obtain ⟨Hs, hs⟩ := D.exists_surgeryCertifiedRoundHomotopy hR
  refine ⟨Hs.trans ((D.roundEndCollapseHomotopy hR).trans Ho.symm), ?_⟩
  intro t
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hs _
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact D.roundEndCollapseHomotopy_infty hR _
    · rw [ContinuousMap.Homotopy.symm_apply]
      exact ho _

end SlabTubeData

theorem exists_certifiedEndCollapse_homotopy [T2Space M] (A : FramedAttachingProduct e a f)
    (hR : A.radius = 2) :
    ∃ H : (surgeryCertifiedCollapse A hR).Homotopy (originalCertifiedCollapse A),
      ∀ t : I, H (t, OnePoint.infty) = OnePoint.infty :=
  (slabTubeData A).exists_certifiedEndHomotopy hR

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
