import Wikipedia.NoExoticSixSphere.RoundedTraceSphereCollapseHomotopy
import Wikipedia.NoExoticSixSphere.CubicalCollapseChoiceIndependence

/-!
# Native stable classes of the actual framed surgery endpoints

The constructed trace gives equality, not just simultaneous vanishing,
for arbitrary collapse choices on its actual endpoint embeddings and
normal frames. Both endpoint atlases are retained. The original endpoint
here is the constructed height-cylinder embedding with its signed frame;
comparison with the unstabilized input embedding is a separate obligation.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

omit [CompactSpace M] [IsManifold (𝓡 6) ∞ M] [T2Space M] in
theorem endpoint_ambientDimension_ge_eight (m : M) : 8 ≤ e.ambientDimension + 6 := by
  have h := e.dimension_le_ambient m
  omega

theorem endpoint_collapse_homotopic
    (dO : (OriginalEnd.embedding A).FramedCollapseData (OriginalEnd.normalFraming A)) :
    letI := UnitSurgery.targetChartedSpace A hR;
    ∀ dS : (UnitSurgery.inducedEmbedding A hR).FramedCollapseData
      (UnitSurgery.normalFraming A hR), dS.sphereMap.Homotopic dO.sphereMap := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : Nonempty M := ⟨f (pole 3)⟩
  let := nonempty_surgeryTarget A hR
  intro dS
  obtain ⟨H, -⟩ := exists_chosenEndSphereCollapse_homotopy A hR
  have hmid : (chosenSurgerySphereCollapse A hR).Homotopic
      (chosenOriginalSphereCollapse A) := ⟨H⟩
  exact (dS.sphereMap_homotopic (surgeryFramedTubeData A hR).collapseData).trans
    (hmid.trans ((originalFramedTubeData A).collapseData.sphereMap_homotopic dO))

theorem endpoint_nativeSixthStageClass_eq
    (dO : (OriginalEnd.embedding A).FramedCollapseData (OriginalEnd.normalFraming A)) :
    letI := UnitSurgery.targetChartedSpace A hR;
    ∀ dS : (UnitSurgery.inducedEmbedding A hR).FramedCollapseData
      (UnitSurgery.normalFraming A hR),
      dS.nativeSixthStageClass (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) =
        dO.nativeSixthStageClass (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) := by
  let := UnitSurgery.targetChartedSpace A hR
  intro dS
  apply CubicalStableSix.sphereClass_eq_of_homotopic
  exact SphereMapSuspension.reindex_homotopic (by
    change e.ambientDimension + 6 = (e.ambientDimension + 6) - 8 + 8
    have h := endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))
    omega) (by
    change (e.ambientDimension + 6) - 6 = (e.ambientDimension + 6) - 8 + 2
    have h := endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))
    omega) (endpoint_collapse_homotopic A hR dO dS)

theorem endpoint_cubicalStableClass_eq
    (dO : (OriginalEnd.embedding A).FramedCollapseData (OriginalEnd.normalFraming A)) :
    letI := UnitSurgery.targetChartedSpace A hR;
    ∀ dS : (UnitSurgery.inducedEmbedding A hR).FramedCollapseData
      (UnitSurgery.normalFraming A hR),
      dS.cubicalStableClass (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) =
        dO.cubicalStableClass (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) := by
  let := UnitSurgery.targetChartedSpace A hR
  intro dS
  exact congrArg CubicalStableSix.ofNative (endpoint_nativeSixthStageClass_eq A hR dO dS)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
