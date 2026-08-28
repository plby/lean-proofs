import Wikipedia.NoExoticSixSphere.BasedImmersedSphereModel
import Wikipedia.NoExoticSixSphere.CenteredReferenceProductChart
import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairChart

/-!
# Arbitrary based sphere classes with a transverse unique common center

The normalized native chart and the actual embedded two-crossing reference
pair supply both local models. Their insertion and relative generic slices
produce self-transverse immersions in the original based homotopy classes,
with unique center fibers and transverse derivatives at that center.

Mutual transversality away from the common center is not yet asserted.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereSumNeck DoubleCrossingSpherePair

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_based_immersed_pair_transverse_at_center
    (f g : C(Sphere 3, M)) (hzero : f (sourceChart 0) = g (sourceChart 0)) :
    ∃ F G : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ F ∧
      ContMDiff (𝓡 3) (𝓡 6) ∞ G ∧ f.HomotopicRel F {sourceChart 0} ∧
      g.HomotopicRel G {sourceChart 0} ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) F s)) ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) G s)) ∧
      NativeSphereSelfTransverse F ∧ NativeSphereSelfTransverse G ∧
      F (sourceChart 0) = G (sourceChart 0) ∧
      Surjective ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
        (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0))) ∧
      (∀ s, F s = F (sourceChart 0) → s = sourceChart 0) ∧
      (∀ s, G s = G (sourceChart 0) → s = sourceChart 0) := by
  obtain ⟨Φ, hsource, hball, hcenter⟩ :=
    ProductChartCoordinates.exists_centered_reference_product_chart (f (sourceChart 0))
  have hball3 : ball (0 : Vector 3 × Vector 3) 3 ⊆ Φ.source := by rw [hsource]
  obtain ⟨F, hF, HF, hFi, hFt, hDF, hFu⟩ :=
    e.exists_based_immersed_representative_with_model r f (sourceChart 0) Φ hball3 hcenter
      alignedLeft contMDiff_alignedLeft norm_alignedLeft_le_two alignedLeft_center
      (injective_mfderiv_chartLeft Φ hball) (injective_chartLeft Φ hball)
  obtain ⟨G, hG, HG, hGi, hGt, hDG, hGu⟩ :=
    e.exists_based_immersed_representative_with_model r g (sourceChart 0) Φ hball3
      (hcenter.trans hzero) alignedRight contMDiff_alignedRight norm_alignedRight_le_two
      alignedRight_center (injective_mfderiv_chartRight Φ hball) (injective_chartRight Φ hball)
  have hF0 := HF.fst_eq_snd (mem_singleton (sourceChart 0))
  have hG0 := HG.fst_eq_snd (mem_singleton (sourceChart 0))
  refine ⟨F, G, hF, hG, HF, HG, hFi, hGi, hFt, hGt, hF0.symm.trans (hzero.trans hG0),
    ?_, ?_, ?_⟩
  · rw [hDF, hDG]
    exact chart_pairTransverse Φ hball (sourceChart 0) (sourceChart 0)
      ((chartLeft_center Φ hball).trans (chartRight_center Φ hball).symm)
  · intro s hs
    exact (hFu s).mp (hs.trans hF0.symm)
  · intro s hs
    exact (hGu s).mp (hs.trans hG0.symm)

end NoExoticSixSphere.EuclideanEmbedding
