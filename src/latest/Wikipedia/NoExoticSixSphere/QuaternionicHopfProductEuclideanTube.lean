import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductEuclideanFrame

/-!
# The actual raw-frame tube in standard Euclidean coordinates

The source atlas and both finite coordinate changes are the ones already
compared with the original paired Hopf collapse. The tube's core and its
normal derivative are the constructed Euclidean embedding and frame.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def southPairEuclideanTube (p : (Sphere 3 × Sphere 3) × V 10) : V 16 :=
  southPairAmbientEuclideanCoordinates
    (southPairedFrameTube 1 (p.1, southPairNormalEuclideanCoordinates.symm p.2))

theorem southPairEuclideanTube_isOpenEmbedding :
    Topology.IsOpenEmbedding southPairEuclideanTube :=
  (southPairAmbientEuclideanCoordinates.toHomeomorph.isOpenEmbedding.comp
    (southPairedFrameTube_isOpenEmbedding 1)).comp
      ((Homeomorph.refl (Sphere 3 × Sphere 3)).prodCongr
        southPairNormalEuclideanCoordinates.symm.toHomeomorph).isOpenEmbedding

theorem contMDiff_southPairEuclideanTube :
    letI := southPairEuclideanAtlas;
    ContMDiff ((𝓡 6).prod (𝓡 10)) (𝓡 16) ∞ southPairEuclideanTube := by
  let _ := southPairEuclideanAtlas
  have hp : ContMDiff ((𝓡 6).prod (𝓡 10))
      (((𝓡 3).prod (𝓡 3)).prod 𝓘(ℝ, SouthPairNormalModel)) ∞
      (fun p : (Sphere 3 × Sphere 3) × V 10 ↦
        (p.1, southPairNormalEuclideanCoordinates.symm p.2)) :=
    (southPairEuclideanToProduct.contMDiff.comp contMDiff_fst).prodMk
      (southPairNormalEuclideanCoordinates.symm.contDiff.contMDiff.comp contMDiff_snd)
  have ht := (contMDiff_southPairedFrameTube 1).comp hp
  have h := southPairAmbientEuclideanCoordinates.toContinuousLinearEquiv.contDiff.contMDiff.comp ht
  exact h

theorem southPairEuclideanTube_core (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    southPairEuclideanTube (p, 0) = southPairEuclideanEmbedding.toFun p := by
  let _ := southPairEuclideanAtlas
  change southPairAmbientEuclideanCoordinates
    (southPairedFrameTube 1 (p, southPairNormalEuclideanCoordinates.symm 0)) = _
  rw [map_zero, southPairedRawTube_core]
  rfl

theorem hasFDerivAt_southPairEuclideanTube_normal (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    HasFDerivAt (fun v : V 10 ↦ southPairEuclideanTube (p, v))
      (southPairEuclideanNormalFrame.ambient p) 0 := by
  let _ := southPairEuclideanAtlas
  rw [southPairEuclideanNormalFrame_ambient]
  have ht : HasFDerivAt (fun v : SouthPairNormalModel ↦ southPairedFrameTube 1 (p, v))
      (southPairNormalFrame.ambient p) (southPairNormalEuclideanCoordinates.symm (0 : V 10)) := by
    simpa only [map_zero] using hasFDerivAt_southPairedFrameTube_one p
  have hc := ht.comp (0 : V 10) southPairNormalEuclideanCoordinates.symm.hasFDerivAt
  have h := southPairAmbientEuclideanCoordinates.toContinuousLinearMap.hasFDerivAt.comp
    (0 : V 10) hc
  exact h

theorem southPairEuclideanTube_collapse (z : OnePoint SouthPairAmbientModel) :
    OpenFiberCollapse.collapseOnePoint southPairEuclideanTube
      (southPairAmbientEuclideanCoordinates.toHomeomorph.onePointCongr z) =
        southPairNormalEuclideanCoordinates.toHomeomorph.onePointCongr
          (OpenFiberCollapse.collapseOnePoint (southPairedFrameTube 1) z) := by
  let τ : (Sphere 3 × Sphere 3) × V 10 → SouthPairAmbientModel :=
    fun p ↦ southPairedFrameTube 1 (p.1, southPairNormalEuclideanCoordinates.symm p.2)
  have hi : Function.Injective τ :=
    (southPairedFrameTube_isOpenEmbedding 1).injective.comp
      ((Homeomorph.refl (Sphere 3 × Sphere 3)).prodCongr
        southPairNormalEuclideanCoordinates.symm.toHomeomorph).injective
  have ha := OpenFiberCollapse.collapseOnePoint_ambientEquiv τ
    southPairAmbientEuclideanCoordinates.toHomeomorph hi z
  have hn := OpenFiberCollapse.collapseOnePoint_fiberEquiv (southPairedFrameTube 1)
    southPairNormalEuclideanCoordinates.symm.toEquiv
      (southPairedFrameTube_isOpenEmbedding 1).injective z
  exact ha.trans hn

end NoExoticSixSphere.QuaternionicHopf
