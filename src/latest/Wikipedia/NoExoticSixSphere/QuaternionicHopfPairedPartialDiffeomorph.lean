import Wikipedia.NoExoticSixSphere.QuaternionicHopfTubePartialDiffeomorph
import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductEuclideanTube
import Wikipedia.NoExoticSixSphere.SmoothPairedTube

/-!
# The actual paired Euclidean tube has a full-source smooth partial inverse

Pair the original smooth inverses, then apply the already specified source
atlas and finite coordinate changes. The resulting partial diffeomorphism
is proved to be exactly the tube whose collapse class was checked.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

def southPairedFramePartial (t : I) :
    PartialDiffeomorph (((𝓡 3).prod (𝓡 3)).prod 𝓘(ℝ, SouthPairNormalModel))
      𝓘(ℝ, SouthPairAmbientModel) ((Sphere 3 × Sphere 3) × SouthPairNormalModel)
        SouthPairAmbientModel ∞ :=
  OpenFiberCollapse.hilbertPairedTubePartial (southTubeFramePartial t) (southTubeFramePartial t)
    (southTubeFramePartial_source t) (southTubeFramePartial_source t)

theorem southPairedFramePartial_apply (t : I)
    (p : (Sphere 3 × Sphere 3) × SouthPairNormalModel) :
    southPairedFramePartial t p = southPairedFrameTube t p := by
  simp only [southPairedFramePartial, OpenFiberCollapse.hilbertPairedTubePartial_apply,
    OpenFiberCollapse.hilbertPairedTube, southTubeFramePartial_apply, southPairedFrameTube_apply]

theorem southPairedFramePartial_source (t : I) : (southPairedFramePartial t).source = Set.univ :=
  OpenFiberCollapse.hilbertPairedTubePartial_source _ _
    (southTubeFramePartial_source t) (southTubeFramePartial_source t)

def southPairEuclideanSourceDiffeomorph :
    letI := southPairEuclideanAtlas;
    Diffeomorph ((𝓡 6).prod (𝓡 10))
      (((𝓡 3).prod (𝓡 3)).prod 𝓘(ℝ, SouthPairNormalModel))
      ((Sphere 3 × Sphere 3) × V 10) ((Sphere 3 × Sphere 3) × SouthPairNormalModel) ∞ := by
  let _ := southPairEuclideanAtlas
  exact diffeomorphProd southPairEuclideanToProduct
    southPairNormalEuclideanCoordinates.symm.toDiffeomorph

theorem southPairEuclideanSourceDiffeomorph_apply (p : (Sphere 3 × Sphere 3) × V 10) :
    letI := southPairEuclideanAtlas;
    southPairEuclideanSourceDiffeomorph p =
      (p.1, southPairNormalEuclideanCoordinates.symm p.2) := rfl

def southPairEuclideanPartial :
    letI := southPairEuclideanAtlas;
    PartialDiffeomorph ((𝓡 6).prod (𝓡 10)) (𝓡 16)
      ((Sphere 3 × Sphere 3) × V 10) (V 16) ∞ := by
  let _ := southPairEuclideanAtlas
  let A := southPairAmbientEuclideanCoordinates.toContinuousLinearEquiv.toDiffeomorph
  exact (southPairEuclideanSourceDiffeomorph.toPartialDiffeomorph.trans
    (southPairedFramePartial 1)).trans A.toPartialDiffeomorph

theorem southPairEuclideanPartial_apply (p : (Sphere 3 × Sphere 3) × V 10) :
    letI := southPairEuclideanAtlas;
    southPairEuclideanPartial p = southPairEuclideanTube p := by
  let _ := southPairEuclideanAtlas
  simp only [southPairEuclideanPartial, partialDiffeomorph_trans_apply, diffeomorph_partial_apply,
    southPairEuclideanSourceDiffeomorph_apply, southPairedFramePartial_apply,
    ContinuousLinearEquiv.coe_toDiffeomorph, southPairEuclideanTube]
  rfl

theorem southPairEuclideanPartial_source :
    letI := southPairEuclideanAtlas; southPairEuclideanPartial.source = Set.univ := by
  let _ := southPairEuclideanAtlas
  exact partialDiffeomorph_trans_source_univ _ _
    (partialDiffeomorph_trans_source_univ _ _ rfl (southPairedFramePartial_source 1)) rfl

end NoExoticSixSphere.QuaternionicHopf
