import Wikipedia.NoExoticSixSphere.QuaternionicHopfPairedTubeHomotopy

/-!
# The initial paired collapse in the original sphere coordinates

Both copies of the chosen radius-dependent normal map are retained.
Undoing that fixed map identifies the initial collapse with the original
paired stabilized Hopf collapse on the whole compactification.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

def southChosenPairNormalCoordinates :
    ((V 4 × ℝ) × (V 4 × ℝ)) ≃ₜ SouthPairNormalModel :=
  (southChosenNormalCoordinates.prodCongr southChosenNormalCoordinates).toHomeomorph.trans
    southTubePairNormalCoordinates

theorem southChosenPairNormalCoordinates_apply (p : (V 4 × ℝ) × (V 4 × ℝ)) :
    southChosenPairNormalCoordinates p = WithLp.toLp 2
      (southChosenNormalCoordinates p.1, southChosenNormalCoordinates p.2) := rfl

theorem southChosenPairNormalCoordinates_symm_apply (v : SouthPairNormalModel) :
    southChosenPairNormalCoordinates.symm v =
      (southChosenNormalCoordinates.symm v.fst, southChosenNormalCoordinates.symm v.snd) := rfl

theorem southPairedFrameTube_zero_formula (p : (Sphere 3 × Sphere 3) × SouthPairNormalModel) :
    southPairedFrameTube 0 p =
      southStabilizedPairTube (p.1, southChosenPairNormalCoordinates.symm p.2) := by
  simp only [southPairedFrameTube_apply, southTubeFrameTube_zero, southNormalizedTube,
    southChosenPairNormalCoordinates_symm_apply, southStabilizedPairTube]

theorem southPairedCollapseHomotopy_zero (z : OnePoint SouthPairAmbientModel) :
    southPairedCollapseHomotopy (0, z) = southChosenPairNormalCoordinates.onePointCongr
      (OpenFiberCollapse.collapseOnePoint southStabilizedPairTube z) := by
  have he : southPairedFrameTube 0 = fun p ↦
      southStabilizedPairTube (p.1, southChosenPairNormalCoordinates.symm p.2) :=
    funext southPairedFrameTube_zero_formula
  rw [southPairedCollapseHomotopy_apply, he]
  exact OpenFiberCollapse.collapseOnePoint_fiberEquiv southStabilizedPairTube
    southChosenPairNormalCoordinates.symm.toEquiv
    southStabilizedPairTube_isOpenEmbedding.injective z

def southPairedTargetSphereHomeomorph : OnePoint SouthPairNormalModel ≃ₜ Sphere 10 :=
  southChosenPairNormalCoordinates.symm.onePointCongr.trans
    (SuspensionProductComparison.productPairSphereHomeomorph 4)

theorem southPairedTargetSphereHomeomorph_infty :
    southPairedTargetSphereHomeomorph OnePoint.infty = spherePole 10 := by
  change SuspensionProductComparison.productPairSphereHomeomorph 4 OnePoint.infty = spherePole 10
  exact SuspensionProductComparison.productPairSphereHomeomorph_infty 4

theorem southPairedSourceSphereHomeomorph_infty :
    StereographicEquator.stabilizedPairSphereHomeomorph 7 OnePoint.infty = spherePole 16 := by
  change SuspensionProductComparison.productPairSphereHomeomorph 7 OnePoint.infty = spherePole 16
  exact SuspensionProductComparison.productPairSphereHomeomorph_infty 7

theorem southPairedCollapseHomotopy_zero_original (z : OnePoint SouthPairAmbientModel) :
    southPairedTargetSphereHomeomorph (southPairedCollapseHomotopy (0, z)) =
      southPairedProductBasedMap.val (StereographicEquator.stabilizedPairSphereHomeomorph 7 z) := by
  rw [southPairedCollapseHomotopy_zero]
  change SuspensionProductComparison.productPairSphereHomeomorph 4
    (southChosenPairNormalCoordinates.symm.onePointCongr
      (southChosenPairNormalCoordinates.onePointCongr
        (OpenFiberCollapse.collapseOnePoint southStabilizedPairTube z))) = _
  have he : southChosenPairNormalCoordinates.symm.onePointCongr =
      southChosenPairNormalCoordinates.onePointCongr.symm := rfl
  rw [he, Homeomorph.symm_apply_apply]
  exact (southStabilizedPairTube_originalMap z).symm

end NoExoticSixSphere.QuaternionicHopf
