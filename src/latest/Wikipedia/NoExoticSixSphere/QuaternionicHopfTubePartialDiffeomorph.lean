import Wikipedia.NoExoticSixSphere.QuaternionicHopfTubeSmoothness
import Wikipedia.NoExoticSixSphere.SmoothProductTube
import Wikipedia.NoExoticSixSphere.SmoothFiberCoordinates
import Wikipedia.NoExoticSixSphere.DiffeomorphProductModels

/-!
# Smooth partial inverses for the actual stabilized Hopf tube

The original certified tube is preserved through its base diffeomorphism,
stabilization, fixed normal coordinates, and smooth fiber-coordinate family.
Every stage has full source and is exactly the tube already used for collapse.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

local instance : ChartedSpace (V 3) {x : Sphere 7 // sphereMap x = south} :=
  regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

local instance : IsManifold (𝓡 3) ∞ {x : Sphere 7 // sphereMap x = south} :=
  regularFiber_isManifold sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])

def southStabilizedBasePartial :
    PartialDiffeomorph ((𝓡 3).prod 𝓘(ℝ, V 4 × ℝ)) 𝓘(ℝ, V 7 × ℝ)
      (Sphere 3 × (V 4 × ℝ)) (V 7 × ℝ) ∞ :=
  (southFiberDiffeomorph.prodCongr
    (Diffeomorph.refl 𝓘(ℝ, V 4 × ℝ) (V 4 × ℝ) ∞)).toPartialDiffeomorph.trans
      (OpenFiberCollapse.productTubePartial southChartTube.tube southChartTube.source_univ)

theorem southStabilizedBasePartial_apply (p : Sphere 3 × (V 4 × ℝ)) :
    southStabilizedBasePartial p = southStabilizedBaseTube p := rfl

theorem southStabilizedBasePartial_source : southStabilizedBasePartial.source = Set.univ :=
  partialDiffeomorph_trans_source_univ _ _ rfl
    (OpenFiberCollapse.productTubePartial_source southChartTube.tube southChartTube.source_univ)

def southStabilizedPartial :
    PartialDiffeomorph ((𝓡 3).prod 𝓘(ℝ, V 4 × ℝ)) (𝓡 8)
      (Sphere 3 × (V 4 × ℝ)) (V 8) ∞ :=
  southStabilizedBasePartial.trans
    (StereographicEquator.stabilizedEquiv 7).toDiffeomorph.toPartialDiffeomorph

theorem southStabilizedPartial_apply (p : Sphere 3 × (V 4 × ℝ)) :
    southStabilizedPartial p = southStabilizedTube p := rfl

theorem southStabilizedPartial_source : southStabilizedPartial.source = Set.univ :=
  partialDiffeomorph_trans_source_univ _ _ southStabilizedBasePartial_source rfl

def southNormalizingDiffeomorph :
    Diffeomorph ((𝓡 3).prod 𝓘(ℝ, SouthNormalModel)) ((𝓡 3).prod 𝓘(ℝ, V 4 × ℝ))
      (Sphere 3 × SouthNormalModel) (Sphere 3 × (V 4 × ℝ)) ∞ := by
  let C : Diffeomorph 𝓘(ℝ, SouthNormalModel) 𝓘(ℝ, V 4 × ℝ)
      SouthNormalModel (V 4 × ℝ) ∞ := southChosenNormalCoordinates.symm.toDiffeomorph
  exact diffeomorphProd (Diffeomorph.refl (𝓡 3) (Sphere 3) ∞) C

def southNormalizedPartial :
    PartialDiffeomorph ((𝓡 3).prod 𝓘(ℝ, SouthNormalModel)) (𝓡 8)
      (Sphere 3 × SouthNormalModel) (V 8) ∞ :=
  southNormalizingDiffeomorph.toPartialDiffeomorph.trans southStabilizedPartial

theorem southNormalizedPartial_apply (p : Sphere 3 × SouthNormalModel) :
    southNormalizedPartial p = southNormalizedTube p := rfl

theorem southNormalizedPartial_source : southNormalizedPartial.source = Set.univ :=
  partialDiffeomorph_trans_source_univ _ _ rfl southStabilizedPartial_source

theorem contMDiff_southTubeFiberRotation_at (t : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : Sphere 3 ↦ (southTubeFiberRotation t p).toContinuousLinearMap) :=
  contMDiff_southTubeFiberRotation.comp
    (f := fun p : Sphere 3 ↦ (t, p)) (contMDiff_const.prodMk contMDiff_id)

theorem contMDiff_southTubeFiberRotation_symm_at (t : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : Sphere 3 ↦ (southTubeFiberRotation t p).symm.toContinuousLinearMap) :=
  contMDiff_southTubeFiberRotation_symm.comp
    (f := fun p : Sphere 3 ↦ (t, p)) (contMDiff_const.prodMk contMDiff_id)

def southTubeFiberDiffeomorph (t : ℝ) :
    Diffeomorph ((𝓡 3).prod 𝓘(ℝ, SouthNormalModel))
      ((𝓡 3).prod 𝓘(ℝ, SouthNormalModel))
      (Sphere 3 × SouthNormalModel) (Sphere 3 × SouthNormalModel) ∞ :=
  fiberCoordinatesDiffeomorph (southTubeFiberRotation t)
    (contMDiff_southTubeFiberRotation_at t) (contMDiff_southTubeFiberRotation_symm_at t)

def southTubeFramePartial (t : I) :
    PartialDiffeomorph ((𝓡 3).prod 𝓘(ℝ, SouthNormalModel)) (𝓡 8)
      (Sphere 3 × SouthNormalModel) (V 8) ∞ :=
  (southTubeFiberDiffeomorph t).toPartialDiffeomorph.trans southNormalizedPartial

theorem southTubeFramePartial_apply (t : I) (p : Sphere 3 × SouthNormalModel) :
    southTubeFramePartial t p = southTubeFrameTube t p := by
  rw [southTubeFrameTube_apply]
  rfl

theorem southTubeFramePartial_source (t : I) : (southTubeFramePartial t).source = Set.univ :=
  partialDiffeomorph_trans_source_univ _ _ rfl southNormalizedPartial_source

end NoExoticSixSphere.QuaternionicHopf
