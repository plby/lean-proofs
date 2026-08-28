import Wikipedia.NoExoticSixSphere.QuaternionicHopfPairedTubeHomotopy

/-!
# Smoothness of the retained Hopf tubes

The actual chosen tube is smooth on its full source. Base parametrization,
linear coordinates, and the smooth fiber rotations preserve this property.
The paired endpoint therefore retains joint smoothness in base and normal
variables, in addition to its already computed normal derivative.
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

theorem contMDiff_southChosenTube :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, southChartEmbedding.NormalModel))
      (𝓡 southChartEmbedding.ambientDimension) ∞ southChartTube.tube := by
  have h := southChartTube.tube.contMDiffOn
  rw [southChartTube.source_univ] at h
  exact contMDiffOn_univ.mp h

theorem contMDiff_southStabilizedBaseTube :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, V 4 × ℝ)) 𝓘(ℝ, V 7 × ℝ) ∞
      southStabilizedBaseTube := by
  have hv : ContMDiff ((𝓡 3).prod 𝓘(ℝ, V 4 × ℝ)) 𝓘(ℝ, V 4) ∞
      (fun p : Sphere 3 × (V 4 × ℝ) ↦ p.2.1) :=
    contDiff_fst.contMDiff.comp contMDiff_snd
  have hu : ContMDiff ((𝓡 3).prod 𝓘(ℝ, V 4 × ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : Sphere 3 × (V 4 × ℝ) ↦ p.2.2) :=
    contDiff_snd.contMDiff.comp contMDiff_snd
  exact (contMDiff_southChosenTube.comp
    ((southFiberDiffeomorph.contMDiff.comp contMDiff_fst).prodMk hv)).prodMk_space hu

theorem contMDiff_southStabilizedTube :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, V 4 × ℝ)) (𝓡 8) ∞ southStabilizedTube :=
  (StereographicEquator.stabilizedEquiv 7).contDiff.contMDiff.comp
    contMDiff_southStabilizedBaseTube

theorem contMDiff_southNormalizedTube :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, SouthNormalModel)) (𝓡 8) ∞ southNormalizedTube :=
  contMDiff_southStabilizedTube.comp
    (f := fun p : Sphere 3 × SouthNormalModel ↦
      (p.1, southChosenNormalCoordinates.symm p.2))
    (contMDiff_fst.prodMk
      (southChosenNormalCoordinates.symm.contDiff.contMDiff.comp contMDiff_snd))

theorem contMDiff_southTubeFrameTube (t : I) :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, SouthNormalModel)) (𝓡 8) ∞ (southTubeFrameTube t) := by
  have hr : ContMDiff ((𝓡 3).prod 𝓘(ℝ, SouthNormalModel))
      𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : Sphere 3 × SouthNormalModel ↦
        (southTubeFiberRotation t p.1).toContinuousLinearMap) :=
    contMDiff_southTubeFiberRotation.comp
      (f := fun p : Sphere 3 × SouthNormalModel ↦ ((t : ℝ), p.1))
      (contMDiff_const.prodMk contMDiff_fst)
  have h := contMDiff_southNormalizedTube.comp
    (contMDiff_fst.prodMk (hr.clm_apply contMDiff_snd))
  have he : southTubeFrameTube t = fun p : Sphere 3 × SouthNormalModel ↦
      southNormalizedTube (p.1, southTubeFiberRotation t p.1 p.2) :=
    funext (southTubeFrameTube_apply t)
  rw [he]
  exact h

theorem contMDiff_southPairedFrameTube (t : I) :
    ContMDiff (((𝓡 3).prod (𝓡 3)).prod 𝓘(ℝ, SouthPairNormalModel))
      𝓘(ℝ, SouthPairAmbientModel) ∞ (southPairedFrameTube t) := by
  have hn : ContMDiff (((𝓡 3).prod (𝓡 3)).prod 𝓘(ℝ, SouthPairNormalModel))
      𝓘(ℝ, SouthNormalModel × SouthNormalModel) ∞
      (fun p : (Sphere 3 × Sphere 3) × SouthPairNormalModel ↦ (p.2.fst, p.2.snd)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ SouthNormalModel SouthNormalModel).contDiff.contMDiff.comp
      contMDiff_snd
  have hl := (contMDiff_southTubeFrameTube t).comp
    ((contMDiff_fst.comp contMDiff_fst).prodMk (contDiff_fst.contMDiff.comp hn))
  have hr := (contMDiff_southTubeFrameTube t).comp
    ((contMDiff_snd.comp contMDiff_fst).prodMk (contDiff_snd.contMDiff.comp hn))
  have hp := hl.prodMk_space hr
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.contDiff.contMDiff.comp hp
  have he : southPairedFrameTube t =
      fun p : (Sphere 3 × Sphere 3) × SouthPairNormalModel ↦ WithLp.toLp 2
        (southTubeFrameTube t (p.1.1, p.2.fst), southTubeFrameTube t (p.1.2, p.2.snd)) :=
    funext (southPairedFrameTube_apply t)
  rw [he]
  simpa only [Function.comp_def, WithLp.prodContinuousLinearEquiv_symm_apply] using h

end NoExoticSixSphere.QuaternionicHopf
