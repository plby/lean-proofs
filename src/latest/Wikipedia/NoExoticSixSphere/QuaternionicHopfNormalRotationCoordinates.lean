import Wikipedia.NoExoticSixSphere.QuaternionicHopfNormalFrameHomotopy

/-!
# Invertible fiber coordinates for the actual Hopf normal-frame homotopy

The coordinates are obtained from the proved full normal ranges, not
postulated as a family of invertible matrices. Their forward and inverse
ambient formulas give joint smoothness for subsequent tube reparametrization.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

theorem southNormalFrame_reconstruct (q : Sphere 3) (v : V 8)
    (hv : v ∈ (NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient q).rangeᗮ) :
    southNormalFrame.ambient q (southNormalFrame.ambientInverse q v) = v := by
  apply southNormalFrame.ambient_ambientInverse_range q
    ⟨v, by change v ∈ ((NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient q).rangeᗮ.starProjection).range
           rwa [Submodule.range_starProjection]⟩

def southRadialFrameEquiv (t : ℝ) (q : Sphere 3) : SouthNormalModel ≃L[ℝ]
    ((NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient q).rangeᗮ.starProjection).range :=
  (LinearEquiv.ofInjective (southRadialFrame t q).toLinearMap
    (southRadialFrame_injective t q)).toContinuousLinearEquiv.trans
      (ContinuousLinearEquiv.ofEq _ _ (by
        rw [Submodule.range_starProjection]
        exact southRadialFrame_range t q))

theorem southRadialFrameEquiv_val (t : ℝ) (q : Sphere 3) (v : SouthNormalModel) :
    (southRadialFrameEquiv t q v).val = southRadialFrame t q v := rfl

def southNormalRotationCoordinates (t : ℝ) (q : Sphere 3) :
    SouthNormalModel ≃L[ℝ] SouthNormalModel :=
  (southRadialFrameEquiv t q).trans (southNormalFrame.equiv q).symm

theorem southNormalRotationCoordinates_apply (t : ℝ) (q : Sphere 3) (v : SouthNormalModel) :
    southNormalRotationCoordinates t q v =
      southNormalFrame.ambientInverse q (southRadialFrame t q v) :=
  (southNormalFrame.ambientInverse_apply_range q (southRadialFrameEquiv t q v)).symm

theorem southNormalRotationCoordinates_frame (t : ℝ) (q : Sphere 3) (v : SouthNormalModel) :
    southNormalFrame.ambient q (southNormalRotationCoordinates t q v) =
      southRadialFrame t q v := by
  rw [southNormalRotationCoordinates_apply]
  apply southNormalFrame_reconstruct
  rw [← southRadialFrame_range t q]
  exact ⟨v, rfl⟩

theorem southNormalRotationCoordinates_zero (q : Sphere 3) :
    southNormalRotationCoordinates 0 q = ContinuousLinearEquiv.refl ℝ SouthNormalModel := by
  apply ContinuousLinearEquiv.ext
  funext v
  rw [southNormalRotationCoordinates_apply, southRadialFrame_zero,
    southNormalFrame.ambientInverse_ambient]
  rfl

theorem southNormalRotationCoordinates_symm_apply (t : ℝ) (q : Sphere 3)
    (v : SouthNormalModel) :
    (southNormalRotationCoordinates t q).symm v = southNormalFrame.ambientInverse q
      ((southRadialRotation t q).symm (southNormalFrame.ambient q v)) := by
  have hn : southNormalFrame.ambient q v ∈ (NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient q).rangeᗮ := by
    rw [← southNormalFrame_range]
    exact ⟨v, rfl⟩
  have hi : (southRadialRotation t q).symm (southNormalFrame.ambient q v) ∈
      (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient q).rangeᗮ := by
    apply (southRadialRotation_normal_iff t q _).mp
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hn
  apply (southNormalRotationCoordinates t q).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply southNormalFrame.ambient_injective q
  rw [southNormalRotationCoordinates_frame]
  change southNormalFrame.ambient q v = southRadialRotation t q
    (southNormalFrame.ambient q (southNormalFrame.ambientInverse q
      ((southRadialRotation t q).symm (southNormalFrame.ambient q v))))
  rw [southNormalFrame_reconstruct q _ hi, LinearIsometryEquiv.apply_symm_apply]

theorem contMDiff_southNormalRotationCoordinates :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : ℝ × Sphere 3 ↦ (southNormalRotationCoordinates p.1 p.2).toContinuousLinearMap) := by
  have he : (fun p : ℝ × Sphere 3 ↦
      (southNormalRotationCoordinates p.1 p.2).toContinuousLinearMap) =
      fun p ↦ (southNormalFrame.ambientInverse p.2).comp (southRadialFrame p.1 p.2) := by
    funext p
    apply ContinuousLinearMap.ext
    exact southNormalRotationCoordinates_apply p.1 p.2
  rw [he]
  exact (southNormalFrame.contMDiff_ambientInverse.comp contMDiff_snd).clm_comp
    contMDiff_southRadialFrame

theorem contMDiff_southRadialRotation_symm :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, V 8 →L[ℝ] V 8) ∞
      (fun p : ℝ × Sphere 3 ↦
        (southRadialRotation p.1 p.2).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  have h := realAdjoint.contDiff.contMDiff.comp contMDiff_southRadialRotation
  change ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, V 8 →L[ℝ] V 8) ∞
    (fun p : ℝ × Sphere 3 ↦
      ((southRadialRotation p.1 p.2).toContinuousLinearEquiv.toContinuousLinearMap).adjoint) at h
  simpa only [LinearIsometryEquiv.adjoint_eq_symm] using h

theorem contMDiff_southNormalRotationCoordinates_symm :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : ℝ × Sphere 3 ↦
        (southNormalRotationCoordinates p.1 p.2).symm.toContinuousLinearMap) := by
  have he : (fun p : ℝ × Sphere 3 ↦
      (southNormalRotationCoordinates p.1 p.2).symm.toContinuousLinearMap) =
      fun p ↦ (southNormalFrame.ambientInverse p.2).comp
        ((southRadialRotation p.1 p.2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (southNormalFrame.ambient p.2)) := by
    funext p
    apply ContinuousLinearMap.ext
    exact southNormalRotationCoordinates_symm_apply p.1 p.2
  rw [he]
  exact (southNormalFrame.contMDiff_ambientInverse.comp contMDiff_snd).clm_comp
    (contMDiff_southRadialRotation_symm.clm_comp
      (southNormalFrame.contMDiff_ambient.comp contMDiff_snd))

end NoExoticSixSphere.QuaternionicHopf
