import Wikipedia.NoExoticSixSphere.QuaternionicHopfNormalRotationCoordinates
import Wikipedia.NoExoticSixSphere.FiberCoordinateCollapse

/-!
# Actual fiber-coordinate changes from the rotated frame back to the raw frame

Conjugating the normal-coordinate family by its endpoint starts at the
identity. Both directions are jointly continuous on time, base, and fiber,
so this family can reparametrize the original open tube throughout.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

def southTubeFiberRotation (t : ℝ) (q : Sphere 3) : SouthNormalModel ≃L[ℝ] SouthNormalModel :=
  (southNormalRotationCoordinates (1 - t) q).trans (southNormalRotationCoordinates 1 q).symm

theorem southTubeFiberRotation_apply (t : ℝ) (q : Sphere 3) (v : SouthNormalModel) :
    southTubeFiberRotation t q v = (southNormalRotationCoordinates 1 q).symm
      (southNormalRotationCoordinates (1 - t) q v) := rfl

theorem southTubeFiberRotation_symm_apply (t : ℝ) (q : Sphere 3) (v : SouthNormalModel) :
    (southTubeFiberRotation t q).symm v = (southNormalRotationCoordinates (1 - t) q).symm
      (southNormalRotationCoordinates 1 q v) := rfl

theorem southTubeFiberRotation_zero (q : Sphere 3) :
    southTubeFiberRotation 0 q = ContinuousLinearEquiv.refl ℝ SouthNormalModel := by
  apply ContinuousLinearEquiv.ext
  funext v
  rw [southTubeFiberRotation_apply, sub_zero, ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem southTubeFiberRotation_frame (t : ℝ) (q : Sphere 3) (v : SouthNormalModel) :
    southRadialFrame 1 q (southTubeFiberRotation t q v) = southRadialFrame (1 - t) q v := by
  rw [← southNormalRotationCoordinates_frame, southTubeFiberRotation_apply,
    ContinuousLinearEquiv.apply_symm_apply, southNormalRotationCoordinates_frame]

theorem contMDiff_southTubeFiberRotation :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : ℝ × Sphere 3 ↦ (southTubeFiberRotation p.1 p.2).toContinuousLinearMap) := by
  have he : (fun p : ℝ × Sphere 3 ↦ (southTubeFiberRotation p.1 p.2).toContinuousLinearMap) =
      fun p ↦ (southNormalRotationCoordinates 1 p.2).symm.toContinuousLinearMap.comp
        (southNormalRotationCoordinates (1 - p.1) p.2).toContinuousLinearMap := by
    funext p
    apply ContinuousLinearMap.ext
    exact southTubeFiberRotation_apply p.1 p.2
  rw [he]
  have hl : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3))
      𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : ℝ × Sphere 3 ↦ (southNormalRotationCoordinates 1 p.2).symm.toContinuousLinearMap) :=
    contMDiff_southNormalRotationCoordinates_symm.comp
      (f := fun p : ℝ × Sphere 3 ↦ ((1 : ℝ), p.2))
      (contMDiff_const.prodMk contMDiff_snd)
  have hr : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3))
      𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : ℝ × Sphere 3 ↦
        (southNormalRotationCoordinates (1 - p.1) p.2).toContinuousLinearMap) :=
    contMDiff_southNormalRotationCoordinates.comp
      (f := fun p : ℝ × Sphere 3 ↦ (1 - p.1, p.2))
      ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd)
  exact hl.clm_comp hr

theorem contMDiff_southTubeFiberRotation_symm :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : ℝ × Sphere 3 ↦ (southTubeFiberRotation p.1 p.2).symm.toContinuousLinearMap) := by
  have he : (fun p : ℝ × Sphere 3 ↦
      (southTubeFiberRotation p.1 p.2).symm.toContinuousLinearMap) =
      fun p ↦ (southNormalRotationCoordinates (1 - p.1) p.2).symm.toContinuousLinearMap.comp
        (southNormalRotationCoordinates 1 p.2).toContinuousLinearMap := by
    funext p
    apply ContinuousLinearMap.ext
    exact southTubeFiberRotation_symm_apply p.1 p.2
  rw [he]
  have hl : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3))
      𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : ℝ × Sphere 3 ↦
        (southNormalRotationCoordinates (1 - p.1) p.2).symm.toContinuousLinearMap) :=
    contMDiff_southNormalRotationCoordinates_symm.comp
      (f := fun p : ℝ × Sphere 3 ↦ (1 - p.1, p.2))
      ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd)
  have hr : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3))
      𝓘(ℝ, SouthNormalModel →L[ℝ] SouthNormalModel) ∞
      (fun p : ℝ × Sphere 3 ↦ (southNormalRotationCoordinates 1 p.2).toContinuousLinearMap) :=
    contMDiff_southNormalRotationCoordinates.comp
      (f := fun p : ℝ × Sphere 3 ↦ ((1 : ℝ), p.2))
      (contMDiff_const.prodMk contMDiff_snd)
  exact hl.clm_comp hr

def southTubeFiberHomeomorph (p : I × Sphere 3) : SouthNormalModel ≃ₜ SouthNormalModel :=
  (southTubeFiberRotation p.1 p.2).toHomeomorph

theorem continuous_southTubeFiberHomeomorph :
    Continuous (fun p : (I × Sphere 3) × SouthNormalModel ↦ southTubeFiberHomeomorph p.1 p.2) := by
  change Continuous (fun p : (I × Sphere 3) × SouthNormalModel ↦
    (southTubeFiberRotation p.1.1 p.1.2).toContinuousLinearMap p.2)
  have h : Continuous (fun p : ℝ × Sphere 3 ↦
      (southTubeFiberRotation p.1 p.2).toContinuousLinearMap) :=
    contMDiff_southTubeFiberRotation.continuous
  have hj : Continuous (fun p : (I × Sphere 3) × SouthNormalModel ↦
      ((p.1.1 : ℝ), p.1.2)) :=
    (continuous_subtype_val.comp continuous_fst.fst).prodMk continuous_fst.snd
  have hh := h.comp hj
  have heval := hh.clm_apply (continuous_snd : Continuous
    (fun p : (I × Sphere 3) × SouthNormalModel ↦ p.2))
  simpa only [Function.comp_def] using heval

theorem continuous_southTubeFiberHomeomorph_symm :
    Continuous (fun p : (I × Sphere 3) × SouthNormalModel ↦
      (southTubeFiberHomeomorph p.1).symm p.2) := by
  change Continuous (fun p : (I × Sphere 3) × SouthNormalModel ↦
    (southTubeFiberRotation p.1.1 p.1.2).symm.toContinuousLinearMap p.2)
  have h : Continuous (fun p : ℝ × Sphere 3 ↦
      (southTubeFiberRotation p.1 p.2).symm.toContinuousLinearMap) :=
    contMDiff_southTubeFiberRotation_symm.continuous
  have hj : Continuous (fun p : (I × Sphere 3) × SouthNormalModel ↦
      ((p.1.1 : ℝ), p.1.2)) :=
    (continuous_subtype_val.comp continuous_fst.fst).prodMk continuous_fst.snd
  have hh := h.comp hj
  have heval := hh.clm_apply (continuous_snd : Continuous
    (fun p : (I × Sphere 3) × SouthNormalModel ↦ p.2))
  simpa only [Function.comp_def] using heval

end NoExoticSixSphere.QuaternionicHopf
