import Wikipedia.SmoothSixDPoincare.MorseBeltFaceCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The finite coordinate of the handle collapse near its belt

In the original unit normal coordinate, the collapse first makes the actual
positive-face radial change and then expands the open disk to the vector
space. This composite is smooth on the open disk. Its differential at zero
is a positive scalar multiple of the identity.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]

theorem contDiff_beltFaceMap : ContDiff ℝ ∞ (beltFaceMap (N := N)) := by
  have hs : ContDiff ℝ ∞ (fun u : N => Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)).div_const _
  exact hs.smul contDiff_id

theorem hasFDerivAt_beltFaceMap_zero :
    HasFDerivAt (beltFaceMap (N := N))
      ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N) 0 := by
  have hs : ContDiff ℝ ∞ (fun u : N => Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)).div_const _
  have hd := (hs.differentiable (by simp) (0 : N)).hasFDerivAt.smul
    (hasFDerivAt_id (0 : N))
  change HasFDerivAt (fun u : N => (Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) • u) _ 0
  simpa [Pi.smul_def'] using hd

theorem hasFDerivAt_univUnitBall_symm_zero :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm : N → N)
      (ContinuousLinearMap.id ℝ N) 0 := by
  have hs : ContDiffAt ℝ ∞ (fun u : N => (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹) 0 := by
    apply ContDiffAt.inv
    · exact ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt.sqrt (by simp))
    · simp
  have hd := (hs.differentiableAt (by simp)).hasFDerivAt.smul (hasFDerivAt_id (0 : N))
  change HasFDerivAt (fun u : N => (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹ • u)
    (ContinuousLinearMap.id ℝ N) 0
  simpa [Pi.smul_def'] using hd

/-- Finite coordinate of the whole-attachment collapse in the native unit normal disk. -/
def beltCollapseCoordinate (u : N) : N :=
  OpenPartialHomeomorph.univUnitBall.symm (beltFaceMap u)

theorem beltCollapseCoordinate_zero : beltCollapseCoordinate (0 : N) = 0 := by
  rw [beltCollapseCoordinate, beltFaceMap_zero,
    OpenPartialHomeomorph.univUnitBall_symm_apply_zero]

theorem contDiffOn_beltCollapseCoordinate :
    ContDiffOn ℝ ∞ (beltCollapseCoordinate (N := N)) (ball 0 1) := by
  apply OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.comp
    contDiff_beltFaceMap.contDiffOn
  intro u hu
  exact mem_ball_zero_iff.mpr
    ((norm_beltFaceMap_lt_one_iff u).mpr (mem_ball_zero_iff.mp hu))

theorem hasFDerivAt_beltCollapseCoordinate_zero :
    HasFDerivAt (beltCollapseCoordinate (N := N))
      ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N) 0 := by
  have hout : HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm : N → N)
      (ContinuousLinearMap.id ℝ N) (beltFaceMap 0) := by
    rw [beltFaceMap_zero]
    exact hasFDerivAt_univUnitBall_symm_zero
  change HasFDerivAt
    ((OpenPartialHomeomorph.univUnitBall.symm : N → N) ∘ beltFaceMap) _ 0
  simpa only [ContinuousLinearMap.id_comp] using hout.comp 0 hasFDerivAt_beltFaceMap_zero

/-- Physical normal coordinates differ by the positive original handle radius. -/
theorem hasFDerivAt_scaled_beltCollapseCoordinate_zero (ρ : ℝ) :
    HasFDerivAt (fun u : N => beltCollapseCoordinate (ρ⁻¹ • u))
      (((Real.sqrt 2)⁻¹ * ρ⁻¹) • ContinuousLinearMap.id ℝ N) 0 := by
  have hout : HasFDerivAt (beltCollapseCoordinate (N := N))
      ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N) (ρ⁻¹ • (0 : N)) := by
    simpa only [smul_zero] using hasFDerivAt_beltCollapseCoordinate_zero (N := N)
  simpa only [Function.comp_def, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp, smul_smul, mul_comm] using
      hout.comp 0 ((hasFDerivAt_id (0 : N)).const_smul ρ⁻¹)

theorem scaled_beltCollapseCoordinate_factor_pos (ρ : ℝ) (hρ : 0 < ρ) :
    0 < (Real.sqrt 2)⁻¹ * ρ⁻¹ := by positivity

end Wikipedia.SmoothSixDPoincare.MorseHandle
