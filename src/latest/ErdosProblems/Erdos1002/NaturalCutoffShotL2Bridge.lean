import ErdosProblems.Erdos1002.PrimitiveShotL2
import ErdosProblems.Erdos1002.NaturalCutoffReconstructionReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The natural-cutoff reconstruction error in one Hilbert space

This file identifies the literal primitive resonance shot sum with its
`L²(AddCircle 1)` representative after pullback to `(0,1)`.  Consequently the
remaining natural-cutoff reconstruction estimate is exactly a norm convergence
statement in `UnitCircleL2`; there is no hidden choice of representatives.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos1002

noncomputable section

/-- The normalized reconstructed shot as an element of circle `L²`. -/
def normalizedReconstructedShotL2 (N : ℕ) : UnitCircleL2 :=
  ((Real.log (N : ℝ))⁻¹ : ℂ) • reconstructedShotL2 N

/-- Pulling the circle `L²` shot back to `(0,1)` gives the literal real shot
sum almost everywhere. -/
theorem unitCircleL2Pullback_reconstructedShot_ae (N : ℕ) :
    unitCircleL2Pullback (reconstructedShotL2 N) =ᵐ[uniform01Measure]
      fun alpha ↦ (reconstructedShotSum N alpha : ℂ) := by
  have hcoe :=
    measurePreserving_unitCircleMk_uniform01.quasiMeasurePreserving.ae
      (reconstructedShotL2_coe_ae N)
  have hIoo : ∀ᵐ alpha ∂uniform01Measure,
      alpha ∈ Ioo (0 : ℝ) 1 := by
    rw [uniform01Measure]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hcoe, hIoo] with alpha halpha hmem
  change
    (reconstructedShotL2 N : AddCircle (1 : ℝ) → ℂ)
        (alpha : AddCircle (1 : ℝ)) = _
  rw [halpha]
  rw [primitiveShotSumCircle_coe (show alpha ∈ Ioc (0 : ℝ) 1 from
    ⟨hmem.1, hmem.2.le⟩)]
  rfl

/-- The normalized circle representative agrees almost everywhere with the
manuscript's normalized reconstructed shot. -/
theorem unitCircleL2Pullback_normalizedReconstructedShot_ae (N : ℕ) :
    unitCircleL2Pullback (normalizedReconstructedShotL2 N)
        =ᵐ[uniform01Measure]
      normalizedReconstructedShotComplex N := by
  have hsmul := unitCircleL2Pullback_smul_ae
    ((Real.log (N : ℝ))⁻¹ : ℂ) (reconstructedShotL2 N)
  filter_upwards [hsmul, unitCircleL2Pullback_reconstructedShot_ae N] with
      alpha hscale hshot
  rw [normalizedReconstructedShotL2, hscale, hshot]
  unfold normalizedReconstructedShotComplex normalizedReconstructedShotSum
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- Exact Hilbert-space form of the remaining natural-cutoff error. -/
theorem eLpNorm_normalizedNaturalCutoff_sub_reconstructedShot_eq_enorm
    (N : ℕ+) :
    eLpNorm
        (normalizedNaturalCutoffPullback N -
          normalizedReconstructedShotComplex (N : ℕ))
        2 uniform01Measure =
      ‖normalizedNaturalCutoffReconstructionL2 N -
          normalizedReconstructedShotL2 (N : ℕ)‖ₑ := by
  calc
    eLpNorm
        (normalizedNaturalCutoffPullback N -
          normalizedReconstructedShotComplex (N : ℕ))
        2 uniform01Measure =
      eLpNorm
        (unitCircleL2Pullback (normalizedNaturalCutoffReconstructionL2 N) -
          unitCircleL2Pullback (normalizedReconstructedShotL2 (N : ℕ)))
        2 uniform01Measure := by
          apply eLpNorm_congr_ae
          filter_upwards
              [unitCircleL2Pullback_normalizedReconstructedShot_ae (N : ℕ)]
              with alpha hshot
          simp only [Pi.sub_apply, normalizedNaturalCutoffPullback]
          rw [hshot]
    _ = eLpNorm
        (unitCircleL2Pullback
          (normalizedNaturalCutoffReconstructionL2 N -
            normalizedReconstructedShotL2 (N : ℕ)))
        2 uniform01Measure := by
          apply eLpNorm_congr_ae
          exact (unitCircleL2Pullback_sub_ae
            (normalizedNaturalCutoffReconstructionL2 N)
            (normalizedReconstructedShotL2 (N : ℕ))).symm
    _ = ‖normalizedNaturalCutoffReconstructionL2 N -
          normalizedReconstructedShotL2 (N : ℕ)‖ₑ :=
      eLpNorm_unitCircleL2Pullback _

/-- It therefore suffices to prove the natural-cutoff comparison as ordinary
norm convergence in `UnitCircleL2`. -/
theorem tendsto_rotation_reconstruction_of_naturalCutoff_L2
    (hL2 : Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖normalizedNaturalCutoffReconstructionL2 N -
          normalizedReconstructedShotL2 (N : ℕ)‖)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        eLpNorm
          (normalizedRotationSum N - normalizedReconstructedShotSum N)
          2 uniform01Measure)
      atTop (nhds 0) := by
  apply tendsto_rotation_reconstruction_of_naturalCutoff_reconstruction
  have henorm : Tendsto
      (fun m : ℕ ↦
        ENNReal.ofReal
          (let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
           ‖normalizedNaturalCutoffReconstructionL2 N -
             normalizedReconstructedShotL2 (N : ℕ)‖))
      atTop (nhds 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL2
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using! h
  apply henorm.congr'
  filter_upwards with m
  let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
  rw [eLpNorm_normalizedNaturalCutoff_sub_reconstructedShot_eq_enorm]
  rw [ofReal_norm_eq_enorm]

end

end Erdos1002
