import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ErdosProblems.Erdos1002.NaturalCutoffShotL2Bridge
import Mathlib.Order.Filter.AtTopBot.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fourier reduction of the natural-cutoff shot error

The remaining reconstruction error is now represented by one canonical
element of `UnitCircleL2`.  This file records its exact Fourier expansion,
Parseval identity, symmetric finite-frequency exhaustion, and normalization.
These statements are unconditional and let subsequent arithmetic estimates
work only with finite Fourier polynomials before passing to the `L²` limit.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- The unnormalized difference between the natural-denominator Fourier
reconstruction and the literal primitive shot sum. -/
def naturalCutoffShotErrorL2 (N : ℕ+) : UnitCircleL2 :=
  naturalCutoffReconstructionL2 N (N : ℕ) - reconstructedShotL2 (N : ℕ)

/-- Its exact `n`-th Fourier coefficient. -/
def naturalCutoffShotErrorCoefficient (N : ℕ+) (n : ℤ) : ℂ :=
  fourierCoeff
      (naturalCutoffReconstructionL2 N (N : ℕ) :
        AddCircle (1 : ℝ) → ℂ) n -
    fourierCoeff
      (reconstructedShotL2 (N : ℕ) : AddCircle (1 : ℝ) → ℂ) n

theorem fourierCoeff_naturalCutoffShotErrorL2 (N : ℕ+) (n : ℤ) :
    fourierCoeff
        (naturalCutoffShotErrorL2 N : AddCircle (1 : ℝ) → ℂ) n =
      naturalCutoffShotErrorCoefficient N n := by
  rw [← fourierCoefficientCLM_apply]
  simp only [naturalCutoffShotErrorL2, map_sub,
    fourierCoefficientCLM_apply, naturalCutoffShotErrorCoefficient]

/-- Symmetric finite-frequency partial sum of the exact error. -/
def naturalCutoffShotErrorFourierPartialSum
    (N : ℕ+) (K : ℕ) : UnitCircleL2 :=
  ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    naturalCutoffShotErrorCoefficient N n • fourierLp 2 n

/-- The symmetric finite-frequency sums converge in circle `L²` to the
literal natural-cutoff shot error. -/
theorem tendsto_naturalCutoffShotErrorFourierPartialSum (N : ℕ+) :
    Tendsto (naturalCutoffShotErrorFourierPartialSum N) atTop
      (nhds (naturalCutoffShotErrorL2 N)) := by
  have hseries := hasSum_fourier_series_L2 (naturalCutoffShotErrorL2 N)
  have hcoeff :
      (fun n : ℤ ↦
          fourierCoeff
              (naturalCutoffShotErrorL2 N : AddCircle (1 : ℝ) → ℂ) n •
            (fourierLp 2 n : UnitCircleL2)) =
        fun n : ℤ ↦
          naturalCutoffShotErrorCoefficient N n •
            (fourierLp 2 n : UnitCircleL2) := by
    funext n
    rw [fourierCoeff_naturalCutoffShotErrorL2]
  rw [hcoeff] at hseries
  have h := hseries.comp (Finset.tendsto_Icc_neg (R := ℤ))
  simpa only [naturalCutoffShotErrorFourierPartialSum] using! h

/-- Parseval in the exact norm form used by the window estimate. -/
theorem tsum_sq_naturalCutoffShotErrorCoefficient (N : ℕ+) :
    (∑' n : ℤ, ‖naturalCutoffShotErrorCoefficient N n‖ ^ 2) =
      ‖naturalCutoffShotErrorL2 N‖ ^ 2 := by
  let f : UnitCircleL2 := naturalCutoffShotErrorL2 N
  have hparseval := tsum_sq_fourierCoeff f
  have hinner := congrArg RCLike.re
    (@L2.inner_def (AddCircle (1 : ℝ)) ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at hinner
  · simp only [← norm_sq_eq_re_inner] at hinner
    calc
      (∑' n : ℤ, ‖naturalCutoffShotErrorCoefficient N n‖ ^ 2) =
          ∑' n : ℤ, ‖fourierCoeff
            (naturalCutoffShotErrorL2 N : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2 := by
        apply tsum_congr
        intro n
        rw [fourierCoeff_naturalCutoffShotErrorL2]
      _ = ∫ x : AddCircle (1 : ℝ), ‖(f : AddCircle (1 : ℝ) → ℂ) x‖ ^ 2
          ∂AddCircle.haarAddCircle := by
        simpa only [f] using! hparseval
      _ = ‖f‖ ^ 2 := hinner.symm
      _ = ‖naturalCutoffShotErrorL2 N‖ ^ 2 := rfl
  · exact L2.integrable_inner f f

/-- Exact finite Parseval identity for every symmetric partial sum. -/
theorem norm_naturalCutoffShotErrorFourierPartialSum_sq
    (N : ℕ+) (K : ℕ) :
    ‖naturalCutoffShotErrorFourierPartialSum N K‖ ^ 2 =
      ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ‖naturalCutoffShotErrorCoefficient N n‖ ^ 2 := by
  unfold naturalCutoffShotErrorFourierPartialSum
  simpa using!
    (orthonormal_fourier.orthogonalFamily.norm_sum
      (naturalCutoffShotErrorCoefficient N)
      (Finset.Icc (-(K : ℤ)) (K : ℤ)))

/-- Any uniform bound proved for all finite symmetric Fourier truncations
passes to the actual `L²` error. -/
theorem norm_naturalCutoffShotErrorL2_le_of_partialSums
    (N : ℕ+) {B : ℝ}
    (hB : ∀ K : ℕ, ‖naturalCutoffShotErrorFourierPartialSum N K‖ ≤ B) :
    ‖naturalCutoffShotErrorL2 N‖ ≤ B := by
  have hnorm : Tendsto
      (fun K : ℕ ↦ ‖naturalCutoffShotErrorFourierPartialSum N K‖)
      atTop (nhds ‖naturalCutoffShotErrorL2 N‖) :=
    (continuous_norm.tendsto _).comp
      (tendsto_naturalCutoffShotErrorFourierPartialSum N)
  exact le_of_tendsto hnorm (Eventually.of_forall hB)

/-- The normalized Hilbert-space error is literally the inverse-log scalar
multiple of the unnormalized error. -/
theorem normalizedNaturalCutoff_sub_normalizedReconstructedShotL2
    (N : ℕ+) :
    normalizedNaturalCutoffReconstructionL2 N -
        normalizedReconstructedShotL2 (N : ℕ) =
      ((Real.log (N : ℝ))⁻¹ : ℂ) • naturalCutoffShotErrorL2 N := by
  simp only [normalizedNaturalCutoffReconstructionL2,
    normalizedReconstructedShotL2, naturalCutoffShotErrorL2, smul_sub]

/-- For `N ≥ 2`, normalization divides the exact error norm by `log N`. -/
theorem norm_normalizedNaturalCutoff_sub_normalizedReconstructedShotL2
    {N : ℕ+} (hN : 2 ≤ (N : ℕ)) :
    ‖normalizedNaturalCutoffReconstructionL2 N -
        normalizedReconstructedShotL2 (N : ℕ)‖ =
      ‖naturalCutoffShotErrorL2 N‖ / Real.log (N : ℝ) := by
  rw [normalizedNaturalCutoff_sub_normalizedReconstructedShotL2, norm_smul]
  have hNR : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  ring

/-- Final reconstruction reduction in the manuscript's unnormalized form:
it is enough to prove that the exact window error is `o(log N)` in circle
`L²`. -/
theorem tendsto_rotation_reconstruction_of_windowError_sublog
    (hwindow : Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 2, by omega⟩
        ‖naturalCutoffShotErrorL2 N‖ / Real.log (N : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        eLpNorm
          (normalizedRotationSum N - normalizedReconstructedShotSum N)
          2 uniform01Measure)
      atTop (nhds 0) := by
  apply tendsto_rotation_reconstruction_of_naturalCutoff_L2
  rw [← (Filter.tendsto_add_atTop_iff_nat 1)]
  apply hwindow.congr'
  filter_upwards with m
  let N : ℕ+ := ⟨m + 2, by omega⟩
  have hN : 2 ≤ (N : ℕ) := by simp [N]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using!
    (norm_normalizedNaturalCutoff_sub_normalizedReconstructedShotL2
      (N := N) hN).symm

end

end Erdos1002
