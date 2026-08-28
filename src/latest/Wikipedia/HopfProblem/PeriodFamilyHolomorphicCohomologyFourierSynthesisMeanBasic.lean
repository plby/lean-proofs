import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopySymbol
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisReconstruction

/-!
# Removing the actual Haar mean from the family Fourier sum

Deleting the zero-frequency coefficient subtracts its original constant
Fourier term. The coefficient is identified with the integral for the
original product probability Haar measure, so this is genuine mean removal
on the original torus, not a new choice of coordinates.
-/

noncomputable section

open MeasureTheory TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open RelativeHomotopy

variable {U : Opens ℂ} {c : Coefficients}

/-- Separating the zero term in the convergent original series subtracts
exactly the original zero coefficient. -/
theorem synthesis_removeZeroCoefficients (hc : SmoothRapidCoefficients U c)
    (x : U × UnitAddTorus (Fin 4)) :
    synthesis (removeZeroCoefficients c) x = synthesis c x - c 0 (x.1 : ℂ) := by
  have hsum := (summable_synthesisModes hc x).tsum_eq_add_tsum_ite (0 : Frequency)
  have hremove : synthesis (removeZeroCoefficients c) x =
      ∑' k : Frequency, if k = 0 then 0 else c k (x.1 : ℂ) * mFourier k x.2 := by
    simp only [synthesis, removeZeroCoefficients, ite_mul, zero_mul]
  rw [hremove, eq_sub_iff_add_eq]
  simpa only [synthesis, mFourier_zero, ContinuousMap.one_apply, mul_one, add_comm]
    using hsum.symm

/-- The literal zero Fourier coefficient is the original product-Haar integral. -/
theorem mFourierCoeff_zero_eq_haarIntegral {d : Type*} [Fintype d]
    (f : UnitAddTorus d → ℂ) :
    mFourierCoeff f 0 =
      ∫ t : UnitAddTorus d, f t ∂Measure.pi (fun _ : d => AddCircle.haarAddCircle) := by
  simp only [mFourierCoeff, neg_zero, mFourier_zero, ContinuousMap.one_apply, one_smul]
  rfl

/-- The supplied zero coefficient is the actual Haar mean of the original sum. -/
theorem haarIntegral_synthesis (hc : SmoothRapidCoefficients U c) (b : U) :
    (∫ t : UnitAddTorus (Fin 4), synthesis c (b, t)
      ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle)) = c 0 (b : ℂ) := by
  rw [← mFourierCoeff_zero_eq_haarIntegral]
  exact mFourierCoeff_synthesis hc b 0

/-- The zero-mode-deleted series has actual Haar mean zero. -/
theorem haarIntegral_removeZeroSynthesis (hc : SmoothRapidCoefficients U c) (b : U) :
    (∫ t : UnitAddTorus (Fin 4), synthesis (removeZeroCoefficients c) (b, t)
      ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle)) = 0 := by
  rw [haarIntegral_synthesis (removeZeroCoefficients_rapid hc), removeZeroCoefficients_zero]

/-- Deleting the zero mode removes the actual original Haar mean. -/
theorem synthesis_removeZero_eq_sub_haarIntegral (hc : SmoothRapidCoefficients U c)
    (b : U) (t : UnitAddTorus (Fin 4)) :
    synthesis (removeZeroCoefficients c) (b, t) = synthesis c (b, t) -
      ∫ s : UnitAddTorus (Fin 4), synthesis c (b, s)
        ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle) := by
  rw [haarIntegral_synthesis hc b]
  exact synthesis_removeZeroCoefficients hc (b, t)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
