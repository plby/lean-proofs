import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeBasic

/-!
# The actual continuous Fourier synthesis

Absolute summability of the coefficients gives convergence in the Banach
space of continuous functions on the compact unit torus, and evaluation
identifies the resulting function with its pointwise Fourier series.
-/

noncomputable section

open UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable (c : (Fin 4 → ℤ) → ℂ)

/-- The series in the actual Banach space of continuous torus functions. -/
def continuousFourierSynthesis : C(UnitAddTorus (Fin 4), ℂ) :=
  ∑' k, c k • mFourier k

theorem summable_continuousFourierModes (hc : Summable c) :
    Summable (fun k : Fin 4 → ℤ => c k • mFourier k) := by
  apply Summable.of_norm
  simpa only [norm_smul, mFourier_norm, mul_one] using hc.norm

theorem continuousFourierSynthesis_hasSum (hc : Summable c) :
    HasSum (fun k => c k • mFourier k) (continuousFourierSynthesis c) :=
  (summable_continuousFourierModes c hc).hasSum

theorem continuousFourierSynthesis_hasSum_apply (hc : Summable c)
    (t : UnitAddTorus (Fin 4)) :
    HasSum (fun k => c k * mFourier k t) (continuousFourierSynthesis c t) := by
  simpa only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] using
    (ContinuousMap.evalCLM ℂ t).hasSum (continuousFourierSynthesis_hasSum c hc)

theorem continuousFourierSynthesis_apply (hc : Summable c) (t : UnitAddTorus (Fin 4)) :
    continuousFourierSynthesis c t = ∑' k, c k * mFourier k t :=
  (continuousFourierSynthesis_hasSum_apply c hc t).tsum_eq.symm

theorem continuousFourierSynthesis_lift (hc : Summable c) (x : Fin 4 → ℝ) :
    torusLift (continuousFourierSynthesis c) x =
      ∑' k, c k * mFourier k (torusQuotient x) :=
  continuousFourierSynthesis_apply c hc (torusQuotient x)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
