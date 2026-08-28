import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesMode
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Actual joint derivatives of parameter-dependent Fourier modes

Each mode is the literal product of its parameter coefficient and the
original unit-torus character. Its joint real Fréchet derivative uses
the actual coefficient derivative and the already proved actual
character derivative. No convergence or derivative of a sum is assumed.
-/

noncomputable section

open UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification

/-- A literal Fourier mode with its original varying parameter coefficient. -/
def jointFourierMode (c : (Fin 4 → ℤ) → ℂ → ℂ) (k : Fin 4 → ℤ)
    (x : ℂ × (Fin 4 → ℝ)) : ℂ :=
  c k x.1 * mFourier k (torusQuotient x.2)

/-- The actual product-rule derivative on the original parameter and real covering vector. -/
def jointFourierModeDerivative (c : (Fin 4 → ℤ) → ℂ → ℂ) (k : Fin 4 → ℤ)
    (x : ℂ × (Fin 4 → ℝ)) : (ℂ × (Fin 4 → ℝ)) →L[ℝ] ℂ :=
  c k x.1 • ((fourierModeDerivative 1 k x.2).comp
    (ContinuousLinearMap.snd ℝ ℂ (Fin 4 → ℝ))) +
  mFourier k (torusQuotient x.2) • ((fderiv ℝ (c k) x.1).comp
    (ContinuousLinearMap.fst ℝ ℂ (Fin 4 → ℝ)))

/-- The original varying mode has the displayed genuine joint derivative. -/
theorem hasFDerivAt_jointFourierMode (c : (Fin 4 → ℤ) → ℂ → ℂ) (k : Fin 4 → ℤ)
    (x : ℂ × (Fin 4 → ℝ)) (hc : DifferentiableAt ℝ (c k) x.1) :
    HasFDerivAt (jointFourierMode c k) (jointFourierModeDerivative c k x) x := by
  have hb : HasFDerivAt (fun y : ℂ × (Fin 4 → ℝ) => c k y.1)
      ((fderiv ℝ (c k) x.1).comp (ContinuousLinearMap.fst ℝ ℂ (Fin 4 → ℝ))) x :=
    hc.hasFDerivAt.comp x (ContinuousLinearMap.fst ℝ ℂ (Fin 4 → ℝ)).hasFDerivAt
  have ht : HasFDerivAt (fun y : ℂ × (Fin 4 → ℝ) => mFourier k (torusQuotient y.2))
      ((fourierModeDerivative 1 k x.2).comp (ContinuousLinearMap.snd ℝ ℂ (Fin 4 → ℝ))) x := by
    simpa only [one_mul, Function.comp_def] using
      (hasFDerivAt_fourierMode 1 k x.2).comp x
        (ContinuousLinearMap.snd ℝ ℂ (Fin 4 → ℝ)).hasFDerivAt
  exact hb.mul ht

/-- In a fixed joint direction the derivative is the same original
Fourier character times the literal parameter and frequency derivatives. -/
theorem jointFourierModeDerivative_apply (c : (Fin 4 → ℤ) → ℂ → ℂ) (k : Fin 4 → ℤ)
    (x v : ℂ × (Fin 4 → ℝ)) :
    jointFourierModeDerivative c k x v =
      (fderiv ℝ (c k) x.1 v.1 +
        ∑ j : Fin 4, (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
          (v.2 j : ℂ) * c k x.1) * mFourier k (torusQuotient x.2) := by
  change c k x.1 * fourierModeDerivative 1 k x.2 v.2 +
    mFourier k (torusQuotient x.2) * fderiv ℝ (c k) x.1 v.1 = _
  rw [fourierModeDerivative_apply]
  simp only [mul_one, add_mul, Finset.mul_sum, Finset.sum_mul]
  rw [add_comm]
  apply congrArg₂ (fun a b : ℂ => a + b)
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
