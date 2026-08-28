import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeMonomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fréchet derivatives and uniform bounds for individual Fourier modes

The derivatives are actual real continuous linear maps on the covering
space. Their operator norms are bounded independently of the base point.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- A real coordinate, included in the complex numbers. -/
def fourierCoordinateCLM (j : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

@[simp]
theorem fourierCoordinateCLM_apply (j : Fin 4) (x : Fin 4 → ℝ) :
    fourierCoordinateCLM j x = (x j : ℂ) := rfl

theorem fourierCoordinateCLM_norm_le (j : Fin 4) :
    ‖fourierCoordinateCLM j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [fourierCoordinateCLM_apply, Complex.norm_real, one_mul] using
    norm_le_pi_norm x j

/-- The coordinatewise Fréchet derivative of an individual Fourier mode. -/
def fourierModeDerivative (a : ℂ) (k : Fin 4 → ℤ) (x : Fin 4 → ℝ) :
    (Fin 4 → ℝ) →L[ℝ] ℂ :=
  ∑ j, (((2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * a) *
    UnitAddTorus.mFourier k (torusQuotient x)) • fourierCoordinateCLM j

@[simp]
theorem fourierModeDerivative_apply (a : ℂ) (k : Fin 4 → ℤ) (x v : Fin 4 → ℝ) :
    fourierModeDerivative a k x v =
      ∑ j, (((2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * a) *
        UnitAddTorus.mFourier k (torusQuotient x)) * (v j : ℂ) := by
  simp only [fourierModeDerivative, sum_apply,
    smul_apply, fourierCoordinateCLM_apply, smul_eq_mul]

private def fourierFrequencyCLM (k : Fin 4 → ℤ) : (Fin 4 → ℝ) →L[ℝ] ℂ :=
  ∑ j, (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) • fourierCoordinateCLM j

private theorem fourierMode_eq_exp_frequency (k : Fin 4 → ℤ) (x : Fin 4 → ℝ) :
    UnitAddTorus.mFourier k (torusQuotient x) =
      Complex.exp (fourierFrequencyCLM k x) := by
  change UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) = _
  rw [mFourier_real_argument]
  congr 1
  simp only [fourierFrequencyCLM, sum_apply,
    smul_apply, fourierCoordinateCLM_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Each Fourier mode has the displayed actual real Fréchet derivative. -/
theorem hasFDerivAt_fourierMode (a : ℂ) (k : Fin 4 → ℤ) (x : Fin 4 → ℝ) :
    HasFDerivAt (fun y => a * UnitAddTorus.mFourier k (torusQuotient y))
      (fourierModeDerivative a k x) x := by
  have hderiv : a • (Complex.exp (fourierFrequencyCLM k x) • fourierFrequencyCLM k) =
      fourierModeDerivative a k x := by
    rw [← fourierMode_eq_exp_frequency]
    simp only [fourierFrequencyCLM, fourierModeDerivative, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  rw [← hderiv]
  simpa only [fourierMode_eq_exp_frequency] using
    ((fourierFrequencyCLM k).hasFDerivAt (x := x)).cexp.const_mul a

/-- A point-independent bound for the operator norm of a mode derivative. -/
theorem fourierModeDerivative_norm_le (a : ℂ) (k : Fin 4 → ℤ) (x : Fin 4 → ℝ) :
    ‖fourierModeDerivative a k x‖ ≤
      ∑ j, ‖(2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * a‖ := by
  unfold fourierModeDerivative
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul, norm_mul, mFourier_norm_apply, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (fourierCoordinateCLM_norm_le j)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
