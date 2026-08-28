import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierSymbol
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential modes and their actual Dolbeault derivatives

The Fourier modes are the genuine complex exponentials of the period
frequency functional. Their real derivatives verify the Dolbeault symbol's
sign and normalization. Integral frequencies are periodic under the actual
period lattice.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex
open scoped BigOperators ContDiff

/-- The exponent of a Fourier mode as a continuous real-linear map. -/
noncomputable def frequencyExponentLinear (p : PeriodDomain) (v : Fin 4 → ℝ) :
    ComplexPlane₂ →L[ℝ] ℂ :=
  (2 * (Real.pi : ℂ) * I) •
    (Complex.ofRealCLM.comp (frequencyFunctional p v).toContinuousLinearMap)

@[simp]
theorem frequencyExponentLinear_apply (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) :
    frequencyExponentLinear p v z =
      2 * (Real.pi : ℂ) * I * (frequencyFunctional p v z : ℂ) := by
  simp [frequencyExponentLinear, smul_eq_mul]

/-- The exponential mode of a real period-coordinate frequency. -/
noncomputable def frequencyMode (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) : ℂ :=
  Complex.exp (frequencyExponentLinear p v z)

@[simp]
theorem frequencyMode_apply (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) :
    frequencyMode p v z =
      Complex.exp (2 * (Real.pi : ℂ) * I * (frequencyFunctional p v z : ℂ)) := by
  simp only [frequencyMode, frequencyExponentLinear_apply]

theorem contDiff_frequencyMode (p : PeriodDomain) (v : Fin 4 → ℝ) :
    ContDiff ℝ ∞ (frequencyMode p v) :=
  (frequencyExponentLinear p v).contDiff.cexp

theorem frequencyMode_hasFDerivAt (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) :
    HasFDerivAt (frequencyMode p v)
      (frequencyMode p v z • frequencyExponentLinear p v) z :=
  (frequencyExponentLinear p v).hasFDerivAt.cexp

theorem fderiv_frequencyMode_apply (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z w : ComplexPlane₂) :
    fderiv ℝ (frequencyMode p v) z w = frequencyMode p v z *
      (2 * (Real.pi : ℂ) * I * (frequencyFunctional p v w : ℂ)) := by
  rw [(frequencyMode_hasFDerivAt p v z).fderiv]
  simp only [smul_apply, smul_eq_mul, frequencyExponentLinear_apply]

/-- The exact symbol is obtained from the genuine real derivative of a mode. -/
theorem frequencyMode_dbar (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) (i : Fin 2) :
    (fderiv ℝ (frequencyMode p v) z (Pi.single i 1) +
      I * fderiv ℝ (frequencyMode p v) z (I • Pi.single i 1)) / 2 =
        dolbeaultSymbol p v i * frequencyMode p v z := by
  rw [fderiv_frequencyMode_apply, fderiv_frequencyMode_apply, dolbeaultSymbol_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

@[simp]
theorem frequencyMode_norm (p : PeriodDomain) (v : Fin 4 → ℝ) (z : ComplexPlane₂) :
    ‖frequencyMode p v z‖ = 1 := by
  simp [frequencyMode_apply, Complex.norm_exp]

theorem frequencyMode_ne_zero (p : PeriodDomain) (v : Fin 4 → ℝ)
    (z : ComplexPlane₂) : frequencyMode p v z ≠ 0 :=
  Complex.exp_ne_zero _

theorem frequencyMode_add (p : PeriodDomain) (v : Fin 4 → ℝ) (z w : ComplexPlane₂) :
    frequencyMode p v (z + w) = frequencyMode p v z * frequencyMode p v w := by
  simp only [frequencyMode, map_add, Complex.exp_add]

theorem frequencyFunctional_integer_period (p : PeriodDomain) (k n : Fin 4 → ℤ) :
    frequencyFunctional p (integerFrequency k) (p.periodVector n) =
      ((∑ j : Fin 4, k j * n j : ℤ) : ℝ) := by
  rw [← PeriodTorusTypeOneOne.periodEquiv_integer_eq_periodVector,
    frequencyFunctional_periodEquiv]
  simp [integerFrequency]

@[simp]
theorem frequencyMode_integer_period (p : PeriodDomain) (k n : Fin 4 → ℤ) :
    frequencyMode p (integerFrequency k) (p.periodVector n) = 1 := by
  rw [frequencyMode_apply, frequencyFunctional_integer_period]
  convert Complex.exp_int_mul_two_pi_mul_I (∑ j : Fin 4, k j * n j) using 1
  congr 1
  push_cast
  ring

theorem frequencyMode_add_integer_period (p : PeriodDomain) (k n : Fin 4 → ℤ)
    (z : ComplexPlane₂) :
    frequencyMode p (integerFrequency k) (z + p.periodVector n) =
      frequencyMode p (integerFrequency k) z := by
  rw [frequencyMode_add, frequencyMode_integer_period, mul_one]

theorem frequencyMode_add_lattice (p : PeriodDomain) (k : Fin 4 → ℤ)
    (z a : ComplexPlane₂) (ha : a ∈ p.lattice) :
    frequencyMode p (integerFrequency k) (z + a) =
      frequencyMode p (integerFrequency k) z := by
  obtain ⟨n, rfl⟩ := (p.mem_lattice_iff a).mp ha
  exact frequencyMode_add_integer_period p k n z

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
