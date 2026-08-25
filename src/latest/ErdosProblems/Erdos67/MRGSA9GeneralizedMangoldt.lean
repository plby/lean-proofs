import ErdosProblems.Erdos67.MRGSA9LowHigh
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Generalized Mangoldt coefficients for the GS A.10 identity

For an arithmetic function `a` with invertible constant coefficient, its
generalized Mangoldt coefficient is

`(a · log) * a⁻¹`.

The identities below are the exact Dirichlet-convolution algebra used in
equation (A.10) of the Granville--Soundararajan appendix.  They do not use an
Euler product or an analytic continuation: those estimates belong to the
subsequent contour step.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The real logarithm, embedded as a complex arithmetic function. -/
def gsComplexLog : ArithmeticFunction ℂ :=
  ⟨fun n ↦ (Real.log n : ℂ), by simp⟩

@[simp] theorem gsComplexLog_apply (n : ℕ) :
    gsComplexLog n = (Real.log n : ℂ) := rfl

/-- Pointwise logarithmic weighting of an arithmetic function. -/
def gsLogWeighted (a : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  a.pmul gsComplexLog

@[simp] theorem gsLogWeighted_apply (a : ArithmeticFunction ℂ) (n : ℕ) :
    gsLogWeighted a n = a n * (Real.log n : ℂ) := by
  simp [gsLogWeighted, ArithmeticFunction.pmul_apply]

/-- The generalized Mangoldt coefficient `Λ_a = (a·log) * a⁻¹`. -/
def gsGeneralizedMangoldt (a : ArithmeticFunction ℂ)
    (ha : Invertible (a 1)) : ArithmeticFunction ℂ :=
  gsLogWeighted a * ArithmeticFunction.dirichletInverse a ha

/-- Exact generalized Mangoldt convolution: `Λ_a * a = a·log`. -/
theorem gsGeneralizedMangoldt_mul_self
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1)) :
    gsGeneralizedMangoldt a ha * a = gsLogWeighted a := by
  rw [gsGeneralizedMangoldt, mul_assoc,
    ArithmeticFunction.dirichletInverse_mul_self, mul_one]

@[simp] theorem gsGeneralizedMangoldt_one
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1)) :
    gsGeneralizedMangoldt a ha 1 = 0 := by
  rw [gsGeneralizedMangoldt, ArithmeticFunction.mul_apply_one,
    gsLogWeighted_apply]
  simp

/-- The twice-differentiated convolution occurring in A.10. -/
theorem twice_gsGeneralizedMangoldt_mul_self
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1)) :
    gsGeneralizedMangoldt a ha * gsGeneralizedMangoldt a ha * a =
      gsGeneralizedMangoldt a ha * gsLogWeighted a := by
  rw [mul_assoc, gsGeneralizedMangoldt_mul_self]

/-- Coefficientwise form of the first generalized Mangoldt identity. -/
theorem sum_gsGeneralizedMangoldt_mul_self
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1)) (n : ℕ) :
    ∑ xy ∈ n.divisorsAntidiagonal,
        gsGeneralizedMangoldt a ha xy.1 * a xy.2 =
      a n * (Real.log n : ℂ) := by
  have h := congrFun
    (congrArg DFunLike.coe (gsGeneralizedMangoldt_mul_self a ha)) n
  simpa only [ArithmeticFunction.mul_apply, gsLogWeighted_apply] using h

/-- Fully expanded finite coefficient form of the double generalized
Mangoldt convolution.  This is the algebraic triple sum in A.10. -/
theorem twice_gsGeneralizedMangoldt_mul_self_apply
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1)) (n : ℕ) :
    (gsGeneralizedMangoldt a ha * gsGeneralizedMangoldt a ha * a) n =
      ∑ xc ∈ n.divisorsAntidiagonal,
        (∑ ab ∈ xc.1.divisorsAntidiagonal,
          gsGeneralizedMangoldt a ha ab.1 *
            gsGeneralizedMangoldt a ha ab.2) * a xc.2 := by
  simp only [ArithmeticFunction.mul_apply]

/-- The high-prime coefficient as an arithmetic function. -/
def gsA9HighArithmetic (f : ℕ → ℂ) (y : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else gsA9High f y n, by simp⟩

theorem gsA9HighArithmetic_apply_of_ne_zero (f : ℕ → ℂ) (y : ℕ)
    {n : ℕ} (hn : n ≠ 0) :
    gsA9HighArithmetic f y n = gsA9High f y n := by
  simp [gsA9HighArithmetic, hn]

@[simp] theorem gsA9HighArithmetic_one
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ) :
    gsA9HighArithmetic f y 1 = 1 := by
  simp [gsA9HighArithmetic, gsA9High, primeBandCoefficient,
    primeSupported_one, hmul.1]

/-- Canonical invertibility witness for the constant coefficient of the A.9
high-prime factor. -/
@[instance_reducible] def gsA9HighArithmeticInvertible
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ) :
    Invertible (gsA9HighArithmetic f y 1) :=
  Invertible.copy invertibleOne _ (gsA9HighArithmetic_one hmul y)

/-- The actual generalized Mangoldt coefficient of the common high factor. -/
def gsA9HighGeneralizedMangoldt
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ) :
    ArithmeticFunction ℂ :=
  gsGeneralizedMangoldt (gsA9HighArithmetic f y)
    (gsA9HighArithmeticInvertible hmul y)

/-- Actual-high-factor form of `Λ_ℓ * ℓ = ℓ·log`. -/
theorem gsA9HighGeneralizedMangoldt_mul_high
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ) :
    gsA9HighGeneralizedMangoldt hmul y * gsA9HighArithmetic f y =
      gsLogWeighted (gsA9HighArithmetic f y) := by
  exact gsGeneralizedMangoldt_mul_self _ _

/-- Actual-high-factor triple-convolution form used on the coefficient side
of A.10. -/
theorem twice_gsA9HighGeneralizedMangoldt_mul_high
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ) :
    gsA9HighGeneralizedMangoldt hmul y *
        gsA9HighGeneralizedMangoldt hmul y * gsA9HighArithmetic f y =
      gsA9HighGeneralizedMangoldt hmul y *
        gsLogWeighted (gsA9HighArithmetic f y) := by
  exact twice_gsGeneralizedMangoldt_mul_self _ _

end

end Erdos67.MRHalaszBands
