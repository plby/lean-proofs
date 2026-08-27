/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSieveLocal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The exact harmonic convolution behind the quantitative sieve sum

Division by the argument preserves Dirichlet convolution. Twisting the
Möbius--zeta inverse identity therefore gives the inverse of the harmonic
function, and hence the exact correction function for any arithmetic weight.
Quantitative absolute-sum and logarithmic-moment bounds are separate steps.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- Pointwise division by the natural argument, with the required zero at zero. -/
def divideByArgument (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n / (n : ℝ), by simp⟩

@[simp] theorem divideByArgument_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    divideByArgument f n = f n / (n : ℝ) := rfl

theorem divideByArgument_mul (f g : ArithmeticFunction ℝ) :
    divideByArgument (f * g) = divideByArgument f * divideByArgument g := by
  ext n
  simp only [divideByArgument_apply, ArithmeticFunction.mul_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hprod : d.1 * d.2 = n := (Nat.mem_divisorsAntidiagonal.mp hd).1
  rw [div_mul_div_comm, ← Nat.cast_mul, hprod]

@[simp] theorem divideByArgument_one :
    divideByArgument (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  by_cases hn : n = 1
  · subst n
    simp
  · simp [hn]

/-- The harmonic arithmetic function `n ↦ 1/n`. -/
def harmonicArithmetic : ArithmeticFunction ℝ :=
  divideByArgument (ζ : ArithmeticFunction ℝ)

/-- The inverse harmonic arithmetic function `n ↦ μ(n)/n`. -/
def mobiusHarmonicArithmetic : ArithmeticFunction ℝ :=
  divideByArgument (μ : ArithmeticFunction ℝ)

@[simp] theorem harmonicArithmetic_apply (n : ℕ) :
    harmonicArithmetic n = 1 / (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [harmonicArithmetic]
  · simp [harmonicArithmetic, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hn]

@[simp] theorem mobiusHarmonicArithmetic_apply (n : ℕ) :
    mobiusHarmonicArithmetic n = (μ n : ℝ) / (n : ℝ) := rfl

theorem mobiusHarmonicArithmetic_mul_harmonicArithmetic :
    mobiusHarmonicArithmetic * harmonicArithmetic = 1 := by
  rw [mobiusHarmonicArithmetic, harmonicArithmetic, ← divideByArgument_mul,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, divideByArgument_one]

/-- The correction coefficients to be bounded by their Euler product. -/
def harmonicCorrection (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f * mobiusHarmonicArithmetic

theorem harmonicCorrection_mul_harmonicArithmetic (f : ArithmeticFunction ℝ) :
    harmonicCorrection f * harmonicArithmetic = f := by
  rw [harmonicCorrection, mul_assoc,
    mobiusHarmonicArithmetic_mul_harmonicArithmetic, mul_one]

/-- The finite divisor identity is valid at every integer, including zero. -/
theorem eq_sum_harmonicCorrection (f : ArithmeticFunction ℝ) (n : ℕ) :
    f n = ∑ d ∈ n.divisorsAntidiagonal,
      harmonicCorrection f d.1 / (d.2 : ℝ) := by
  conv_lhs => rw [← harmonicCorrection_mul_harmonicArithmetic f]
  simp only [ArithmeticFunction.mul_apply, harmonicArithmetic_apply, div_eq_mul_inv,
    one_mul]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.harmonicCorrection_mul_harmonicArithmetic
