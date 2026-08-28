import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial quotients for finite scalar divisors

The positive and negative parts of an integer-valued finite divisor give
two monic polynomials. Their quotient is the literal factorized rational
function, including its totalized values at zeros and poles. No analytic
continuation or rationality assumption is used in this construction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar

open scoped BigOperators Polynomial

/-- The polynomial made from the positive part of a finite divisor. -/
def divisorNumerator (d : ℂ → ℤ) (hd : d.HasFiniteSupport) : Polynomial ℂ :=
  ∏ u ∈ hd.toFinset, (Polynomial.X - Polynomial.C u) ^ (d u).toNat

/-- The polynomial made from the negative part of a finite divisor. -/
def divisorDenominator (d : ℂ → ℤ) (hd : d.HasFiniteSupport) : Polynomial ℂ :=
  ∏ u ∈ hd.toFinset, (Polynomial.X - Polynomial.C u) ^ (-d u).toNat

theorem divisorNumerator_monic (d : ℂ → ℤ) (hd : d.HasFiniteSupport) :
    (divisorNumerator d hd).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro u hu
  exact (Polynomial.monic_X_sub_C u).pow _

theorem divisorDenominator_monic (d : ℂ → ℤ) (hd : d.HasFiniteSupport) :
    (divisorDenominator d hd).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro u hu
  exact (Polynomial.monic_X_sub_C u).pow _

theorem divisorNumerator_ne_zero (d : ℂ → ℤ) (hd : d.HasFiniteSupport) :
    divisorNumerator d hd ≠ 0 :=
  (divisorNumerator_monic d hd).ne_zero

theorem divisorDenominator_ne_zero (d : ℂ → ℤ) (hd : d.HasFiniteSupport) :
    divisorDenominator d hd ≠ 0 :=
  (divisorDenominator_monic d hd).ne_zero

@[simp] theorem divisorNumerator_eval (d : ℂ → ℤ) (hd : d.HasFiniteSupport) (z : ℂ) :
    (divisorNumerator d hd).eval z = ∏ u ∈ hd.toFinset, (z - u) ^ (d u).toNat := by
  simp [divisorNumerator, Polynomial.eval_prod]

@[simp] theorem divisorDenominator_eval (d : ℂ → ℤ) (hd : d.HasFiniteSupport)
    (z : ℂ) :
    (divisorDenominator d hd).eval z = ∏ u ∈ hd.toFinset, (z - u) ^ (-d u).toNat := by
  simp [divisorDenominator, Polynomial.eval_prod]

private theorem zpow_eq_positive_div_negative (z : ℂ) (n : ℤ) :
    z ^ n = z ^ n.toNat / z ^ (-n).toNat := by
  cases n <;> simp

/-- Splitting each integer exponent into its positive and negative parts
identifies the finite divisor product with a quotient of actual polynomials. -/
theorem factorizedRational_eq_divisorQuotient
    (d : ℂ → ℤ) (hd : d.HasFiniteSupport) (z : ℂ) :
    (∏ᶠ u, (· - u) ^ d u) z =
      (divisorNumerator d hd).eval z / (divisorDenominator d hd).eval z := by
  rw [Function.FactorizedRational.finprod_eq_fun hd]
  change (∏ᶠ u, (z - u) ^ d u) = _
  have hsupport : (fun u => (z - u) ^ d u).mulSupport ⊆ hd.toFinset := by
    intro u hu
    by_contra hnot
    have hzero : d u = 0 := by
      by_contra hne
      exact hnot (hd.mem_toFinset.mpr hne)
    simp [Function.mem_mulSupport, hzero] at hu
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupport,
    divisorNumerator_eval, divisorDenominator_eval, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl (fun u _ => zpow_eq_positive_div_negative (z - u) (d u))

/-- An arbitrary scalar multiple of the finite divisor product has a
polynomial-quotient presentation with a nonzero denominator polynomial. -/
theorem exists_polynomial_quotient_const_mul_factorizedRational
    (c : ℂ) (d : ℂ → ℤ) (hd : d.HasFiniteSupport) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      ∀ z : ℂ, c * (∏ᶠ u, (· - u) ^ d u) z = P.eval z / Q.eval z := by
  refine ⟨Polynomial.C c * divisorNumerator d hd, divisorDenominator d hd,
    divisorDenominator_ne_zero d hd, ?_⟩
  intro z
  rw [factorizedRational_eq_divisorQuotient d hd z]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]

/-- In particular, the finite divisor product itself is a quotient of
two monic, nonzero polynomials. -/
theorem exists_polynomial_quotient_factorizedRational
    (d : ℂ → ℤ) (hd : d.HasFiniteSupport) :
    ∃ P Q : Polynomial ℂ, P.Monic ∧ Q.Monic ∧ P ≠ 0 ∧ Q ≠ 0 ∧
      ∀ z : ℂ, (∏ᶠ u, (· - u) ^ d u) z = P.eval z / Q.eval z :=
  ⟨divisorNumerator d hd, divisorDenominator d hd,
    divisorNumerator_monic d hd, divisorDenominator_monic d hd,
    divisorNumerator_ne_zero d hd, divisorDenominator_ne_zero d hd,
    factorizedRational_eq_divisorQuotient d hd⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar
