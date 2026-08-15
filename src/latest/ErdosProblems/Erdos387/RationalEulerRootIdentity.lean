/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalReciprocalRoots

/-!
# Rational Euler coefficients as reciprocal-root power sums

The bounded Euler product and the fixed rational Artin polynomial have the
same coefficients through the cutoff.  Their division-free logarithmic
derivatives therefore agree through that cutoff, yielding the exact Euler
sum / reciprocal-root power-sum identity.
-/

namespace Erdos387

open Polynomial PowerSeries
open scoped BigOperators PowerSeries

namespace RationalWeil

theorem coeff_finiteEulerProduct_eq_coeff_artinLPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    {N j : ℕ} (hjN : j ≤ N) :
    PowerSeries.coeff j
        (finiteEulerProduct
          (fun P : MonicIrreducibleLE (ZMod p) N ↦
            polynomialWeight coeff P.poly)) =
      PowerSeries.coeff j
        (artinLPolynomial coeff : PowerSeries ℂ) := by
  classical
  rw [finiteEulerProduct,
    coeff_localEulerProduct_polynomialWeight_eq_monicWeightSum coeff hjN,
    Polynomial.coeff_coe,
    coeff_artinLPolynomial_eq_monicWeightSum coeff hne]

theorem coeff_zero_finiteEulerProduct_polynomialWeight
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {N : ℕ} :
    PowerSeries.coeff 0
        (finiteEulerProduct
          (fun P : MonicIrreducibleLE (ZMod p) N ↦
            polynomialWeight coeff P.poly)) = 1 := by
  classical
  rw [finiteEulerProduct,
    coeff_localEulerProduct_polynomialWeight_eq_monicWeightSum coeff
      (Nat.zero_le N),
    monicWeightSum_zero]

theorem coeff_finiteEulerLogDerivative_polynomialWeight_eq_neg_powerSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    {N n : ℕ} (hnN : n ≤ N) (hn : n ≠ 0) :
    PowerSeries.coeff n
        (finiteEulerLogDerivative
          (fun P : MonicIrreducibleLE (ZMod p) N ↦
            polynomialWeight coeff P.poly)) =
      -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  let w : MonicIrreducibleLE (ZMod p) N → ℂ :=
    fun P ↦ polynomialWeight coeff P.poly
  calc
    PowerSeries.coeff n (finiteEulerLogDerivative w) =
        PowerSeries.coeff n (reciprocalRootLogDerivative
          (artinLPolynomial coeff).reverse.roots) := by
      exact coeff_logDerivative_eq_of_coeff_eq_up_to
        (X_mul_derivativeFun_finiteEulerProduct w)
        (X_mul_derivative_artinLPolynomial coeff hne)
        (constantCoeff_finiteEulerLogDerivative w)
        (constantCoeff_reciprocalRootLogDerivative _)
        (coeff_zero_finiteEulerProduct_polynomialWeight coeff)
        (fun j hj ↦
          coeff_finiteEulerProduct_eq_coeff_artinLPolynomial coeff hne hj)
        hnN
    _ = -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum :=
      coeff_reciprocalRootLogDerivative _ hn

theorem irreducible_sum_eq_neg_artinRootPowerSum
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    {N n : ℕ} (hnN : n ≤ N) (hn : n ≠ 0) :
    (∑ P : MonicIrreducibleLE (ZMod p) N,
      if P.poly.natDegree ∣ n then
        (P.poly.natDegree : ℂ) *
          polynomialWeight coeff P.poly ^
            (n / P.poly.natDegree)
      else 0) =
      -((artinLPolynomial coeff).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  rw [← coeff_finiteEulerLogDerivative hn]
  exact coeff_finiteEulerLogDerivative_polynomialWeight_eq_neg_powerSum
    coeff hne hnN hn

end RationalWeil

end Erdos387
