/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalStepanovLinear
import Waring.Analytic.StepanovHasseFrobenius

/-!
# Rational Stepanov auxiliary polynomial

The high rational monomial is packaged as one Frobenius expansion, so every
Hasse derivative below the half-extension spacing treats it as a constant.
On a full-trace fiber, multiplying by the `(p-1)`-st power of the low
denominator turns the resulting value into a common high-denominator factor
times the reduced polynomial from `RationalStepanovLinear`.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators
open Waring.Analytic.Stepanov

namespace RationalStepanov

/-- One term of the rational auxiliary polynomial.  The inner expansion of
the centered monomial makes its local order a multiple of the full extension
cardinality while retaining the value `(x-pole)^k` at extension points. -/
noncomputable def rationalAuxiliaryTerm
    {E : Type*} [Field E] (p h : ℕ) (pole : E) (i k : ℕ)
    (e lowN lowD : E[X]) : E[X] :=
  e * expand E (p ^ (h + 3))
    (lowN ^ i * lowD ^ (p - 1 - i) *
      expand E (p ^ (h + 3)) ((X - C pole) ^ k))

/-- The complete rational Stepanov auxiliary polynomial. -/
noncomputable def rationalAuxiliaryPolynomial
    {E : Type*} [Field E] (p h : ℕ) (pole : E)
    (lowN lowD : E[X]) (a : AuxiliaryCoefficients E p h) : E[X] :=
  ∑ i : Fin p, ∑ k : Fin (K p h + 1),
    rationalAuxiliaryTerm p h pole i k
      (auxiliaryCoefficientPolynomial a i k) lowN lowD

/-- At a point fixed by the full extension Frobenius, a low Hasse derivative
of one auxiliary term has the expected high-block value. -/
theorem eval_hasseDeriv_rationalAuxiliaryTerm
    {E : Type*} [Field E] {p h r i k : ℕ} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (x pole : E) (e lowN lowD : E[X])
    (hr : r < p ^ (h + 3))
    (hxpow : x ^ (p ^ (2 * (h + 3))) = x) :
    (hasseDeriv r
      (rationalAuxiliaryTerm p h pole i k e lowN lowD)).eval x =
      (hasseDeriv r e).eval x *
        (lowN.eval (x ^ (p ^ (h + 3))) ^ i *
          lowD.eval (x ^ (p ^ (h + 3))) ^ (p - 1 - i) *
            (x - pole) ^ k) := by
  unfold rationalAuxiliaryTerm
  rw [Waring.Analytic.Stepanov.eval_hasseDeriv_mul_expand_pow
    hp.pos x e _ hr]
  simp only [eval_mul, eval_pow, expand_eval, eval_sub, eval_X, eval_C]
  have hpow : (x ^ (p ^ (h + 3))) ^ (p ^ (h + 3)) = x := by
    rw [← pow_mul, ← pow_add]
    simpa only [show (h + 3) + (h + 3) = 2 * (h + 3) by omega]
      using hxpow
  rw [hpow]

/-- Evaluation of the high numerator is evaluation of the low numerator at
the half-extension Frobenius power. -/
theorem eval_highRationalNumerator_eq
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) (x : E) :
    (highRationalNumerator p m A B).eval x =
      (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) :=
  eval_highRationalNumerator p m A B x

/-- The denominator-cleared algebraic relation between the low and high
halves on a full rational trace fiber. -/
theorem eval_high_mul_low_eq_of_fullRationalTrace
    {E : Type*} [Field E] (p m : ℕ) (A B : E[X])
    (x c : E)
    (hlow : (lowRationalDenominator p m B).eval x ≠ 0)
    (hhigh : (highRationalDenominator p m B).eval x ≠ 0)
    (htrace :
      (fullRationalNumerator p m A B).eval x *
          ((fullRationalDenominator p m B).eval x)⁻¹ = c) :
    (highRationalNumerator p m A B).eval x *
        (lowRationalDenominator p m B).eval x =
      (c * (lowRationalDenominator p m B).eval x -
          (lowRationalNumerator p m A B).eval x) *
        (highRationalDenominator p m B).eval x := by
  rw [eval_fullRationalNumerator, eval_fullRationalDenominator,
    ← eval_highRationalNumerator_eq,
    ← eval_highRationalDenominator] at htrace
  field_simp [hlow, hhigh] at htrace
  calc
    (highRationalNumerator p m A B).eval x *
          (lowRationalDenominator p m B).eval x =
        ((lowRationalNumerator p m A B).eval x *
            (highRationalDenominator p m B).eval x +
          (highRationalNumerator p m A B).eval x *
            (lowRationalDenominator p m B).eval x) -
          (lowRationalNumerator p m A B).eval x *
            (highRationalDenominator p m B).eval x := by ring
    _ = ((highRationalDenominator p m B).eval x *
            (lowRationalDenominator p m B).eval x * c) -
          (lowRationalNumerator p m A B).eval x *
            (highRationalDenominator p m B).eval x := by rw [htrace]
    _ = (c * (lowRationalDenominator p m B).eval x -
          (lowRationalNumerator p m A B).eval x) *
        (highRationalDenominator p m B).eval x := by ring

/-- Homogeneous denominator clearing for one high rational monomial. -/
theorem homogeneous_high_term_mul_low_pow
    {E : Type*} [Field E] {p i : ℕ} (hi : i < p)
    (de hn hd low w center : E) (hrel : hn * low = w * hd) :
    (de * (hn ^ i * hd ^ (p - 1 - i) * center)) * low ^ (p - 1) =
      hd ^ (p - 1) *
        (de * (w ^ i * low ^ (p - 1 - i) * center)) := by
  have hi' : i ≤ p - 1 := by omega
  have hsplit : p - 1 = i + (p - 1 - i) := by omega
  have hpowers : hn ^ i * low ^ i = w ^ i * hd ^ i := by
    rw [← mul_pow, hrel, mul_pow]
  have hlowPow : low ^ (p - 1) = low ^ i * low ^ (p - 1 - i) := by
    exact (congrArg (fun n : ℕ => low ^ n) hsplit).trans (pow_add low _ _)
  have hhighPow : hd ^ (p - 1) = hd ^ i * hd ^ (p - 1 - i) := by
    exact (congrArg (fun n : ℕ => hd ^ n) hsplit).trans (pow_add hd _ _)
  rw [hlowPow, hhighPow]
  calc
    (de * (hn ^ i * hd ^ (p - 1 - i) * center)) *
          (low ^ i * low ^ (p - 1 - i)) =
        de * (hn ^ i * low ^ i) * hd ^ (p - 1 - i) *
          low ^ (p - 1 - i) * center := by ring
    _ = de * (w ^ i * hd ^ i) * hd ^ (p - 1 - i) *
          low ^ (p - 1 - i) * center := by rw [hpowers]
    _ = (hd ^ i * hd ^ (p - 1 - i)) *
        (de * (w ^ i * low ^ (p - 1 - i) * center)) := by ring

/-- A reduced polynomial value controls the corresponding full auxiliary
Hasse derivative on a trace fiber. -/
theorem eval_hasseDeriv_rationalAuxiliaryPolynomial_mul_lowDen
    {E : Type*} [Field E] {p h r : ℕ} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (x c pole : E)
    (lowN lowD highN highD : E[X])
    (a : AuxiliaryCoefficients E p h)
    (hr : r < p ^ (h + 3))
    (hxpow : x ^ (p ^ (2 * (h + 3))) = x)
    (hhighN : highN.eval x = lowN.eval (x ^ (p ^ (h + 3))))
    (hhighD : highD.eval x = lowD.eval (x ^ (p ^ (h + 3))))
    (hrel : highN.eval x * lowD.eval x =
      (c * lowD.eval x - lowN.eval x) * highD.eval x) :
    (hasseDeriv r
      (rationalAuxiliaryPolynomial p h pole lowN lowD a)).eval x *
        (lowD.eval x) ^ (p - 1) =
      (highD.eval x) ^ (p - 1) *
        (rationalReducedConditionPolynomial
          p h c pole r lowN lowD a).eval x := by
  change (evalRingHom x)
      (hasseDeriv r
        (rationalAuxiliaryPolynomial p h pole lowN lowD a)) *
          lowD.eval x ^ (p - 1) = _
  simp only [rationalAuxiliaryPolynomial,
    rationalReducedConditionPolynomial, map_sum,
    eval_finsetSum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hiMem
  apply Finset.sum_congr rfl
  intro k hkMem
  change (hasseDeriv r
      (rationalAuxiliaryTerm p h pole (i : ℕ) (k : ℕ)
        (auxiliaryCoefficientPolynomial a i k) lowN lowD)).eval x *
        lowD.eval x ^ (p - 1) = _
  rw [eval_hasseDeriv_rationalAuxiliaryTerm hp x pole
    (auxiliaryCoefficientPolynomial a i k) lowN lowD hr hxpow,
    rationalReducedTerm, eval_mul, eval_mul, eval_mul, eval_pow,
    eval_sub, eval_mul, eval_C, eval_pow, eval_pow, eval_sub, eval_X,
    eval_C, ← hhighN, ← hhighD]
  simpa only [mul_assoc] using
    (homogeneous_high_term_mul_low_pow i.isLt
      (eval x (hasseDeriv r (auxiliaryCoefficientPolynomial a i k)))
      (highN.eval x) (highD.eval x) (lowD.eval x)
      (c * lowD.eval x - lowN.eval x) ((x - pole) ^ (k : ℕ)) hrel)

/-- A kernel family gives all required low Hasse vanishings on a rational
trace fiber. -/
theorem hasseDeriv_rationalAuxiliaryPolynomial_eval_eq_zero
    {E : Type*} [Field E] {p h s : ℕ} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (c pole : E)
    {lowN lowD highN highD : E[X]}
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    {a : AuxiliaryCoefficients E p h}
    (ha : rationalReducedConditionLinear
      p h s c pole lowN lowD a = 0)
    {x : E} (hxpow : x ^ (p ^ (2 * (h + 3))) = x)
    (hlow : lowD.eval x ≠ 0)
    (hhighN : highN.eval x = lowN.eval (x ^ (p ^ (h + 3))))
    (hhighD : highD.eval x = lowD.eval (x ^ (p ^ (h + 3))))
    (hrel : highN.eval x * lowD.eval x =
      (c * lowD.eval x - lowN.eval x) * highD.eval x)
    {r : ℕ} (hr : r < R p h) :
    (hasseDeriv r
      (rationalAuxiliaryPolynomial p h pole lowN lowD a)).eval x = 0 := by
  have hrpow : r < p ^ (h + 3) := hr.trans (R_lt_pow hp)
  have hred := rationalReducedConditionPolynomial_eq_zero_of_linear_eq_zero
    hp.pos c pole hN hD ha hr
  have hidentity := eval_hasseDeriv_rationalAuxiliaryPolynomial_mul_lowDen
    hp x c pole lowN lowD highN highD a hrpow hxpow hhighN hhighD hrel
  rw [hred, eval_zero, mul_zero] at hidentity
  exact (mul_eq_zero.mp hidentity).resolve_right (pow_ne_zero _ hlow)

end RationalStepanov

end Erdos387
