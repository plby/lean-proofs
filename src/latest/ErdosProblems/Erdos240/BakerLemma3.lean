/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.AlgebraicLiouville
import ErdosProblems.Erdos240.BakerParameters
import ErdosProblems.Erdos240.ComplexTaylor
import ErdosProblems.Erdos240.DeltaPower
import ErdosProblems.Erdos240.EmbeddingProduct
import ErdosProblems.Erdos240.ExponentialPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The analytic and Liouville core of van der Poorten--Loxton Lemma 3

This file packages the part of Lemma 3 on pp. 43--44 of van der Poorten and
Loxton that is independent of the still-missing coefficient construction and
denominator-clearing theorem for powers of Tijdeman's polynomial.

The definitions below retain the source's exact normalization.  An index has
the four kinds of coordinates denoted there by
`lambda_{-1}, lambda_0, lambda_1, ..., lambda_n`.  The distinguished last
logarithm is split off, and

`gamma_r = lambda_r - b_r * lambda_n / b_n`.

Thus the exponent in `g` is the exponent in `f` plus

`lambda_n / b_n * (b_1 log alpha_1 + ... + b_n log alpha_n)`.

The closeness theorem is consequently an exact termwise exponential-remainder
bound.  The last section transfers either an algebraic-integer norm bound or a
finite embedding-product bound across this small error.  Future code need only
supply the algebraic-integrality certificate produced by the strengthened
version of Lemma 1.
-/

open scoped BigOperators NumberField Polynomial

noncomputable section

namespace Erdos240.BakerLemma3

open Finset
open DeltaPower

/-- Coordinate data needed by the source auxiliary functions. -/
structure SourceCoordinates (oldRank : ℕ) (I : Type*) where
  shift : I → ℕ
  deltaIndex : I → ℕ
  oldExponent : I → Fin oldRank → ℕ
  lastExponent : I → ℕ

/-- The linear form in the chosen complex logarithms. -/
def logForm {oldRank : ℕ}
    (b : Fin oldRank → ℤ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (logAlphaLast : ℂ) : ℂ :=
  ∑ r, (b r : ℂ) * logAlpha r + (bLast : ℂ) * logAlphaLast

/-- The normalized exponent `gamma_r` from the source. -/
def gamma {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (lambda : I) (r : Fin oldRank) : ℂ :=
  (coord.oldExponent lambda r : ℂ) -
    (b r : ℂ) * (coord.lastExponent lambda : ℂ) / (bLast : ℂ)

/-- Exponential rate used by `f`. -/
def modifiedRate {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (lambda : I) : ℂ :=
  ∑ r, gamma coord b bLast lambda r * logAlpha r

/-- Exponential rate used by `g`. -/
def algebraicRate {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (lambda : I) : ℂ :=
  ∑ r, (coord.oldExponent lambda r : ℂ) * logAlpha r +
    (coord.lastExponent lambda : ℂ) * logAlphaLast

/-- The perturbation rate between `g` and `f`. -/
def perturbationRate {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (logAlphaLast : ℂ) (lambda : I) : ℂ :=
  (coord.lastExponent lambda : ℂ) / (bLast : ℂ) *
    logForm b bLast logAlpha logAlphaLast

/-- The exact algebraic identity underlying the comparison of `f` and `g`. -/
theorem algebraicRate_eq_modifiedRate_add_perturbationRate
    {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ) (lambda : I) :
    algebraicRate coord logAlpha logAlphaLast lambda =
      modifiedRate coord b bLast logAlpha lambda +
        perturbationRate coord b bLast logAlpha logAlphaLast lambda := by
  classical
  have hbLastC : (bLast : ℂ) ≠ 0 := by exact_mod_cast hbLast
  have hterm (r : Fin oldRank) :
      (coord.oldExponent lambda r : ℂ) * logAlpha r =
        gamma coord b bLast lambda r * logAlpha r +
          ((coord.lastExponent lambda : ℂ) / (bLast : ℂ)) *
            ((b r : ℂ) * logAlpha r) := by
    unfold gamma
    field_simp [hbLastC]
    ring
  have hsum :
      ∑ r, (coord.oldExponent lambda r : ℂ) * logAlpha r =
        (∑ r, gamma coord b bLast lambda r * logAlpha r) +
          ((coord.lastExponent lambda : ℂ) / (bLast : ℂ)) *
            ∑ r, (b r : ℂ) * logAlpha r := by
    calc
      ∑ r, (coord.oldExponent lambda r : ℂ) * logAlpha r =
          ∑ r, (gamma coord b bLast lambda r * logAlpha r +
            ((coord.lastExponent lambda : ℂ) / (bLast : ℂ)) *
              ((b r : ℂ) * logAlpha r)) := by
        apply sum_congr rfl
        intro r hr
        exact hterm r
      _ = (∑ r, gamma coord b bLast lambda r * logAlpha r) +
          ∑ r, ((coord.lastExponent lambda : ℂ) / (bLast : ℂ)) *
            ((b r : ℂ) * logAlpha r) := sum_add_distrib
      _ = _ := by rw [← Finset.mul_sum]
  simp only [algebraicRate, modifiedRate, perturbationRate, logForm]
  rw [hsum]
  field_simp [hbLastC]
  ring

/-- The source's powered, normalized Delta derivative, with the exact Delta
power supplied as an argument, evaluated in `ℂ`. -/
def poweredDeltaHasseEval (h power order : ℕ) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) z
    (poweredDeltaHasse h power order)

/-- The source's two-argument polynomial
`Delta(z;m)=(z+1)...(z+m)/m!`, evaluated in `ℂ`. -/
def simpleDeltaEval (m : ℕ) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) z (Erdos240Delta.delta m)

/-- The factor called `A(z; m)` in the source. -/
def auxiliaryFactor {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (lambda : I) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  poweredDeltaHasseEval h (coord.deltaIndex lambda + 1) (m 0)
      (z + coord.shift lambda) *
    ∏ r, simpleDeltaEval (m r.succ)
      ((bLast : ℂ) * coord.oldExponent lambda r -
        (b r : ℂ) * coord.lastExponent lambda)

/-- The argument `z / q^N` used at induction level `N`. -/
def scaledArgument (q N : ℕ) (z : ℂ) : ℂ :=
  z / (q : ℂ) ^ N

/-- The common coefficient of the matching terms of `f` and `g`.

At level `N`, the source scales **only** the argument of the Delta factor.
The exponential monomial below is still evaluated at the original `z`. -/
def sourceCoefficient {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (p : I → ℤ) (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) (lambda : I) : ℂ :=
  (p lambda : ℂ) *
    auxiliaryFactor coord h b bLast lambda (scaledArgument q N z) m

/-- The exact auxiliary function `f(z; m)` of Lemma 3.  It is written as
the zeroth ordinary derivative of a finite exponential polynomial so later
derivative and growth estimates can use `ExponentialPolynomial` directly.
Notice that its coefficient contains `A(z / q^N; m)`, whereas its exponential
factor has argument `z`, not `z / q^N`. -/
def vdplF {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  ExponentialPolynomial.ordinaryDerivative support
    (sourceCoefficient coord p h b bLast q N z m)
    (modifiedRate coord b bLast logAlpha) 0 z

/-- The exact auxiliary function `g(z; m)` of Lemma 3. -/
def vdplG {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ)
    (logAlphaLast : ℂ) (q N : ℕ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  ExponentialPolynomial.ordinaryDerivative support
    (sourceCoefficient coord p h b bLast q N z m)
    (algebraicRate coord logAlpha logAlphaLast) 0 z

/-- Sum form of the exact definition of `f`. -/
theorem vdplF_eq_sum {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    vdplF coord support p h b bLast logAlpha q N z m =
      ∑ lambda ∈ support,
        sourceCoefficient coord p h b bLast q N z m lambda *
          Complex.exp
            (modifiedRate coord b bLast logAlpha lambda * z) := by
  simp [vdplF, ExponentialPolynomial.ordinaryDerivative]

/-- Sum form of the exact definition of `g`. -/
theorem vdplG_eq_sum {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ)
    (logAlphaLast : ℂ) (q N : ℕ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    vdplG coord support p h b bLast logAlpha logAlphaLast q N z m =
      ∑ lambda ∈ support,
        sourceCoefficient coord p h b bLast q N z m lambda *
          Complex.exp
            (algebraicRate coord logAlpha logAlphaLast lambda * z) := by
  simp [vdplG, ExponentialPolynomial.ordinaryDerivative]

/-- A finite exponential sum changes by at most the sum of the translated
first-order exponential remainders when all rates are perturbed. -/
theorem norm_ordinaryDerivative_zero_perturb_le
    {I : Type*} (support : Finset I) (c baseRate perturb : I → ℂ) (z : ℂ) :
    ‖ExponentialPolynomial.ordinaryDerivative support c
          (fun i ↦ baseRate i + perturb i) 0 z -
        ExponentialPolynomial.ordinaryDerivative support c baseRate 0 z‖ ≤
      ∑ i ∈ support, ‖c i‖ * ‖Complex.exp (baseRate i * z)‖ *
        (Real.exp ‖perturb i * z‖ * ‖perturb i * z‖) := by
  classical
  simp only [ExponentialPolynomial.ordinaryDerivative, pow_zero, mul_one,
    ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
  have hfactor :
      c i * Complex.exp ((baseRate i + perturb i) * z) -
          c i * Complex.exp (baseRate i * z) =
        c i * (Complex.exp (baseRate i * z + perturb i * z) -
          Complex.exp (baseRate i * z)) := by
    rw [add_mul]
    ring
  rw [hfactor, norm_mul]
  have hrem :=
    ComplexTaylor.norm_exp_add_sub_exp_mul_partialSum_le
      (baseRate i * z) (perturb i * z) 1
  have hpartial : ComplexTaylor.expPartialSum (perturb i * z) 1 = 1 := by
    simp [ComplexTaylor.expPartialSum]
  rw [hpartial, mul_one, pow_one] at hrem
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hrem (norm_nonneg (c i))

/-- Exact termwise closeness estimate for the source auxiliary functions. -/
theorem norm_vdplG_sub_vdplF_le
    {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
        vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      ∑ lambda ∈ support,
        ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
          ‖Complex.exp
            (modifiedRate coord b bLast logAlpha lambda * z)‖ *
          (Real.exp
              ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda *
                z‖ *
            ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda *
              z‖) := by
  classical
  unfold vdplG vdplF
  have hrate : algebraicRate coord logAlpha logAlphaLast =
      fun lambda ↦ modifiedRate coord b bLast logAlpha lambda +
        perturbationRate coord b bLast logAlpha logAlphaLast lambda := by
    funext lambda
    exact algebraicRate_eq_modifiedRate_add_perturbationRate
      coord b hbLast logAlpha logAlphaLast lambda
  rw [hrate]
  exact norm_ordinaryDerivative_zero_perturb_le support
    (sourceCoefficient coord p h b bLast q N z m)
    (modifiedRate coord b bLast logAlpha)
    (perturbationRate coord b bLast logAlpha logAlphaLast) z

/-- The perturbation of an individual exponential rate is controlled by the
small linear form. -/
theorem norm_perturbationRate_mul_le_of_logForm
    {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (logAlphaLast : ℂ) (lambda : I) (z : ℂ) {bound : ℝ}
    (hsmall : ‖logForm b bLast logAlpha logAlphaLast‖ ≤ bound) :
    ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda * z‖ ≤
      ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ * bound * ‖z‖ := by
  rw [perturbationRate, mul_assoc, norm_mul, norm_mul]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall
        (norm_nonneg ((coord.lastExponent lambda : ℂ) / (bLast : ℂ))))
      (norm_nonneg z)

/-- Closeness written solely in terms of an upper bound for the original
linear form.  This is the analytic implication used with the paper's
assumption `(2)`. -/
theorem norm_vdplG_sub_vdplF_le_of_logForm
    {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) {bound : ℝ}
    (hsmall : ‖logForm b bLast logAlpha logAlphaLast‖ ≤ bound) :
    ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
        vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      ∑ lambda ∈ support,
        let U := ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ * bound *
          ‖z‖
        ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
          ‖Complex.exp
            (modifiedRate coord b bLast logAlpha lambda * z)‖ *
          (Real.exp U * U) := by
  refine (norm_vdplG_sub_vdplF_le coord support p h b hbLast logAlpha logAlphaLast
    q N z m).trans ?_
  apply sum_le_sum
  intro lambda hlambda
  let U := ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ * bound *
    ‖z‖
  have hU :
      ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda *
          z‖ ≤ U :=
    norm_perturbationRate_mul_le_of_logForm coord b bLast logAlpha logAlphaLast
      lambda z hsmall
  dsimp only
  gcongr

/-- The source function `f` has the standard exponential-polynomial growth
bound. -/
theorem norm_vdplF_le
    {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    ‖vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      ∑ lambda ∈ support,
        ‖sourceCoefficient coord p h b bLast q N z m lambda‖ *
          Real.exp (‖modifiedRate coord b bLast logAlpha lambda‖ *
            ‖z‖) := by
  simpa [vdplF] using
    ExponentialPolynomial.norm_ordinaryDerivative_le support
      (sourceCoefficient coord p h b bLast q N z m)
      (modifiedRate coord b bLast logAlpha) 0 z

/-! ## Constructing the algebraic-integer certificate -/

/-- The algebraic lift of a finite auxiliary sum.  A later radical-field
module supplies `term`; all integer coefficients are already visible here. -/
def algebraicAuxiliaryValue {I K : Type*} [Ring K]
    (support : Finset I) (p : I → ℤ) (term : I → K) : K :=
  ∑ lambda ∈ support, (p lambda : K) * term lambda

/-- Bridge from a rational powered-Delta denominator identity to algebraic
integrality.  If `denominator * value` is literally an integer and the
remaining radical monomial is integral, then the corresponding cleared term
in any number field is integral. -/
theorem isIntegral_algebraMap_mul_algebraMap_mul_of_mul_eq_int
    {K : Type*} [Field K] [NumberField K]
    {denominator value : ℚ} {w : ℤ} {radicalTerm : K}
    (hclear : denominator * value = (w : ℚ))
    (hradical : IsIntegral ℤ radicalTerm) :
    IsIntegral ℤ
      (algebraMap ℚ K denominator * (algebraMap ℚ K value * radicalTerm)) := by
  rw [← mul_assoc, ← map_mul, hclear]
  simpa using (isIntegral_intCast w).mul hradical

/-- A common denominator which makes every algebraic term integral also
makes their integral-coefficient sum integral.  This is the sole
denominator-clearing input required by the certificate constructor. -/
theorem isIntegral_cleared_algebraicAuxiliaryValue
    {I K : Type*} [Field K] [NumberField K]
    (support : Finset I) (p : I → ℤ) (term : I → K) (denominator : K)
    (hterm : ∀ lambda ∈ support,
      IsIntegral ℤ (denominator * term lambda)) :
    IsIntegral ℤ
      (denominator * algebraicAuxiliaryValue support p term) := by
  classical
  rw [algebraicAuxiliaryValue, Finset.mul_sum]
  apply IsIntegral.sum
  intro lambda hlambda
  have hp : IsIntegral ℤ (p lambda : K) := isIntegral_intCast _
  have hmul := hp.mul (hterm lambda hlambda)
  simpa [mul_assoc, mul_left_comm] using hmul

/-- The individual complex term appearing in `g`, without its integral
coefficient. -/
def algebraicComplexTerm {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    (lambda : I) : ℂ :=
  auxiliaryFactor coord h b bLast lambda (scaledArgument q N z) m *
    Complex.exp
      (algebraicRate coord logAlpha logAlphaLast lambda * z)

/-- `g` is the integral-coefficient sum of its individual complex terms. -/
theorem vdplG_eq_sum_algebraicComplexTerm
    {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    vdplG coord support p h b bLast logAlpha logAlphaLast q N z m =
      ∑ lambda ∈ support, (p lambda : ℂ) *
        algebraicComplexTerm coord h b bLast logAlpha logAlphaLast q N z m lambda := by
  rw [vdplG_eq_sum]
  apply sum_congr rfl
  intro lambda hlambda
  simp only [sourceCoefficient, algebraicComplexTerm]
  ring

/-- **Certificate construction for Lemma 3.**

Suppose a radical-field term has been chosen above every complex term of
`g`, and a common algebraic denominator makes each lifted term integral.
Then the cleared full auxiliary value is a ring of integers element.  Its
distinguished embedding is exactly `scale * g`; hence it is nonzero whenever
`g` is nonzero.  Uniform bounds for the other embeddings complete precisely
the certificate expected by `eq_zero_or_half_inv_pow_div_norm_le_norm`.

The powered-Delta denominator theorem is used only to prove `htermIntegral`;
no analytic definition or Lemma 3 estimate needs to change when that theorem
is strengthened. -/
theorem exists_algebraicInteger_certificate_of_termwise_integral
    {oldRank : ℕ} {I K : Type*} [Field K] [NumberField K]
    (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    (term : I → K) (denominator : K) (sigma : K →ₐ[ℚ] ℂ)
    {scale : ℂ} (hscale : scale ≠ 0)
    (hdenominatorMap : sigma denominator = scale)
    (htermIntegral : ∀ lambda ∈ support,
      IsIntegral ℤ (denominator * term lambda))
    (htermMap : ∀ lambda ∈ support,
      sigma (term lambda) =
        algebraicComplexTerm coord h b bLast logAlpha logAlphaLast
          q N z m lambda)
    {H : ℝ}
    (hother : ∀ tau : K →ₐ[ℚ] ℂ, tau ≠ sigma →
      ‖tau (denominator * algebraicAuxiliaryValue support p term)‖ ≤ H)
    (hg : vdplG coord support p h b bLast logAlpha logAlphaLast q N z m ≠ 0) :
    ∃ a : NumberField.RingOfIntegers K,
      a ≠ 0 ∧
        sigma (a : K) = scale *
          vdplG coord support p h b bLast logAlpha logAlphaLast q N z m ∧
        ∀ tau : K →ₐ[ℚ] ℂ, tau ≠ sigma → ‖tau (a : K)‖ ≤ H := by
  classical
  let value : K := algebraicAuxiliaryValue support p term
  have hvalueIntegral : IsIntegral ℤ (denominator * value) :=
    isIntegral_cleared_algebraicAuxiliaryValue support p term denominator htermIntegral
  let a : NumberField.RingOfIntegers K := ⟨denominator * value, hvalueIntegral⟩
  have hmapValue : sigma value =
      vdplG coord support p h b bLast logAlpha logAlphaLast q N z m := by
    rw [vdplG_eq_sum_algebraicComplexTerm]
    dsimp only [value, algebraicAuxiliaryValue]
    simp only [map_sum, map_mul, map_intCast]
    apply sum_congr rfl
    intro lambda hlambda
    rw [htermMap lambda hlambda]
  have hmap : sigma (a : K) = scale *
      vdplG coord support p h b bLast logAlpha logAlphaLast q N z m := by
    change sigma (denominator * value) = _
    rw [map_mul, hdenominatorMap, hmapValue]
  refine ⟨a, ?_, hmap, ?_⟩
  · intro ha
    have hzero : scale *
        vdplG coord support p h b bLast logAlpha logAlphaLast q N z m = 0 := by
      rw [← hmap, ha]
      simp
    exact (mul_ne_zero hscale hg) hzero
  · intro tau htau
    change ‖tau (denominator * value)‖ ≤ H
    exact hother tau htau

/-! ## Transferring Liouville lower bounds across the analytic error -/

/-- If `g` has norm at least `L` and `g-f` has norm at most `L/2`, then
`f` has norm at least `L/2`. -/
theorem half_le_norm_of_lower_le_norm_of_sub_le_half
    {f g : ℂ} {L : ℝ} (hg : L ≤ ‖g‖)
    (hclose : ‖g - f‖ ≤ L / 2) :
    L / 2 ≤ ‖f‖ := by
  have hreverse : ‖g‖ - ‖f‖ ≤ ‖g - f‖ := norm_sub_norm_le g f
  linarith

/-- A direct nonzero algebraic-integer value of `g` gives the source's
factor-`1/2` lower bound for the nearby value of `f`. -/
theorem half_inv_pow_finrank_sub_one_le_norm_of_algebraicInteger
    {K : Type*} [Field K] [NumberField K]
    {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (sigma : K →ₐ[ℚ] ℂ) {H : ℝ} (hH : 0 < H)
    (hother : ∀ tau : K →ₐ[ℚ] ℂ, tau ≠ sigma → ‖tau (a : K)‖ ≤ H)
    {f g : ℂ} (hg : g = sigma (a : K))
    (hclose : ‖g - f‖ ≤ (H ^ (Module.finrank ℚ K - 1))⁻¹ / 2) :
    (H ^ (Module.finrank ℚ K - 1))⁻¹ / 2 ≤ ‖f‖ := by
  apply half_le_norm_of_lower_le_norm_of_sub_le_half (f := f) (g := g)
  · rw [hg]
    exact AlgebraicLiouville.inv_pow_finrank_sub_one_le_norm ha sigma hH hother
  · exact hclose

/-- A denominator-cleared algebraic integer gives a lower bound for the
uncleared value.  This is the form needed at the points `l/q`. -/
theorem inv_pow_div_norm_le_norm_of_algebraicInteger_multiple
    {K : Type*} [Field K] [NumberField K]
    {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (sigma : K →ₐ[ℚ] ℂ) {H : ℝ} (hH : 0 < H)
    (hother : ∀ tau : K →ₐ[ℚ] ℂ, tau ≠ sigma → ‖tau (a : K)‖ ≤ H)
    {scale g : ℂ} (hscale : scale ≠ 0) (hmap : sigma (a : K) = scale * g) :
    (H ^ (Module.finrank ℚ K - 1))⁻¹ / ‖scale‖ ≤ ‖g‖ := by
  rw [div_le_iff₀ (norm_pos_iff.mpr hscale)]
  have hliouville :=
    AlgebraicLiouville.inv_pow_finrank_sub_one_le_norm ha sigma hH hother
  rw [hmap, norm_mul] at hliouville
  simpa [mul_comm] using hliouville

/-- The cleared-value version with the analytic factor `1/2`. -/
theorem half_inv_pow_div_norm_le_norm_of_algebraicInteger_multiple
    {K : Type*} [Field K] [NumberField K]
    {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (sigma : K →ₐ[ℚ] ℂ) {H : ℝ} (hH : 0 < H)
    (hother : ∀ tau : K →ₐ[ℚ] ℂ, tau ≠ sigma → ‖tau (a : K)‖ ≤ H)
    {scale f g : ℂ} (hscale : scale ≠ 0) (hmap : sigma (a : K) = scale * g)
    (hclose : ‖g - f‖ ≤
      ((H ^ (Module.finrank ℚ K - 1))⁻¹ / ‖scale‖) / 2) :
    ((H ^ (Module.finrank ℚ K - 1))⁻¹ / ‖scale‖) / 2 ≤ ‖f‖ := by
  apply half_le_norm_of_lower_le_norm_of_sub_le_half
  · exact inv_pow_div_norm_le_norm_of_algebraicInteger_multiple
      ha sigma hH hother hscale hmap
  · exact hclose

/-- Lemma 3's lower-bound alternative in certificate form.  The future
denominator-clearing theorem supplies `hcertificate`; all analytic and norm
reasoning after that point is discharged here. -/
theorem eq_zero_or_half_inv_pow_div_norm_le_norm
    {K : Type*} [Field K] [NumberField K]
    (sigma : K →ₐ[ℚ] ℂ) {H : ℝ} (hH : 0 < H)
    {scale f g : ℂ} (hscale : scale ≠ 0)
    (hcertificate : g ≠ 0 →
      ∃ a : NumberField.RingOfIntegers K,
        a ≠ 0 ∧ sigma (a : K) = scale * g ∧
          ∀ tau : K →ₐ[ℚ] ℂ, tau ≠ sigma → ‖tau (a : K)‖ ≤ H)
    (hclose : ‖g - f‖ ≤
      ((H ^ (Module.finrank ℚ K - 1))⁻¹ / ‖scale‖) / 2) :
    g = 0 ∨ ((H ^ (Module.finrank ℚ K - 1))⁻¹ / ‖scale‖) / 2 ≤ ‖f‖ := by
  by_cases hg : g = 0
  · exact Or.inl hg
  · right
    obtain ⟨a, ha, hmap, hother⟩ := hcertificate hg
    exact half_inv_pow_div_norm_le_norm_of_algebraicInteger_multiple
      ha sigma hH hother hscale hmap hclose

/-- Lemma 3's lower alternative obtained directly from a termwise
powered-Delta integrality hypothesis.  This is the stable consumer-facing
interface: a later module supplies the radical-field terms, their common
denominator, and conjugate estimates, while the conclusion already has the
source's `g = 0 ∨ lower/2 ≤ ‖f‖` shape. -/
theorem vdplG_eq_zero_or_half_lower_of_termwise_integral
    {oldRank : ℕ} {I K : Type*} [Field K] [NumberField K]
    (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    (term : I → K) (denominator : K) (sigma : K →ₐ[ℚ] ℂ)
    {scale : ℂ} (hscale : scale ≠ 0)
    (hdenominatorMap : sigma denominator = scale)
    (htermIntegral : ∀ lambda ∈ support,
      IsIntegral ℤ (denominator * term lambda))
    (htermMap : ∀ lambda ∈ support,
      sigma (term lambda) =
        algebraicComplexTerm coord h b bLast logAlpha logAlphaLast
          q N z m lambda)
    {H : ℝ} (hH : 0 < H)
    (hother : ∀ tau : K →ₐ[ℚ] ℂ, tau ≠ sigma →
      ‖tau (denominator * algebraicAuxiliaryValue support p term)‖ ≤ H)
    (hclose :
      ‖vdplG coord support p h b bLast logAlpha logAlphaLast q N z m -
          vdplF coord support p h b bLast logAlpha q N z m‖ ≤
        ((H ^ (Module.finrank ℚ K - 1))⁻¹ / ‖scale‖) / 2) :
    vdplG coord support p h b bLast logAlpha logAlphaLast q N z m = 0 ∨
      ((H ^ (Module.finrank ℚ K - 1))⁻¹ / ‖scale‖) / 2 ≤
        ‖vdplF coord support p h b bLast logAlpha q N z m‖ := by
  apply eq_zero_or_half_inv_pow_div_norm_le_norm sigma hH hscale
  · intro hg
    exact exists_algebraicInteger_certificate_of_termwise_integral
      coord support p h b bLast logAlpha logAlphaLast q N z m
      term denominator sigma hscale hdenominatorMap htermIntegral htermMap hother hg
  · exact hclose

/-- The same transfer when the product over a finite family of embeddings has
already been established directly. -/
theorem half_one_div_pow_card_sub_one_le_norm_of_embeddingProduct
    {I : Type*} [Fintype I] (i : I) (conjugate : I → ℂ) {H : ℝ}
    (hH : 1 ≤ H) (hbound : ∀ j, ‖conjugate j‖ ≤ H)
    (hprod : 1 ≤ ‖∏ j, conjugate j‖) {f : ℂ}
    (hclose : ‖conjugate i - f‖ ≤
      (1 / H ^ (Fintype.card I - 1)) / 2) :
    (1 / H ^ (Fintype.card I - 1)) / 2 ≤ ‖f‖ := by
  apply half_le_norm_of_lower_le_norm_of_sub_le_half
  · exact EmbeddingProduct.one_div_pow_card_sub_one_le_norm_of_forall_le
      i conjugate H hH hbound hprod
  · exact hclose

end Erdos240.BakerLemma3

#print axioms Erdos240.BakerLemma3.algebraicRate_eq_modifiedRate_add_perturbationRate
#print axioms Erdos240.BakerLemma3.norm_vdplG_sub_vdplF_le_of_logForm
#print axioms Erdos240.BakerLemma3.isIntegral_algebraMap_mul_algebraMap_mul_of_mul_eq_int
#print axioms Erdos240.BakerLemma3.exists_algebraicInteger_certificate_of_termwise_integral
#print axioms Erdos240.BakerLemma3.half_inv_pow_div_norm_le_norm_of_algebraicInteger_multiple
#print axioms Erdos240.BakerLemma3.eq_zero_or_half_inv_pow_div_norm_le_norm
#print axioms Erdos240.BakerLemma3.vdplG_eq_zero_or_half_lower_of_termwise_integral
