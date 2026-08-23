/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceState
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Jet transport for the coprime-node completion

On pp. 51--52 of van der Poorten--Loxton, the values available after
radical descent have the full predecessor multi-index budget.  Hermite
interpolation then spends part of that budget on ordinary derivatives in
the interpolation variable.  This file records the algebraic identities
behind that conversion.

The two identities are exact.  Differentiating the head Hasse derivative
raises its Hasse index, while multiplication by an old modified exponent is
converted to a difference of two consecutive ordinary Delta polynomials.
They are the source of the `S/4 + 3S/4` budget split.
-/

open scoped BigOperators Polynomial

noncomputable section

namespace Erdos240.BakerCoprimeJetTransport

open Polynomial
open Erdos240Delta DeltaPower BakerLemma3 BakerSourceState

/-- Increase one component of a source multi-index by one. -/
def increment {n : ℕ} (m : VDPLMultiIndex n) (i : Fin n) :
    VDPLMultiIndex n :=
  m + Pi.single i 1

@[simp] theorem increment_same {n : ℕ} (m : VDPLMultiIndex n) (i : Fin n) :
    increment m i i = m i + 1 := by
  simp [increment]

@[simp] theorem increment_ne {n : ℕ} (m : VDPLMultiIndex n)
    {i j : Fin n} (hij : j ≠ i) :
    increment m i j = m j := by
  simp [increment, hij]

/-- Spending one ordinary derivative consumes exactly one unit of total
multi-index budget. -/
@[simp] theorem weight_increment {n : ℕ} (m : VDPLMultiIndex n) (i : Fin n) :
    VDPLMultiIndex.weight (increment m i) = VDPLMultiIndex.weight m + 1 := by
  classical
  simp [VDPLMultiIndex.weight, increment, Finset.sum_add_distrib]

/-- Ordinary differentiation raises the Hasse index, with the expected
integer factor. -/
theorem derivative_poweredDeltaHasse (h power order : ℕ) :
    derivative (poweredDeltaHasse h power order) =
      (order + 1) • poweredDeltaHasse h power (order + 1) := by
  have hcomp := congrArg
    (fun D : ℚ[X] →ₗ[ℚ] ℚ[X] ↦ D (poweredDelta h power))
    (Polynomial.hasseDeriv_comp (R := ℚ) 1 order)
  simpa only [poweredDeltaHasse, Polynomial.hasseDeriv_one,
    LinearMap.comp_apply, LinearMap.smul_apply, Nat.one_add, Nat.choose_one_right,
    Nat.succ_eq_add_one] using hcomp

/-- Analytic derivative form of `derivative_poweredDeltaHasse`. -/
theorem hasDerivAt_poweredDeltaHasseEval (h power order : ℕ) (z : ℂ) :
    HasDerivAt (poweredDeltaHasseEval h power order)
      ((order + 1 : ℂ) * poweredDeltaHasseEval h power (order + 1) z) z := by
  change HasDerivAt
    (fun x ↦ Polynomial.eval₂ (algebraMap ℚ ℂ) x
      (poweredDeltaHasse h power order))
    ((order + 1 : ℂ) * Polynomial.eval₂ (algebraMap ℚ ℂ) z
      (poweredDeltaHasse h power (order + 1))) z
  have hpoly :=
    (poweredDeltaHasse h power order).hasDerivAt_aeval z
  rw [derivative_poweredDeltaHasse] at hpoly
  simpa [poweredDeltaHasseEval, Polynomial.aeval_def, nsmul_eq_mul] using hpoly

/-- The consecutive-Delta relation used to trade multiplication by an old
modified exponent for one unit of multi-index budget. -/
theorem X_mul_delta (m : ℕ) :
    X * delta m = C (m + 1 : ℚ) * (delta (m + 1) - delta m) := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_sub, eval_delta_eq_prod, Finset.prod_range_succ,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [Nat.factorial_ne_zero]
  ring

/-- Evaluation form of `X_mul_delta` over the complex numbers. -/
theorem mul_simpleDeltaEval (m : ℕ) (x : ℂ) :
    x * simpleDeltaEval m x =
      (m + 1 : ℂ) * (simpleDeltaEval (m + 1) x - simpleDeltaEval m x) := by
  have h := congrArg
    (fun p : ℚ[X] ↦ Polynomial.eval₂ (algebraMap ℚ ℂ) x p)
    (X_mul_delta m)
  simpa [simpleDeltaEval] using h

/-- Raising an old multi-index component changes only the corresponding
factor in the finite old-coordinate product. -/
theorem oldDeltaProduct_increment {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (lambda : I) (m : VDPLMultiIndex (oldRank + 1)) (r : Fin oldRank) :
    (∏ s, simpleDeltaEval ((increment m r.succ) s.succ)
        ((bLast : ℂ) * coord.oldExponent lambda s -
          (b s : ℂ) * coord.lastExponent lambda)) =
      simpleDeltaEval (m r.succ + 1)
          ((bLast : ℂ) * coord.oldExponent lambda r -
            (b r : ℂ) * coord.lastExponent lambda) *
        ∏ s ∈ (Finset.univ.erase r),
          simpleDeltaEval (m s.succ)
            ((bLast : ℂ) * coord.oldExponent lambda s -
              (b s : ℂ) * coord.lastExponent lambda) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun s ↦ simpleDeltaEval ((increment m r.succ) s.succ)
      ((bLast : ℂ) * coord.oldExponent lambda s -
        (b s : ℂ) * coord.lastExponent lambda)) (Finset.mem_univ r)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro s hs
    have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
    have hsucc : s.succ ≠ r.succ := by
      intro h
      exact hsr (Fin.succ_injective oldRank h)
    rw [increment_ne m hsucc]

/-- Multiplication of the old-coordinate product by the integral modified
exponent consumes one old-coordinate unit, in difference form. -/
theorem modifiedExponent_mul_oldDeltaProduct {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (lambda : I) (m : VDPLMultiIndex (oldRank + 1)) (r : Fin oldRank) :
    (((bLast : ℂ) * coord.oldExponent lambda r -
        (b r : ℂ) * coord.lastExponent lambda) *
      ∏ s, simpleDeltaEval (m s.succ)
        ((bLast : ℂ) * coord.oldExponent lambda s -
          (b s : ℂ) * coord.lastExponent lambda)) =
      (m r.succ + 1 : ℂ) *
        ((∏ s, simpleDeltaEval ((increment m r.succ) s.succ)
            ((bLast : ℂ) * coord.oldExponent lambda s -
              (b s : ℂ) * coord.lastExponent lambda)) -
          ∏ s, simpleDeltaEval (m s.succ)
            ((bLast : ℂ) * coord.oldExponent lambda s -
              (b s : ℂ) * coord.lastExponent lambda)) := by
  classical
  let x : Fin oldRank → ℂ := fun s ↦
    (bLast : ℂ) * coord.oldExponent lambda s -
      (b s : ℂ) * coord.lastExponent lambda
  have hold := Finset.mul_prod_erase Finset.univ
    (fun s ↦ simpleDeltaEval (m s.succ) (x s)) (Finset.mem_univ r)
  dsimp only [x] at hold ⊢
  rw [oldDeltaProduct_increment]
  rw [← hold]
  calc
    (((bLast : ℂ) * coord.oldExponent lambda r -
          (b r : ℂ) * coord.lastExponent lambda) *
        (simpleDeltaEval (m r.succ)
          ((bLast : ℂ) * coord.oldExponent lambda r -
            (b r : ℂ) * coord.lastExponent lambda) *
          ∏ s ∈ Finset.univ.erase r,
            simpleDeltaEval (m s.succ)
              ((bLast : ℂ) * coord.oldExponent lambda s -
                (b s : ℂ) * coord.lastExponent lambda))) =
        ((((bLast : ℂ) * coord.oldExponent lambda r -
            (b r : ℂ) * coord.lastExponent lambda) *
          simpleDeltaEval (m r.succ)
            ((bLast : ℂ) * coord.oldExponent lambda r -
              (b r : ℂ) * coord.lastExponent lambda)) *
          ∏ s ∈ Finset.univ.erase r,
            simpleDeltaEval (m s.succ)
              ((bLast : ℂ) * coord.oldExponent lambda s -
                (b s : ℂ) * coord.lastExponent lambda)) := by ring
    _ = (((m r.succ + 1 : ℂ) *
          (simpleDeltaEval (m r.succ + 1)
              ((bLast : ℂ) * coord.oldExponent lambda r -
                (b r : ℂ) * coord.lastExponent lambda) -
            simpleDeltaEval (m r.succ)
              ((bLast : ℂ) * coord.oldExponent lambda r -
                (b r : ℂ) * coord.lastExponent lambda))) *
          ∏ s ∈ Finset.univ.erase r,
            simpleDeltaEval (m s.succ)
              ((bLast : ℂ) * coord.oldExponent lambda s -
                (b s : ℂ) * coord.lastExponent lambda)) := by
      rw [mul_simpleDeltaEval]
    _ = _ := by ring

/-- The normalized exponent is the integral modified exponent divided by
`bLast`.  This is the normalization used on p. 51 of the source. -/
theorem gamma_eq_modifiedExponent_div {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hbLast : bLast ≠ 0) (lambda : I) (r : Fin oldRank) :
    gamma coord b bLast lambda r =
      ((bLast : ℂ) * coord.oldExponent lambda r -
        (b r : ℂ) * coord.lastExponent lambda) / (bLast : ℂ) := by
  have hbLastC : (bLast : ℂ) ≠ 0 := by exact_mod_cast hbLast
  simp only [gamma]
  field_simp [hbLastC]

/-- Multiplication of the complete Delta factor by one normalized old
exponent is a difference of adjacent multi-index values. -/
theorem gamma_mul_auxiliaryFactor {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (lambda : I) (u : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    (r : Fin oldRank) :
    gamma coord b bLast lambda r *
        auxiliaryFactor coord h b bLast lambda u m =
      ((m r.succ + 1 : ℂ) / (bLast : ℂ)) *
        (auxiliaryFactor coord h b bLast lambda u (increment m r.succ) -
          auxiliaryFactor coord h b bLast lambda u m) := by
  rw [gamma_eq_modifiedExponent_div coord b hbLast]
  unfold auxiliaryFactor
  have hzero : (0 : Fin (oldRank + 1)) ≠ r.succ := by
    intro hrs
    have := congrArg Fin.val hrs
    simp at this
  simp only [increment_ne m hzero]
  let H : ℂ := poweredDeltaHasseEval h (coord.deltaIndex lambda + 1) (m 0)
    (u + coord.shift lambda)
  let Q : ℂ := ∏ s, simpleDeltaEval (m s.succ)
    ((bLast : ℂ) * coord.oldExponent lambda s -
      (b s : ℂ) * coord.lastExponent lambda)
  let Q' : ℂ := ∏ s, simpleDeltaEval ((increment m r.succ) s.succ)
    ((bLast : ℂ) * coord.oldExponent lambda s -
      (b s : ℂ) * coord.lastExponent lambda)
  have hprod :
      ((bLast : ℂ) * coord.oldExponent lambda r -
          (b r : ℂ) * coord.lastExponent lambda) * Q =
        (m r.succ + 1 : ℂ) * (Q' - Q) := by
    exact modifiedExponent_mul_oldDeltaProduct coord b bLast lambda m r
  dsimp only [H, Q, Q'] at hprod ⊢
  calc
    _ = ((1 : ℂ) / (bLast : ℂ)) *
        poweredDeltaHasseEval h (coord.deltaIndex lambda + 1) (m 0)
          (u + coord.shift lambda) *
        (((bLast : ℂ) * coord.oldExponent lambda r -
            (b r : ℂ) * coord.lastExponent lambda) *
          ∏ s, simpleDeltaEval (m s.succ)
            ((bLast : ℂ) * coord.oldExponent lambda s -
              (b s : ℂ) * coord.lastExponent lambda)) := by ring
    _ = _ := by rw [hprod]; ring

/-- The exponential rate acting on the complete Delta factor is the sum of
the old-coordinate adjacent differences. -/
theorem modifiedRate_mul_auxiliaryFactor {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (logAlpha : Fin oldRank → ℂ) (lambda : I) (u : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    modifiedRate coord b bLast logAlpha lambda *
        auxiliaryFactor coord h b bLast lambda u m =
      ∑ r, (((m r.succ + 1 : ℂ) * logAlpha r) / (bLast : ℂ)) *
        (auxiliaryFactor coord h b bLast lambda u (increment m r.succ) -
          auxiliaryFactor coord h b bLast lambda u m) := by
  classical
  simp only [modifiedRate, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    gamma coord b bLast lambda r * logAlpha r *
        auxiliaryFactor coord h b bLast lambda u m =
      logAlpha r * (gamma coord b bLast lambda r *
        auxiliaryFactor coord h b bLast lambda u m) := by ring
    _ = logAlpha r * (((m r.succ + 1 : ℂ) / (bLast : ℂ)) *
        (auxiliaryFactor coord h b bLast lambda u (increment m r.succ) -
          auxiliaryFactor coord h b bLast lambda u m)) := by
      rw [gamma_mul_auxiliaryFactor coord h b hbLast]
    _ = _ := by ring

/-- The head increment leaves every old-coordinate Delta factor unchanged. -/
theorem auxiliaryFactor_increment_head {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : I)
    (u : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    auxiliaryFactor coord h b bLast lambda u (increment m 0) =
      poweredDeltaHasseEval h (coord.deltaIndex lambda + 1) (m 0 + 1)
          (u + coord.shift lambda) *
        ∏ r, simpleDeltaEval (m r.succ)
          ((bLast : ℂ) * coord.oldExponent lambda r -
            (b r : ℂ) * coord.lastExponent lambda) := by
  simp [auxiliaryFactor]

/-- Exact derivative of the source Delta factor after the level scaling.
Only the head multi-index is raised. -/
theorem hasDerivAt_auxiliaryFactor_scaled {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : I)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    HasDerivAt
      (fun w ↦ auxiliaryFactor coord h b bLast lambda
        (scaledArgument q N w) m)
      (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) *
        auxiliaryFactor coord h b bLast lambda
          (scaledArgument q N z) (increment m 0)) z := by
  let Q : ℂ := ∏ r, simpleDeltaEval (m r.succ)
    ((bLast : ℂ) * coord.oldExponent lambda r -
      (b r : ℂ) * coord.lastExponent lambda)
  have hinner : HasDerivAt (fun w : ℂ ↦
      scaledArgument q N w + (coord.shift lambda : ℂ))
      ((1 : ℂ) / (q : ℂ) ^ N) z := by
    simpa [scaledArgument] using
      ((hasDerivAt_id z).div_const ((q : ℂ) ^ N)).add_const
        (coord.shift lambda : ℂ)
  have hhead :=
    (hasDerivAt_poweredDeltaHasseEval h (coord.deltaIndex lambda + 1)
      (m 0) (scaledArgument q N z + coord.shift lambda)).comp z hinner
  have hmul := hhead.mul_const Q
  rw [auxiliaryFactor_increment_head]
  change HasDerivAt
    (fun w ↦ poweredDeltaHasseEval h (coord.deltaIndex lambda + 1) (m 0)
        (scaledArgument q N w + coord.shift lambda) * Q)
    (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) *
      (poweredDeltaHasseEval h (coord.deltaIndex lambda + 1) (m 0 + 1)
        (scaledArgument q N z + coord.shift lambda) * Q)) z
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

section AnalyticJet

/-- One summand of the analytic auxiliary function. -/
def sourceTerm {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (p : I → ℤ) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (q N : ℕ) (lambda : I) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  (p lambda : ℂ) *
    auxiliaryFactor coord h b bLast lambda (scaledArgument q N z) m *
      Complex.exp (modifiedRate coord b bLast logAlpha lambda * z)

/-- The finite-difference operator on the multi-index family which represents
one ordinary derivative in the interpolation variable. -/
def jetStep {oldRank : ℕ}
    (q N : ℕ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (F : VDPLMultiIndex (oldRank + 1) → ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) * F (increment m 0)) +
    ∑ r, (((m r.succ + 1 : ℂ) * logAlpha r) / (bLast : ℂ)) *
      (F (increment m r.succ) - F m)

/-- Exact one-step jet transport for an individual source summand. -/
theorem hasDerivAt_sourceTerm {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (p : I → ℤ) (h : ℕ)
    (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (logAlpha : Fin oldRank → ℂ) (q N : ℕ) (lambda : I)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    @HasDerivAt ℂ DenselyNormedField.toNontriviallyNormedField ℂ
      NormedField.toNormedCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℂ).toModule _ _
      (fun w ↦ sourceTerm coord p h b bLast logAlpha q N lambda w m)
      (jetStep q N bLast logAlpha
        (fun m' ↦ sourceTerm coord p h b bLast logAlpha q N lambda z m') m) z := by
  classical
  let A : VDPLMultiIndex (oldRank + 1) → ℂ := fun m' ↦
    auxiliaryFactor coord h b bLast lambda (scaledArgument q N z) m'
  let e : ℂ := Complex.exp (modifiedRate coord b bLast logAlpha lambda * z)
  have haux := hasDerivAt_auxiliaryFactor_scaled coord h b bLast lambda q N z m
  have hcoeff := haux.const_mul (p lambda : ℂ)
  have hexp : HasDerivAt
      (fun w ↦ Complex.exp (modifiedRate coord b bLast logAlpha lambda * w))
      (modifiedRate coord b bLast logAlpha lambda * e) z := by
    simpa [e, Function.comp_def, mul_comm] using
      (Complex.hasDerivAt_exp
        (modifiedRate coord b bLast logAlpha lambda * z)).comp z
          ((hasDerivAt_id z).const_mul
            (modifiedRate coord b bLast logAlpha lambda))
  have hprod := hcoeff.mul hexp
  have hrate := modifiedRate_mul_auxiliaryFactor coord h b hbLast logAlpha
    lambda (scaledArgument q N z) m
  have hcoef :
      (p lambda : ℂ) *
            (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) * A (increment m 0)) * e +
          ((p lambda : ℂ) * A m) *
            (modifiedRate coord b bLast logAlpha lambda * e) =
        jetStep q N bLast logAlpha
          (fun m' ↦ sourceTerm coord p h b bLast logAlpha q N lambda z m') m := by
    change
      (p lambda : ℂ) *
            (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) * A (increment m 0)) * e +
          ((p lambda : ℂ) * A m) *
            (modifiedRate coord b bLast logAlpha lambda * e) =
        (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) *
            ((p lambda : ℂ) * A (increment m 0) * e)) +
          ∑ r, (((m r.succ + 1 : ℂ) * logAlpha r) / (bLast : ℂ)) *
            ((p lambda : ℂ) * A (increment m r.succ) * e -
              (p lambda : ℂ) * A m * e)
    calc
      (p lambda : ℂ) *
            (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) * A (increment m 0)) * e +
          ((p lambda : ℂ) * A m) *
            (modifiedRate coord b bLast logAlpha lambda * e) =
        (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) *
            ((p lambda : ℂ) * A (increment m 0) * e)) +
          (p lambda : ℂ) *
            (modifiedRate coord b bLast logAlpha lambda * A m) * e := by ring
      _ = (((m 0 + 1 : ℂ) / (q : ℂ) ^ N) *
            ((p lambda : ℂ) * A (increment m 0) * e)) +
          ∑ r, (((m r.succ + 1 : ℂ) * logAlpha r) / (bLast : ℂ)) *
            ((p lambda : ℂ) * A (increment m r.succ) * e -
              (p lambda : ℂ) * A m * e) := by
        rw [show (p lambda : ℂ) *
            (modifiedRate coord b bLast logAlpha lambda * A m) * e =
            ∑ r, (((m r.succ + 1 : ℂ) * logAlpha r) / (bLast : ℂ)) *
              ((p lambda : ℂ) * A (increment m r.succ) * e -
                (p lambda : ℂ) * A m * e) by
          calc
            (p lambda : ℂ) *
                (modifiedRate coord b bLast logAlpha lambda * A m) * e =
              (p lambda : ℂ) *
                (∑ r, (((m r.succ + 1 : ℂ) * logAlpha r) / (bLast : ℂ)) *
                  (A (increment m r.succ) - A m)) * e := by rw [hrate]
            _ = _ := by
              rw [Finset.mul_sum, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro r hr
              ring]
  rw [← hcoef]
  have hfun :
      (fun w ↦ sourceTerm coord p h b bLast logAlpha q N lambda w m) =ᶠ[nhds z]
        ((fun y ↦ (p lambda : ℂ) *
          auxiliaryFactor coord h b bLast lambda (scaledArgument q N y) m) *
          fun w ↦ Complex.exp
            (modifiedRate coord b bLast logAlpha lambda * w)) :=
    Filter.Eventually.of_forall fun w ↦ by rfl
  simpa only [A, e] using hprod.congr_of_eventuallyEq hfun

/-- At derivative order zero, the source auxiliary function is the finite
sum of `sourceTerm`s. -/
theorem vdplF_eq_sum_sourceTerm {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (q N : ℕ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    vdplF coord support p h b bLast logAlpha q N z m =
      ∑ lambda ∈ support,
        sourceTerm coord p h b bLast logAlpha q N lambda z m := by
  simp [vdplF, ExponentialPolynomial.ordinaryDerivative, sourceCoefficient,
    sourceTerm]

/-- `jetStep` commutes with a finite sum of multi-index families. -/
theorem sum_jetStep {oldRank : ℕ} {I : Type*}
    (support : Finset I) (q N : ℕ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ)
    (F : I → VDPLMultiIndex (oldRank + 1) → ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (∑ lambda ∈ support, jetStep q N bLast logAlpha (F lambda) m) =
      jetStep q N bLast logAlpha
        (fun m' ↦ ∑ lambda ∈ support, F lambda m') m := by
  classical
  unfold jetStep
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.mul_sum]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]

/-- Analytic linearity of `jetStep`: differentiating a transported family
transports the pointwise derivatives by the same operator. -/
theorem hasDerivAt_jetStep {oldRank : ℕ}
    (q N : ℕ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (F : ℂ → VDPLMultiIndex (oldRank + 1) → ℂ)
    (F' : VDPLMultiIndex (oldRank + 1) → ℂ) (z : ℂ)
    (hF : ∀ m',
      @HasDerivAt ℂ DenselyNormedField.toNontriviallyNormedField ℂ
        NormedField.toNormedCommRing.toAddCommGroup
        (NormedAlgebra.toNormedSpace ℂ).toModule _ _
        (fun w ↦ F w m') (F' m') z)
    (m : VDPLMultiIndex (oldRank + 1)) :
    @HasDerivAt ℂ DenselyNormedField.toNontriviallyNormedField ℂ
      NormedField.toNormedCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℂ).toModule _ _
      (fun w ↦ jetStep q N bLast logAlpha (F w) m)
      (jetStep q N bLast logAlpha F' m) z := by
  classical
  let a : ℂ := (m 0 + 1 : ℂ) / (q : ℂ) ^ N
  let c : Fin oldRank → ℂ := fun r ↦
    ((m r.succ + 1 : ℂ) * logAlpha r) / (bLast : ℂ)
  have hhead := (hF (increment m 0)).const_mul a
  have hold := HasDerivAt.fun_sum (u := Finset.univ) fun r hr ↦
    ((hF (increment m r.succ)).sub (hF m)).const_mul (c r)
  have hadd := hhead.add hold
  have hfun :
      (fun w ↦ jetStep q N bLast logAlpha (F w) m) =ᶠ[nhds z]
        (fun w ↦ a * F w (increment m 0) +
          ∑ r, c r * (F w (increment m r.succ) - F w m)) :=
    Filter.Eventually.of_forall fun w ↦ by rfl
  have hadd' := hadd.congr_of_eventuallyEq hfun
  simpa only [jetStep, a, c] using hadd'

/-- Iterate the discrete jet-transport operator. -/
def jetPower {oldRank : ℕ}
    (q N : ℕ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ) :
    ℕ → (VDPLMultiIndex (oldRank + 1) → ℂ) →
      VDPLMultiIndex (oldRank + 1) → ℂ
  | 0, F => F
  | n + 1, F => fun m ↦
      jetStep q N bLast logAlpha (jetPower q N bLast logAlpha n F) m

/-- Exact one-step jet transport for the complete source auxiliary function.
Thus the analytic derivative budget and the discrete descent budget are the
same budget, one unit at a time. -/
theorem hasDerivAt_vdplF {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (logAlpha : Fin oldRank → ℂ) (q N : ℕ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    @HasDerivAt ℂ DenselyNormedField.toNontriviallyNormedField ℂ
      NormedField.toNormedCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℂ).toModule _ _
      (fun w ↦ vdplF coord support p h b bLast logAlpha q N w m)
      (jetStep q N bLast logAlpha
        (fun m' ↦ vdplF coord support p h b bLast logAlpha q N z m') m) z := by
  classical
  have hsum := HasDerivAt.fun_sum (u := support) fun lambda hlambda ↦
    hasDerivAt_sourceTerm coord p h b hbLast logAlpha q N lambda z m
  rw [sum_jetStep support q N bLast logAlpha] at hsum
  have hfun :
      (fun w ↦ vdplF coord support p h b bLast logAlpha q N w m) =ᶠ[nhds z]
        (fun w ↦ ∑ lambda ∈ support,
          sourceTerm coord p h b bLast logAlpha q N lambda w m) :=
    Filter.Eventually.of_forall fun w ↦ vdplF_eq_sum_sourceTerm
      coord support p h b bLast logAlpha q N w m
  have hsum' := hsum.congr_of_eventuallyEq hfun
  simpa only [vdplF_eq_sum_sourceTerm] using hsum'

@[simp] theorem fWithLogs_eq_vdplF {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    fWithLogs state b bLast logAlpha z m =
      vdplF coordinates state.support state.coeff P.h b bLast logAlpha
        P.q J z m := by
  rfl

/-- Concrete `LevelState` specialization of the one-step jet recurrence. -/
theorem hasDerivAt_fWithLogs {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hbLast : bLast ≠ 0) (logAlpha : Fin oldRank → ℂ)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    @HasDerivAt ℂ DenselyNormedField.toNontriviallyNormedField ℂ
      NormedField.toNormedCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℂ).toModule _ _
      (fun w ↦ fWithLogs state b bLast logAlpha w m)
      (jetStep P.q J bLast logAlpha
        (fun m' ↦ fWithLogs state b bLast logAlpha z m') m) z := by
  simpa only [fWithLogs_eq_vdplF] using
    hasDerivAt_vdplF coordinates state.support state.coeff P.h b hbLast
      logAlpha P.q J z m

/-- Concrete source-logarithm specialization used by the coprime descent. -/
theorem hasDerivAt_fSource {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hbLast : bLast ≠ 0)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    @HasDerivAt ℂ DenselyNormedField.toNontriviallyNormedField ℂ
      NormedField.toNormedCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℂ).toModule _ _
      (fun w ↦ fSource state b bLast w m)
      (jetStep P.q J bLast (oldLog P)
      (fun m' ↦ fSource state b bLast z m') m) z := by
  exact hasDerivAt_fWithLogs state b hbLast (oldLog P) z m

/-- Successive analytic derivatives of `vdplF` are represented by successive
applications of the discrete jet operator. -/
theorem hasDerivAt_jetPower_vdplF {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (logAlpha : Fin oldRank → ℂ) (q N n : ℕ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    @HasDerivAt ℂ DenselyNormedField.toNontriviallyNormedField ℂ
      NormedField.toNormedCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℂ).toModule _ _
      (fun w ↦ jetPower q N bLast logAlpha n
        (fun m' ↦ vdplF coord support p h b bLast logAlpha q N w m') m)
      (jetPower q N bLast logAlpha (n + 1)
        (fun m' ↦ vdplF coord support p h b bLast logAlpha q N z m') m) z := by
  induction n generalizing z m with
  | zero =>
      simpa only [jetPower, Nat.zero_add] using
        hasDerivAt_vdplF coord support p h b hbLast logAlpha q N z m
  | succ n ih =>
      have hstep := hasDerivAt_jetStep q N bLast logAlpha
        (fun w m' ↦ jetPower q N bLast logAlpha n
          (fun m'' ↦ vdplF coord support p h b bLast logAlpha q N w m'') m')
        (jetPower q N bLast logAlpha (n + 1)
          (fun m' ↦ vdplF coord support p h b bLast logAlpha q N z m')) z
        (fun m' ↦ ih z m') m
      simpa only [jetPower, Nat.succ_eq_add_one, Nat.add_assoc] using hstep

/-- Closed formula for every iterated ordinary derivative of `vdplF`. -/
theorem iteratedDeriv_vdplF_eq_jetPower {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (logAlpha : Fin oldRank → ℂ) (q N n : ℕ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    iteratedDeriv n
        (fun w ↦ vdplF coord support p h b bLast logAlpha q N w m) z =
      jetPower q N bLast logAlpha n
        (fun m' ↦ vdplF coord support p h b bLast logAlpha q N z m') m := by
  induction n generalizing z m with
  | zero => simp [jetPower]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have ihfun :
          iteratedDeriv n
              (fun w ↦ vdplF coord support p h b bLast logAlpha q N w m) =
            fun w ↦ jetPower q N bLast logAlpha n
              (fun m' ↦ vdplF coord support p h b bLast logAlpha q N w m') m := by
        funext w
        exact ih w m
      rw [ihfun]
      exact (hasDerivAt_jetPower_vdplF coord support p h b hbLast logAlpha
        q N n z m).deriv

/-- The exact iterated-derivative formula in the concrete `LevelState`
notation. -/
theorem iteratedDeriv_fWithLogs_eq_jetPower {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hbLast : bLast ≠ 0) (logAlpha : Fin oldRank → ℂ)
    (n : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    iteratedDeriv n (fun w ↦ fWithLogs state b bLast logAlpha w m) z =
      jetPower P.q J bLast logAlpha n
        (fun m' ↦ fWithLogs state b bLast logAlpha z m') m := by
  simpa only [fWithLogs_eq_vdplF] using
    iteratedDeriv_vdplF_eq_jetPower coordinates state.support state.coeff
      P.h b hbLast logAlpha P.q J n z m

/-- Source-logarithm specialization of the iterated jet formula. -/
theorem iteratedDeriv_fSource_eq_jetPower {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hbLast : bLast ≠ 0)
    (n : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    iteratedDeriv n (fun w ↦ fSource state b bLast w m) z =
      jetPower P.q J bLast (oldLog P) n
        (fun m' ↦ fSource state b bLast z m') m := by
  exact iteratedDeriv_fWithLogs_eq_jetPower state b hbLast (oldLog P) n z m

/-- `n` applications of the discrete jet transport only inspect source
multi-indices at total weight at most `weight m + n`.  This is the exact
support statement behind the source's `S/4 + 3S/4` ledger. -/
theorem jetPower_eq_zero_of_weight_add_le {oldRank : ℕ}
    (q N : ℕ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (F : VDPLMultiIndex (oldRank + 1) → ℂ) (n : ℕ)
    (m : VDPLMultiIndex (oldRank + 1))
    (hzero : ∀ m', VDPLMultiIndex.weight m' ≤
        VDPLMultiIndex.weight m + n → F m' = 0) :
    jetPower q N bLast logAlpha n F m = 0 := by
  induction n generalizing m with
  | zero =>
      simpa only [jetPower, Nat.add_zero] using hzero m le_rfl
  | succ n ih =>
      have hinc : ∀ i : Fin (oldRank + 1),
          jetPower q N bLast logAlpha n F (increment m i) = 0 := by
        intro i
        apply ih
        intro m' hm'
        apply hzero m'
        rw [weight_increment] at hm'
        omega
      have hself : jetPower q N bLast logAlpha n F m = 0 := by
        apply ih
        intro m' hm'
        apply hzero m'
        omega
      simp only [jetPower, jetStep, hinc, hself, sub_self, mul_zero,
        Finset.sum_const_zero, add_zero]

/-- Budget-shaped corollary of `jetPower_eq_zero_of_weight_add_le`. -/
theorem jetPower_eq_zero_of_budget {oldRank : ℕ}
    (q N : ℕ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (F : VDPLMultiIndex (oldRank + 1) → ℂ) {S n : ℕ}
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m + n ≤ S)
    (hzero : ∀ m', VDPLMultiIndex.weight m' ≤ S → F m' = 0) :
    jetPower q N bLast logAlpha n F m = 0 := by
  apply jetPower_eq_zero_of_weight_add_le q N bLast logAlpha F n m
  intro m' hm'
  exact hzero m' (hm'.trans hm)

end AnalyticJet

end Erdos240.BakerCoprimeJetTransport

#print axioms Erdos240.BakerCoprimeJetTransport.derivative_poweredDeltaHasse
#print axioms Erdos240.BakerCoprimeJetTransport.mul_simpleDeltaEval
#print axioms Erdos240.BakerCoprimeJetTransport.hasDerivAt_vdplF
#print axioms Erdos240.BakerCoprimeJetTransport.hasDerivAt_fSource
#print axioms Erdos240.BakerCoprimeJetTransport.iteratedDeriv_fSource_eq_jetPower
#print axioms Erdos240.BakerCoprimeJetTransport.jetPower_eq_zero_of_budget
