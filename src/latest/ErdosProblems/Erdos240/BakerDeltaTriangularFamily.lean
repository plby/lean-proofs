/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerTriangularTransport
import ErdosProblems.Erdos240.Delta
import Mathlib.Analysis.Complex.Basic

/-!
# Ordinary Delta families for the p. 51 transport

The old-coordinate factors in source equation (3) are the ordinary
two-argument polynomials

`Delta(Y;m) = (Y+1)...(Y+m)/m!`,

not a Hasse derivative of a fixed power of `Delta`.  As `m` ranges from
`0` to `S`, these polynomials have the consecutive exact degrees needed by
`BakerTriangularTransport`.  This file packages that family over both `ℚ`
and `ℂ`, together with its affine residue lift `Y ↦ qY+c`.
-/

open scoped Polynomial

noncomputable section

namespace Erdos240.BakerDeltaTriangularFamily

open Polynomial
open Erdos240Delta
open Erdos240.BakerTriangularTransport

/-- The rational Delta numerator is monic. -/
theorem monic_deltaNumerator (h : ℕ) : (deltaNumerator h).Monic := by
  rw [deltaNumerator_eq]
  exact (monic_ascPochhammer ℚ h).comp (monic_X_add_C (1 : ℚ)) (by
    have hx : (X + (1 : ℚ[X])).natDegree = 1 := by
      simpa only [← Polynomial.C_1] using
        Polynomial.natDegree_X_add_C (1 : ℚ)
    rw [hx]
    exact one_ne_zero)

/-- Exact degree of the normalized binomial polynomial. -/
theorem natDegree_delta (h : ℕ) : (delta h).natDegree = h := by
  rw [delta, Polynomial.natDegree_C_mul (by positivity)]
  rw [deltaNumerator_eq, Polynomial.natDegree_comp,
    ascPochhammer_natDegree]
  have hx : (X + (1 : ℚ[X])).natDegree = 1 := by
    simpa only [← Polynomial.C_1] using
      Polynomial.natDegree_X_add_C (1 : ℚ)
  rw [hx, Nat.mul_one]

theorem leadingCoeff_delta_ne_zero (h : ℕ) :
    (delta h).leadingCoeff ≠ 0 := by
  rw [delta, (monic_deltaNumerator h).leadingCoeff_C_mul]
  positivity

/-- The literal rational source family `m ↦ Delta(Y;m)`. -/
def ordinaryDeltaFamilyRat (S : ℕ) : PolynomialFamily ℚ S where
  polynomial m := delta (m : ℕ)
  degree m := natDegree_delta m
  leadingCoeff_ne_zero m := leadingCoeff_delta_ne_zero m

@[simp] theorem ordinaryDeltaFamilyRat_polynomial (S : ℕ)
    (m : Fin (S + 1)) :
    (ordinaryDeltaFamilyRat S).polynomial m = delta (m : ℕ) := rfl

/-- The complex-coefficient form used by the analytic auxiliary function. -/
def ordinaryDeltaFamilyComplex (S : ℕ) : PolynomialFamily ℂ S where
  polynomial m := (delta (m : ℕ)).map (algebraMap ℚ ℂ)
  degree m := by
    rw [Polynomial.natDegree_map_eq_of_injective
      (algebraMap ℚ ℂ).injective, natDegree_delta]
  leadingCoeff_ne_zero m := by
    rw [Polynomial.leadingCoeff_map_of_injective
      (algebraMap ℚ ℂ).injective]
    simpa using
      (algebraMap ℚ ℂ).injective.ne (leadingCoeff_delta_ne_zero m)

@[simp] theorem ordinaryDeltaFamilyComplex_polynomial (S : ℕ)
    (m : Fin (S + 1)) :
    (ordinaryDeltaFamilyComplex S).polynomial m =
      (delta (m : ℕ)).map (algebraMap ℚ ℂ) := rfl

theorem eval_ordinaryDeltaFamilyComplex (S : ℕ) (m : Fin (S + 1))
    (y : ℂ) :
    ((ordinaryDeltaFamilyComplex S).polynomial m).eval y =
      Polynomial.eval₂ (algebraMap ℚ ℂ) y (delta (m : ℕ)) := by
  exact Polynomial.eval_map (algebraMap ℚ ℂ) y

/-- The rational residue-lifted family `Delta(qY+c;m)`. -/
def affineOrdinaryDeltaFamilyRat (S : ℕ) (q c : ℚ) (hq : q ≠ 0) :
    PolynomialFamily ℚ S :=
  (ordinaryDeltaFamilyRat S).affineComp q c hq

theorem eval_affineOrdinaryDeltaFamilyRat (S : ℕ)
    (q c : ℚ) (hq : q ≠ 0) (m : Fin (S + 1)) (y : ℚ) :
    ((affineOrdinaryDeltaFamilyRat S q c hq).polynomial m).eval y =
      (delta (m : ℕ)).eval (q * y + c) := by
  exact (ordinaryDeltaFamilyRat S).eval_affineComp q c hq m y

/-- The complex residue-lifted family used directly in equation (12). -/
def affineOrdinaryDeltaFamilyComplex (S : ℕ)
    (q c : ℂ) (hq : q ≠ 0) : PolynomialFamily ℂ S :=
  (ordinaryDeltaFamilyComplex S).affineComp q c hq

theorem eval_affineOrdinaryDeltaFamilyComplex (S : ℕ)
    (q c : ℂ) (hq : q ≠ 0) (m : Fin (S + 1)) (y : ℂ) :
    ((affineOrdinaryDeltaFamilyComplex S q c hq).polynomial m).eval y =
      Polynomial.eval₂ (algebraMap ℚ ℂ) (q * y + c) (delta (m : ℕ)) := by
  unfold affineOrdinaryDeltaFamilyComplex
  rw [(ordinaryDeltaFamilyComplex S).eval_affineComp q c hq,
    eval_ordinaryDeltaFamilyComplex]

end Erdos240.BakerDeltaTriangularFamily

#print axioms Erdos240.BakerDeltaTriangularFamily.monic_deltaNumerator
#print axioms Erdos240.BakerDeltaTriangularFamily.ordinaryDeltaFamilyRat
#print axioms Erdos240.BakerDeltaTriangularFamily.ordinaryDeltaFamilyComplex
#print axioms Erdos240.BakerDeltaTriangularFamily.eval_affineOrdinaryDeltaFamilyRat
#print axioms Erdos240.BakerDeltaTriangularFamily.eval_affineOrdinaryDeltaFamilyComplex
