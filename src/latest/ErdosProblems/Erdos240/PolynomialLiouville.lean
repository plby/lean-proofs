/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Data.Real.Basic

/-!
# A rational Liouville bound for integer polynomials

This file records the elementary denominator-clearing estimate used when a
polynomial with integer coefficients is evaluated at a rational number.  The
homogenization of the polynomial gives an explicit integral numerator.
-/

namespace Erdos240.PolynomialLiouville

open Polynomial

/-- The integral numerator obtained by homogenizing `P` to its degree and
evaluating at the numerator and denominator. -/
noncomputable def clearedNumerator (P : ℤ[X]) (a q : ℤ) : ℤ :=
  MvPolynomial.eval ![a, q] (P.homogenize P.natDegree)

/-- Clearing the denominator of `P(a / q)` produces `clearedNumerator P a q`.
This identity is stated in `ℝ`, where it is used for absolute-value bounds. -/
theorem cast_clearedNumerator_eq_mul_pow (P : ℤ[X]) (a q : ℤ) (hq : q ≠ 0) :
    (clearedNumerator P a q : ℝ) =
      P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (q : ℝ)) *
        (q : ℝ) ^ P.natDegree := by
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  have h := Polynomial.eval_homogenize
    (p := P.map (Int.castRingHom ℝ)) (n := P.natDegree)
    (Polynomial.natDegree_map_le) ![(a : ℝ), (q : ℝ)] hqR
  rw [Polynomial.homogenize_map] at h
  change (Int.castRingHom ℝ)
      (MvPolynomial.eval ![a, q] (P.homogenize P.natDegree)) = _
  rw [MvPolynomial.map_eval]
  have hvec : (fun i => ((![a, q] i : ℤ) : ℝ)) =
      ![(a : ℝ), (q : ℝ)] := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro k
        exact Fin.elim0 k
  change MvPolynomial.eval (fun i => ((![a, q] i : ℤ) : ℝ))
      (MvPolynomial.map (Int.castRingHom ℝ) (P.homogenize P.natDegree)) = _
  rw [hvec]
  simpa [Polynomial.eval_map] using h

/-- **Polynomial Liouville bound at a rational point.**

If an integer polynomial does not vanish at `a / q`, then its absolute value
there is at least the reciprocal of the `natDegree P`-th power of the absolute
value of the denominator.  No coprimality assumption on `a` and `q` is needed.
-/
theorem one_div_abs_pow_natDegree_le_abs_eval₂_intCast_div
    (P : ℤ[X]) (a q : ℤ) (hq : q ≠ 0)
    (hne : P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (q : ℝ)) ≠ 0) :
    1 / |(q : ℝ)| ^ P.natDegree ≤
      |P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (q : ℝ))| := by
  let z := clearedNumerator P a q
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  have hqAbs : 0 < |(q : ℝ)| := abs_pos.mpr hqR
  have hzCast : (z : ℝ) =
      P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (q : ℝ)) *
        (q : ℝ) ^ P.natDegree := by
    simpa [z] using cast_clearedNumerator_eq_mul_pow P a q hq
  have hz : z ≠ 0 := by
    intro hz0
    have : (P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (q : ℝ))) *
        (q : ℝ) ^ P.natDegree = 0 := by simpa [hz0] using hzCast.symm
    exact hne (mul_eq_zero.mp this |>.resolve_right (pow_ne_zero _ hqR))
  have honeInt : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
  have honeReal : (1 : ℝ) ≤ |(z : ℝ)| := by
    have honeCast : ((1 : ℤ) : ℝ) ≤ ((|z| : ℤ) : ℝ) := Int.cast_le.mpr honeInt
    simpa only [Int.cast_one, Int.cast_abs] using honeCast
  have hmul : (1 : ℝ) ≤
      |P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (q : ℝ))| *
        |(q : ℝ)| ^ P.natDegree := by
    rw [hzCast, abs_mul, abs_pow] at honeReal
    exact honeReal
  exact (div_le_iff₀ (pow_pos hqAbs P.natDegree)).2 hmul

end Erdos240.PolynomialLiouville

#print axioms Erdos240.PolynomialLiouville.cast_clearedNumerator_eq_mul_pow
#print axioms Erdos240.PolynomialLiouville.one_div_abs_pow_natDegree_le_abs_eval₂_intCast_div
