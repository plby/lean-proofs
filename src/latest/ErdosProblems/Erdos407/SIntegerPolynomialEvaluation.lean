/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.RankDrop

/-!
# Polynomial evaluation over `ℤ[1/6]`

This file records the elementary product-formula input used in the last
contradiction of the rational three-place Subspace Theorem.  A polynomial
whose coefficients are in `ℤ[1/6]`, evaluated at a `ℤ[1/6]`-point, is again
in `ℤ[1/6]`.  If the value is nonzero, the product of its absolute values at
`∞`, `2`, and `3` is at least one.
-/

namespace Erdos407.RankDrop.SIntegerSix

open scoped BigOperators

/-- Closure of `ℤ[1/6]` under a sum over an arbitrary finite set. -/
theorem finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsSInteger (f i)) :
    IsSInteger (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- Closure of `ℤ[1/6]` under a product over an arbitrary finite set. -/
theorem finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsSInteger (f i)) :
    IsSInteger (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact mul (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- Every natural power of an `S`-integer is an `S`-integer. -/
theorem pow {q : ℚ} (hq : IsSInteger q) :
    ∀ e : ℕ, IsSInteger (q ^ e)
  | 0 => by simpa using one
  | e + 1 => by
      rw [pow_succ]
      exact mul (pow hq e) hq

/-- Evaluation preserves `ℤ[1/6]` when all coefficients and coordinates lie
in `ℤ[1/6]`.  Only coefficients in the finite support are needed. -/
theorem mvPolynomial_eval {ι : Type*} (P : MvPolynomial ι ℚ)
    (x : ι → ℚ)
    (hcoeff : ∀ d ∈ P.support, IsSInteger (P.coeff d))
    (hx : ∀ i, IsSInteger (x i)) :
    IsSInteger (MvPolynomial.eval x P) := by
  classical
  rw [MvPolynomial.eval_eq]
  apply finsetSum P.support
  intro d hd
  apply mul (hcoeff d hd)
  apply finsetProd d.support
  intro i hi
  exact pow (hx i) (d i)

/-- Evaluating an integral polynomial in rational `S`-integers gives an
`S`-integer.  This is the form used for the integral GLR auxiliary
polynomial and all of its integral Hasse derivatives. -/
theorem mvPolynomial_eval₂_int {ι : Type*} (P : MvPolynomial ι ℤ)
    (x : ι → ℚ) (hx : ∀ i, IsSInteger (x i)) :
    IsSInteger (MvPolynomial.eval₂ (Int.castRingHom ℚ) x P) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply finsetSum P.support
  intro d hd
  apply mul (intCast (P.coeff d))
  apply finsetProd d.support
  intro i hi
  exact pow (hx i) (d i)

/-- The restricted product formula for a nonzero polynomial value at an
`S`-integral point. -/
theorem one_le_prod_realPlaceNorm_mvPolynomial_eval {ι : Type*}
    (P : MvPolynomial ι ℚ) (x : ι → ℚ)
    (hcoeff : ∀ d ∈ P.support, IsSInteger (P.coeff d))
    (hx : ∀ i, IsSInteger (x i))
    (hne : MvPolynomial.eval x P ≠ 0) :
    (1 : ℝ) ≤ ∏ v, Erdos407.HeightBoxes.realPlaceNorm v
      (MvPolynomial.eval x P) := by
  rw [Erdos407.RankDrop.prod_realPlaceNorm_eq_normProduct23]
  exact_mod_cast one_le_normProduct23 (mvPolynomial_eval P x hcoeff hx) hne

/-- Integral coefficients are a convenient common special case. -/
theorem one_le_prod_realPlaceNorm_mvPolynomial_eval_of_intCoefficients
    {ι : Type*} (P : MvPolynomial ι ℚ) (x : ι → ℚ)
    (hcoeff : ∀ d ∈ P.support, ∃ z : ℤ, P.coeff d = z)
    (hx : ∀ i, IsSInteger (x i))
    (hne : MvPolynomial.eval x P ≠ 0) :
    (1 : ℝ) ≤ ∏ v, Erdos407.HeightBoxes.realPlaceNorm v
      (MvPolynomial.eval x P) := by
  apply one_le_prod_realPlaceNorm_mvPolynomial_eval P x _ hx hne
  intro d hd
  obtain ⟨z, hz⟩ := hcoeff d hd
  rw [hz]
  exact intCast z

/-- Restricted product formula for a nonzero value of an integral
multivariate polynomial at an `S`-integral point. -/
theorem one_le_prod_realPlaceNorm_mvPolynomial_eval₂_int {ι : Type*}
    (P : MvPolynomial ι ℤ) (x : ι → ℚ)
    (hx : ∀ i, IsSInteger (x i))
    (hne : MvPolynomial.eval₂ (Int.castRingHom ℚ) x P ≠ 0) :
    (1 : ℝ) ≤ ∏ v, Erdos407.HeightBoxes.realPlaceNorm v
      (MvPolynomial.eval₂ (Int.castRingHom ℚ) x P) := by
  rw [Erdos407.RankDrop.prod_realPlaceNorm_eq_normProduct23]
  exact_mod_cast one_le_normProduct23 (mvPolynomial_eval₂_int P x hx) hne

end Erdos407.RankDrop.SIntegerSix
