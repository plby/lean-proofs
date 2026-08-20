/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Basic definitions for Erdős Problem 485

For a polynomial over `ℚ`, `termCount` is the number of nonzero
coefficients.  The set `squareTermCounts k` consists of all term counts of
squares of polynomials having exactly `k` terms, and `f k` is its least
element.

This file also records the elementary order-theoretic part of the problem:
the infimum is always attained, including at `k = 0`, and any uniform bound

`termCount P ≤ 1 + 32 ^ (2 ^ termCount (P ^ 2))`

for polynomials with at least two terms implies `f k → ∞`.
-/

namespace Erdos485

open Filter Polynomial

noncomputable section

/-- The number of nonzero coefficients (terms) of a rational polynomial. -/
def termCount (P : ℚ[X]) : ℕ :=
  P.support.card

@[simp]
theorem termCount_zero : termCount (0 : ℚ[X]) = 0 := by
  simp [termCount]

@[simp]
theorem termCount_one : termCount (1 : ℚ[X]) = 1 := by
  rw [termCount, ← Polynomial.C_1]
  simp only [Polynomial.support_C one_ne_zero, Finset.card_singleton]

theorem termCount_eq_zero {P : ℚ[X]} : termCount P = 0 ↔ P = 0 := by
  change P.support.card = 0 ↔ P = 0
  exact Polynomial.card_support_eq_zero

/-- The possible numbers of terms in `P²`, as `P` ranges over rational
polynomials having exactly `k` terms. -/
def squareTermCounts (k : ℕ) : Set ℕ :=
  {m | ∃ P : ℚ[X], termCount P = k ∧ termCount (P ^ 2) = m}

/-- An explicit polynomial with support `range k`.  Defining it through its
finitely supported coefficient function makes the `k = 0` case definitionally
the zero polynomial. -/
private def densePolynomial (k : ℕ) : ℚ[X] :=
  ⟨AddMonoidAlgebra.ofCoeff <|
    Finsupp.onFinset (Finset.range k)
      (fun n ↦ if n < k then (1 : ℚ) else 0)
      (by simp_all [Finset.mem_range])⟩

private theorem densePolynomial_support (k : ℕ) :
    (densePolynomial k).support = Finset.range k := by
  ext n
  simp [densePolynomial, Polynomial.support, Finset.mem_range]

private theorem densePolynomial_termCount (k : ℕ) :
    termCount (densePolynomial k) = k := by
  simp [termCount, densePolynomial_support]

/-- For every `k`, there is a rational polynomial with exactly `k` terms;
hence the set over which `f k` is minimized is nonempty. -/
theorem squareTermCounts_nonempty (k : ℕ) : (squareTermCounts k).Nonempty := by
  refine ⟨termCount ((densePolynomial k) ^ 2), densePolynomial k, ?_, rfl⟩
  exact densePolynomial_termCount k

/-- The minimum possible term count in a square of a `k`-term rational
polynomial. -/
def f (k : ℕ) : ℕ :=
  sInf (squareTermCounts k)

/-- The infimum defining `f` is attained by an actual rational polynomial. -/
theorem f_attained (k : ℕ) :
    ∃ P : ℚ[X], termCount P = k ∧ termCount (P ^ 2) = f k := by
  simpa only [f, squareTermCounts, Set.mem_ofPred_eq] using
    Nat.sInf_mem (squareTermCounts_nonempty k)

/-- A conveniently named synonym for `f_attained`. -/
theorem exists_minimizer (k : ℕ) :
    ∃ P : ℚ[X], termCount P = k ∧ termCount (P ^ 2) = f k :=
  f_attained k

/-- `f k` is no larger than the square term count of any particular
`k`-term polynomial. -/
theorem f_minimal {k : ℕ} {P : ℚ[X]} (hP : termCount P = k) :
    f k ≤ termCount (P ^ 2) := by
  exact Nat.sInf_le ⟨P, hP, rfl⟩

/-- There are no terms in the square of a zero-term polynomial. -/
@[simp]
theorem f_zero : f 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using f_minimal (P := (0 : ℚ[X])) termCount_zero

/-- A one-term nonzero polynomial has a one-term square. -/
@[simp]
theorem f_one : f 1 = 1 := by
  apply Nat.le_antisymm
  · simpa using f_minimal (P := (1 : ℚ[X])) termCount_one
  · show 1 ≤ sInf (squareTermCounts 1)
    refine le_csInf (squareTermCounts_nonempty 1) ?_
    intro m hm
    rcases hm with ⟨P, hP, rfl⟩
    have hP0 : P ≠ 0 := by
      intro h
      subst P
      simp at hP
    have hP2 : P ^ 2 ≠ 0 := pow_ne_zero 2 hP0
    simpa only [termCount, Nat.one_le_iff_ne_zero,
      Polynomial.card_support_eq_zero, ne_eq] using hP2

/-- The elementary final step of the resolution of Erdős Problem 485.

The assumed estimate says that a polynomial with at least two terms cannot
have a square with boundedly many terms while its own term count becomes
arbitrarily large.  Applying it to a minimizer for each `k` proves that `f`
tends to infinity. -/
theorem tendsto_f_atTop_of_uniform_bound
    (hbound : ∀ P : ℚ[X], 2 ≤ termCount P →
      termCount P ≤ 1 + 32 ^ (2 ^ termCount (P ^ 2))) :
    Tendsto f atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  refine ⟨2 + 32 ^ (2 ^ B), ?_⟩
  intro k hk
  by_contra hfB
  have hfB' : f k ≤ B := Nat.le_of_lt (Nat.lt_of_not_ge hfB)
  obtain ⟨P, hPk, hP2⟩ := f_attained k
  have hP_ge_two : 2 ≤ termCount P :=
    (Nat.le_add_right 2 (32 ^ (2 ^ B))).trans (hk.trans_eq hPk.symm)
  have hk_upper : k ≤ 1 + 32 ^ (2 ^ f k) := by
    simpa only [hPk, hP2] using hbound P hP_ge_two
  have hpow : 32 ^ (2 ^ f k) ≤ 32 ^ (2 ^ B) :=
    Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hfB')
  omega

end

end Erdos485
