/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.InverseRationalFunction
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic

/-!
# Polynomial models for differenced reciprocal phases

The recursively cleared numerator and denominator from
`InverseRationalFunction` are evaluations of literal polynomials over the
prime field.  This file also records the degree and monicity bounds needed
by the eventual complete rational-character-sum estimate.
-/

namespace Erdos387

open Polynomial

namespace InverseRational

/-- Polynomial denominator of the iterated rational phase. -/
noncomputable def denominatorPolynomial
    (q : ℕ) [NeZero q] (a : ZMod q) : List ℕ → (ZMod q)[X]
  | [] => X + C a
  | h :: hs =>
      (denominatorPolynomial q a hs).comp
          (X + C (((h + 1 : ℕ) : ZMod q))) *
        denominatorPolynomial q a hs

/-- Polynomial numerator of the iterated rational phase. -/
noncomputable def numeratorPolynomial
    (q : ℕ) [NeZero q] (c a : ZMod q) : List ℕ → (ZMod q)[X]
  | [] => C c
  | h :: hs =>
      (numeratorPolynomial q c a hs).comp
          (X + C (((h + 1 : ℕ) : ZMod q))) *
        denominatorPolynomial q a hs -
      numeratorPolynomial q c a hs *
        (denominatorPolynomial q a hs).comp
          (X + C (((h + 1 : ℕ) : ZMod q)))

/-- Evaluation of the polynomial denominator recovers the pointwise
recursive denominator. -/
theorem eval_denominatorPolynomial
    {q : ℕ} [NeZero q] (a : ZMod q) (hs : List ℕ) (x : ℕ) :
    (denominatorPolynomial q a hs).eval (x : ZMod q) =
      denominator q a hs x := by
  induction hs generalizing x with
  | nil => simp [denominatorPolynomial, denominator, add_comm]
  | cons h hs ih =>
      simp only [denominatorPolynomial, denominator, eval_mul, eval_comp,
        eval_add, eval_X, eval_C]
      rw [show (x : ZMod q) + ((h + 1 : ℕ) : ZMod q) =
          ((x + h + 1 : ℕ) : ZMod q) by push_cast; ring, ih, ih]

/-- Evaluation of the polynomial numerator recovers the pointwise recursive
numerator. -/
theorem eval_numeratorPolynomial
    {q : ℕ} [NeZero q] (c a : ZMod q) (hs : List ℕ) (x : ℕ) :
    (numeratorPolynomial q c a hs).eval (x : ZMod q) =
      numerator q c a hs x := by
  induction hs generalizing x with
  | nil => simp [numeratorPolynomial, numerator]
  | cons h hs ih =>
      simp only [numeratorPolynomial, numerator, eval_sub, eval_mul,
        eval_comp, eval_add, eval_X, eval_C]
      rw [show (x : ZMod q) + ((h + 1 : ℕ) : ZMod q) =
          ((x + h + 1 : ℕ) : ZMod q) by push_cast; ring,
        ih, ih, eval_denominatorPolynomial, eval_denominatorPolynomial]

/-- Every denominator polynomial is monic. -/
theorem monic_denominatorPolynomial
    {q : ℕ} [NeZero q] (a : ZMod q) (hs : List ℕ) :
    (denominatorPolynomial q a hs).Monic := by
  induction hs with
  | nil => exact monic_X_add_C a
  | cons h hs ih =>
      exact (ih.comp_X_add_C _).mul ih

/-- The denominator degree doubles at each difference. -/
theorem natDegree_denominatorPolynomial
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (a : ZMod q) (hs : List ℕ) :
    (denominatorPolynomial q a hs).natDegree = 2 ^ hs.length := by
  induction hs with
  | nil => simp [denominatorPolynomial, natDegree_X]
  | cons h hs ih =>
      have hm := monic_denominatorPolynomial a hs
      rw [denominatorPolynomial, (hm.comp_X_add_C _).natDegree_mul hm,
        Polynomial.natDegree_comp, natDegree_X_add_C, mul_one, ih]
      simpa [pow_succ, Nat.mul_comm, two_mul]

/-- The cleared numerator has degree no larger than the denominator.  The
slightly coarser bound is enough for the degree factor in a Weil estimate;
the expected sharper value is `2^j - 1`. -/
theorem natDegree_numeratorPolynomial_le
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (c a : ZMod q) (hs : List ℕ) :
    (numeratorPolynomial q c a hs).natDegree ≤ 2 ^ hs.length := by
  induction hs with
  | nil => simp [numeratorPolynomial]
  | cons h hs ih =>
      let L : (ZMod q)[X] := X + C (((h + 1 : ℕ) : ZMod q))
      let P : (ZMod q)[X] := numeratorPolynomial q c a hs
      let Q : (ZMod q)[X] := denominatorPolynomial q a hs
      have hL : L.natDegree = 1 := by
        change (X + C (((h + 1 : ℕ) : ZMod q))).natDegree = 1
        exact natDegree_X_add_C _
      have hQ : Q.natDegree = 2 ^ hs.length := by
        exact natDegree_denominatorPolynomial a hs
      have hP : P.natDegree ≤ 2 ^ hs.length := ih
      have hshiftP : (P.comp L).natDegree ≤ 2 ^ hs.length := by
        calc
          (P.comp L).natDegree ≤ P.natDegree * L.natDegree :=
            natDegree_comp_le
          _ ≤ (2 ^ hs.length) * 1 := Nat.mul_le_mul hP (le_of_eq hL)
          _ = 2 ^ hs.length := Nat.mul_one _
      have hshiftQ : (Q.comp L).natDegree = 2 ^ hs.length := by
        rw [Polynomial.natDegree_comp, hL, mul_one, hQ]
      have hleft : (P.comp L * Q).natDegree ≤
          2 ^ hs.length + 2 ^ hs.length := by
        exact natDegree_mul_le.trans (Nat.add_le_add hshiftP (le_of_eq hQ))
      have hright : (P * Q.comp L).natDegree ≤
          2 ^ hs.length + 2 ^ hs.length := by
        exact natDegree_mul_le.trans (Nat.add_le_add hP (le_of_eq hshiftQ))
      change (P.comp L * Q - P * Q.comp L).natDegree ≤
        2 ^ (h :: hs).length
      calc
        (P.comp L * Q - P * Q.comp L).natDegree ≤
            max (P.comp L * Q).natDegree (P * Q.comp L).natDegree :=
          natDegree_sub_le _ _
        _ ≤ 2 ^ hs.length + 2 ^ hs.length := max_le hleft hright
        _ = 2 ^ (h :: hs).length := by
          simp [pow_succ, Nat.mul_comm, two_mul]

end InverseRational

end Erdos387
