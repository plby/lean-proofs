import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Alternating sums with adjacent correction terms

The adjacent correction terms in an exact-sequence dimension recurrence
cancel in an alternating sum, leaving only the terminal correction.  This
identity applies to arbitrary integer-valued sequences.
-/

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEulerAlgebra

open scoped BigOperators

/-- The alternating sum including the term with index `N`. -/
def alternatingSumThrough (a : ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * a n

@[simp] theorem alternatingSumThrough_zero (a : ℕ → ℤ) :
    alternatingSumThrough a 0 = a 0 := by
  simp [alternatingSumThrough]

/-- Increasing the cutoff adds the next signed term. -/
theorem alternatingSumThrough_succ (a : ℕ → ℤ) (N : ℕ) :
    alternatingSumThrough a (N + 1) =
      alternatingSumThrough a N + (-1 : ℤ) ^ (N + 1) * a (N + 1) :=
  Finset.sum_range_succ (fun n => (-1 : ℤ) ^ n * a n) (N + 1)

/-- The adjacent correction terms telescope to the signed terminal term. -/
theorem alternatingSumThrough_eq_sub_add_last (a b h d : ℕ → ℤ)
    (hzero : h 0 = b 0 - a 0 + d 0)
    (hsucc : ∀ n, h (n + 1) = b (n + 1) - a (n + 1) + d (n + 1) + d n)
    (N : ℕ) :
    alternatingSumThrough h N =
      alternatingSumThrough b N - alternatingSumThrough a N + (-1 : ℤ) ^ N * d N := by
  induction N with
  | zero =>
      simpa only [alternatingSumThrough_zero, pow_zero, one_mul] using hzero
  | succ N hN =>
      rw [alternatingSumThrough_succ h N, alternatingSumThrough_succ b N,
        alternatingSumThrough_succ a N, hN, hsucc N, pow_succ]
      ring

/-- A vanishing terminal correction gives the alternating-sum difference. -/
theorem alternatingSumThrough_eq_sub (a b h d : ℕ → ℤ)
    (hzero : h 0 = b 0 - a 0 + d 0)
    (hsucc : ∀ n, h (n + 1) = b (n + 1) - a (n + 1) + d (n + 1) + d n)
    (N : ℕ) (hd : d N = 0) :
    alternatingSumThrough h N = alternatingSumThrough b N - alternatingSumThrough a N := by
  simpa only [hd, mul_zero, add_zero] using
    alternatingSumThrough_eq_sub_add_last a b h d hzero hsucc N

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEulerAlgebra
