/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 384.
https://www.erdosproblems.com/forum/thread/384

Informal authors:
- E. F. Ecklund Jr.

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos384.md
-/
/-
# Erdős Problem 384

The problem-page formulation uses the strict bound `p < n / 2`.  Ecklund's
published theorem uses the non-strict bound `p ≤ n / 2`; the distinction is
essential.  The strict formulation is false already for `n = 4`, `k = 2`,
since every natural prime is at least `2`.

Mathematical source: E. F. Ecklund, Jr., "On prime divisors of the binomial
coefficient", Pacific J. Math. 29 (1969), 267–270.
-/

import Mathlib

namespace Erdos384

/-- The exceptional coefficient occurs at both symmetric parameter pairs. -/
def IsErdos384Exception (n k : ℕ) : Prop :=
  n = 7 ∧ (k = 3 ∨ k = 4)

/-- The exact strict formulation displayed on the Erdős Problems page.

The inequality `2 * p < n` expresses `p < n / 2` over the rationals without
using truncated natural-number division. -/
def Erdos384StrictStatement : Prop :=
  ∀ n k : ℕ, 1 < k → k < n - 1 → ¬ IsErdos384Exception n k →
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose n k ∧ 2 * p < n

/-- The numerical value of the exceptional symmetric binomial coefficients. -/
lemma exceptional_choose_value :
    Nat.choose 7 3 = 35 ∧ Nat.choose 7 4 = 35 := by
  norm_num [Nat.choose]

/-- At `n = 4`, the interval of natural primes strictly below `n / 2` is
empty, independently of the divisibility condition. -/
lemma no_prime_divisor_strictly_below_half_at_four :
    ¬ ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose 4 2 ∧ 2 * p < 4 := by
  rintro ⟨p, hp, _hdiv, hlt⟩
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- The complete concrete counterexample data for the strict formulation. -/
theorem choose_four_two_counterexample :
    1 < (2 : ℕ) ∧
      2 < 4 - 1 ∧
      ¬ IsErdos384Exception 4 2 ∧
      Nat.choose 4 2 = 6 ∧
      ¬ ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose 4 2 ∧ 2 * p < 4 := by
  refine ⟨by norm_num, by norm_num, ?_, by norm_num [Nat.choose],
    no_prime_divisor_strictly_below_half_at_four⟩
  norm_num [IsErdos384Exception]

/-- Erdős Problem 384, with the strict inequality stated on the problem page,
is false.  The witness is `Nat.choose 4 2 = 6`; its divisor `2` lies exactly
on the boundary `n / 2`. -/
theorem not_erdos_384 :
    ¬ (∀ n k : ℕ, 1 < k → k < n - 1 → ¬ IsErdos384Exception n k →
      ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose n k ∧ 2 * p < n) := by
  intro h
  have hWitness := h 4 2 (by norm_num) (by norm_num)
    (by norm_num [IsErdos384Exception])
  exact no_prime_divisor_strictly_below_half_at_four hWitness

end Erdos384

alias _root_.Erdos384.erdos384_strict_statement_false := _root_.Erdos384.not_erdos_384
