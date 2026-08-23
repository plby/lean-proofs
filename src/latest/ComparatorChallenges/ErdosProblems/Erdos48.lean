import Mathlib

open scoped ArithmeticFunction.sigma

namespace Erdos48

/-- Natural numbers attained by both Euler's totient and the divisor sum. -/
def CommonValue : Set ℕ :=
  {v | (∃ n : ℕ, n.totient = v) ∧ ∃ m : ℕ, σ 1 m = v}

/-- Infinitely many common values give infinitely many witnessing pairs. -/
lemma infinite_solution_pairs_of_infinite_commonValues
    (h : CommonValue.Infinite) :
    {(n, m) : ℕ × ℕ | n.totient = σ 1 m}.Infinite := by
  sorry

end Erdos48

/-- Erdős Problem 48: Euler's totient and the sum-of-divisors function have
infinitely many common values. -/
theorem erdos_48 :
    True ↔ {(n, m) : ℕ × ℕ | n.totient = σ 1 m}.Infinite := by
  sorry
