import Mathlib

namespace VinogradovsTheorem

/-- Every sufficiently large odd natural number is the sum of three pairwise
 distinct primes. -/
theorem vinogradovs_theorem :
    ∃ N : ℕ, ∀ n : ℕ, N < n → Odd n →
      ∃ p q r : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
          p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p + q + r := by
  sorry

end VinogradovsTheorem
