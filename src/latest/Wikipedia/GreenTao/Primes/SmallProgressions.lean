import Wikipedia.GreenTao.ArithmeticProgression.Basic

/-!
# Prime progressions of length at most two

The analytic Green--Tao argument is only needed from length three onward.
This file closes the small lengths directly, so the final assembly can work
under the standing hypothesis `3 ≤ k`.
-/

namespace Wikipedia.SzemeredisTheorem

/-- The primes contain the progression `2, 3`. -/
theorem containsAP_primes_two :
    ContainsAP {p : ℕ | Nat.Prime p} 2 := by
  refine ⟨2, 1, Nat.zero_lt_one, ?_⟩
  intro j hj
  have hj_cases : j = 0 ∨ j = 1 := by
    omega
  rcases hj_cases with rfl | rfl
  · simpa using Nat.prime_two
  · simpa using Nat.prime_three

/-- All lengths below three are handled by truncating `2, 3`. -/
theorem containsAP_primes_of_le_two {k : ℕ} (hk : k ≤ 2) :
    ContainsAP {p : ℕ | Nat.Prime p} k :=
  containsAP_primes_two.take hk

end Wikipedia.SzemeredisTheorem
