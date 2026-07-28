import Arxiv.Arxiv2407_19026.TangentCertifiedRound3

/-!
# Main diagonal Ramsey bound

This file closes the three certified optimization rounds and extracts the
advertised eventual bound `R(k,k) < 3.8^k`.
-/

noncomputable section

namespace Arxiv2407_19026

/-- The fully certified final exponent from the three tangent rounds. -/
theorem hasRamseyExponent_main :
    HasRamseyExponent mainRamseyExponent := by
  simpa [mainRamseyExponent] using hasRamseyExponent_beta3

/-- For all sufficiently large `k`, the diagonal Ramsey number is below
`3.8^k`. -/
theorem eventually_diagonal_ramsey_lt_three_point_eight :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (ramseyNumber k k : ℝ) < (19 / 5 : ℝ) ^ k :=
  eventually_diagonal_lt_of_mainRamseyExponent hasRamseyExponent_main

end Arxiv2407_19026
