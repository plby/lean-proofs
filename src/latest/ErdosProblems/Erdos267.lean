import ErdosProblems.Erdos267.Proof

/-!
Colin Snyder and GPT-5.6's F-192 proof claim for Erdős Problem 267,
ported to Lean 4.33.0. See Erdos267/README.md for source and version details.
-/

namespace Erdos267

/-- Every positive increasing index sequence with a uniform ratio gap
greater than one has an irrational reciprocal Fibonacci sum. -/
theorem erdos_267 (n : ℕ → ℕ)
    (hpos : ∀ k : ℕ, 0 < n k) (hmono : StrictMono n)
    (hgap : ∃ c : ℝ, 1 < c ∧
      ∀ k : ℕ, c ≤ (n (k + 1) : ℝ) / (n k : ℝ)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  exact erdos_problem_267 n hpos hmono hgap

end Erdos267

#print axioms Erdos267.erdos_267
