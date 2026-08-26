import ErdosProblems.Erdos538.Proof

/-!
Colin Snyder and GPT-5.6's matching-order proof claim for Erdős Problem 538,
ported to Lean 4.33.0. See Erdos538/README.md for source and version details.
-/

namespace Erdos538

/-- An explicit universal upper estimate and matching admissible witnesses. -/
theorem erdos_538 (r N : ℕ) (hr : 2 ≤ r) (hN : 2 ≤ N) :
    (∀ A : Finset ℕ, Admissible r N A →
      Real.log (Real.log (N + 1)) * (reciprocalMass A : ℝ) ≤
        2 * r * (1 + Real.log (N * N))) ∧
    (∃ A : Finset ℕ, Admissible r N A ∧
      Real.log (N + 1) ≤
        4 + (8192 * (Nat.log 2 (Nat.log 2 N) + 1) : ℕ) *
          (reciprocalMass A : ℝ)) := by
  exact erdos538_matching_order r N hr hN

end Erdos538

#print axioms Erdos538.erdos_538
