import ErdosProblems.Erdos788.Proof

/-!
Lean version: 4.33.0 (ported from 4.27.0).
Formal author: Shouqiao Wang; formalization model unspecified upstream.
See Erdos788/README.md for source and attribution details.
-/

namespace Erdos788

/-- The original maximum has asymptotic exponent one half. -/
theorem erdos_788 :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε) :=
  hasExponentOneHalf

/-- A fixed square-root logarithmic lower bound and a quantitative upper exponent. -/
theorem erdos_788_quantitative :
    (∀ n : ℕ, 3 ≤ n →
      (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (f n : ℝ)) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + C *
        (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ^ (1 / 3 : ℝ)) := by
  obtain ⟨hlower, ⟨C, hC, n₀, hn₀, hbound⟩, _⟩ := paperMainTheorem
  refine ⟨hlower, C, hC, n₀, hn₀, ?_⟩
  intro n hn
  exact (hbound n hn).2

end Erdos788

#print axioms Erdos788.erdos_788
#print axioms Erdos788.erdos_788_quantitative
