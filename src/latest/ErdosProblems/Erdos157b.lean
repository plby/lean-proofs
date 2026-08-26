/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos157b.ParameterSelection

/-!
# An elementary binary-field proof of Erdős Problem 157

Polynomial-sized characteristic-seven tags make the encoding overhead subquadratic,
so the coefficient field can be `ZMod 2`. All masks and prime-specific choices are
sampled together; a single countable avoidance argument supplies eventual coverage.
-/

namespace Erdos157.Binary

/-- An infinite Sidon subset of the natural numbers is an asymptotic additive
basis of order three, by the simplified elementary binary-field construction. -/
theorem erdos_157 :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A → a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, n = a + b + c) := by
  obtain ⟨τ, ω, hbasis⟩ := exists_encoded_asymptoticBasis
  exact ⟨encodedSet CoefficientField τ ω,
    Erdos157.infinite_of_isAsymptoticBasisOfOrderThree hbasis,
    encodedSet_isSidon CoefficientField τ ω, hbasis⟩

end Erdos157.Binary
