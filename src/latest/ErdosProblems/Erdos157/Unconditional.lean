import ErdosProblems.Erdos157.ParameterSelection

/-!
# Erdős problem 157

An unconditional elementary construction of an infinite Sidon set that is an
asymptotic basis of order three. The proof uses the standard Lean logical axioms,
with no additional axioms, proof placeholders, or increased computational limits.
-/

namespace Erdos157

open Elementary Elementary.AuxiliaryModuli

/-- There exists an infinite Sidon subset of the natural numbers that is an
asymptotic basis of order three. -/
theorem erdos_157 : ∃ S : Set ℕ, S.Infinite ∧ IsSidon S ∧ IsAsymptoticBasisOfOrderThree S := by
  obtain ⟨τ, ω, hbasis⟩ := exists_encoded_asymptoticBasis
  exact ⟨encodedSet CoefficientField τ ω, infinite_of_isAsymptoticBasisOfOrderThree hbasis,
    encodedSet_isSidon CoefficientField τ ω, hbasis⟩

end Erdos157
