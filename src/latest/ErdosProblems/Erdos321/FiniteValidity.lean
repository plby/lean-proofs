import ErdosProblems.Erdos321.Basic

namespace Erdos321

/-- A computationally decidable formulation of validity, quantifying over the
finite subtype of the powerset rather than over all finsets. -/
def FiniteValid (A : Finset ℕ) : Prop :=
  ∀ S T : {s : Finset ℕ // s ∈ A.powerset}, S ≠ T →
    reciprocalSubsetSum S.1 ≠ reciprocalSubsetSum T.1

instance (A : Finset ℕ) : Decidable (FiniteValid A) := by
  unfold FiniteValid
  infer_instance

/-- The finite decidable formulation is exactly the original validity
predicate. -/
theorem valid_iff_finiteValid (A : Finset ℕ) : Valid A ↔ FiniteValid A := by
  constructor
  · intro h S T hne hEq
    apply hne
    apply Subtype.ext
    exact h S.1 S.2 T.1 T.2 hEq
  · intro h S hS T hT hEq
    by_contra hne
    exact h ⟨S, hS⟩ ⟨T, hT⟩ (by simpa using hne) hEq

end Erdos321
