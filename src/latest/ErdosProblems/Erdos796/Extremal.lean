import ErdosProblems.Erdos796.Core

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite extremal interpretation of `g3`

The definition of `g3` is a finite supremum over the admissible subsets of
`positiveIcc n`.  This file records that every admissible set is bounded by
that supremum and, conversely, that the supremum is attained by an admissible
set.
-/

namespace Erdos796

/-- The finite collection of admissible subsets of `[1,n]`. -/
noncomputable def admissibleCandidates (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (positiveIcc n).powerset.filter (Admissible n)

/-- The empty set is admissible for every ambient interval. -/
theorem empty_admissible (n : ℕ) : Admissible n ∅ := by
  constructor
  · simp
  · intro m
    simp [strictProductRepCount]

/-- The finite collection over which `g3 n` is defined is nonempty. -/
theorem admissibleCandidates_nonempty (n : ℕ) :
    (admissibleCandidates n).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [admissibleCandidates, empty_admissible]

/-- Every admissible subset of `[1,n]` has cardinality at most `g3 n`. -/
theorem card_le_g3 {n : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    A.card ≤ g3 n := by
  classical
  unfold g3
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA.1, hA⟩

/-- The finite supremum defining `g3 n` is attained by an admissible set. -/
theorem g3_attained (n : ℕ) :
    ∃ A : Finset ℕ, Admissible n A ∧ A.card = g3 n := by
  classical
  let candidates := admissibleCandidates n
  have hcandidates : candidates.Nonempty := by
    simpa [candidates] using! admissibleCandidates_nonempty n
  obtain ⟨A, hA, hmax⟩ :=
    Finset.exists_mem_eq_sup candidates hcandidates Finset.card
  refine ⟨A, ?_, ?_⟩
  · have hA' : A ∈ (positiveIcc n).powerset.filter (Admissible n) := by
      simpa [candidates, admissibleCandidates] using! hA
    exact (Finset.mem_filter.mp hA').2
  · simpa [g3, candidates, admissibleCandidates] using! hmax.symm

end Erdos796
