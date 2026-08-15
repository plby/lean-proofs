import Mathlib

/-!
# Erdős Problem 321: formal statement

For a finite set `A` of positive integers, `Valid A` says that the map sending
`S ⊆ A` to `∑ n ∈ S, 1/n` in `ℚ` is injective.  `extremalSize N` is the
largest cardinality of such an `A` contained in `{1, …, N}`.
-/

namespace Erdos321

/-- The exact rational sum of the reciprocals of the elements of `S`. -/
def reciprocalSubsetSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, ((n : ℚ)⁻¹)

/-- All subset sums of reciprocals from `A` are distinct. -/
def Valid (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powerset, ∀ T ∈ A.powerset,
    reciprocalSubsetSum S = reciprocalSubsetSum T → S = T

/-- `A` is one of the sets allowed by Erdős Problem 321 at parameter `N`. -/
def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ Valid A

/-- The finite collection over which the maximum is taken. -/
noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter Valid

/-- The exact answer to Erdős Problem 321 at parameter `N`. -/
noncomputable def extremalSize (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

/-- Every admissible set has cardinality at most `extremalSize N`. -/
theorem card_le_extremalSize {N : ℕ} {A : Finset ℕ} (hA : Admissible N A) :
    A.card ≤ extremalSize N := by
  classical
  exact Finset.le_sup (by simpa [candidateSets, Admissible] using hA)

/-- The finite supremum defining `extremalSize` is attained by an admissible
set, so this really is a maximum rather than merely an upper bound. -/
theorem exists_extremizer (N : ℕ) :
    ∃ A : Finset ℕ, Admissible N A ∧ A.card = extremalSize N := by
  classical
  have hne : (candidateSets N).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidateSets, Valid]
  obtain ⟨A, hmem, hsup⟩ := Finset.exists_mem_eq_sup (candidateSets N) hne Finset.card
  refine ⟨A, ?_, hsup.symm⟩
  simpa [candidateSets, Admissible] using hmem

/-- An exact proposed answer is correct precisely when it equals the extremal
function at every `N`. -/
def ExactAnswer (answer : ℕ → ℕ) : Prop :=
  ∀ N, answer N = extremalSize N

end Erdos321
