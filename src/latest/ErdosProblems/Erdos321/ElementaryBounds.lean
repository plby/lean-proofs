import ErdosProblems.Erdos321.FiniteValidity

namespace Erdos321

/-- The extremal function is monotone in its interval endpoint. -/
theorem extremalSize_mono : Monotone extremalSize := by
  intro N M hNM
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  have hAsub : A ⊆ Finset.Icc 1 M := by
    intro a ha
    have haIcc := Finset.mem_Icc.mp (hA.1 ha)
    exact Finset.mem_Icc.mpr ⟨haIcc.1, haIcc.2.trans hNM⟩
  rw [← hcard]
  exact card_le_extremalSize ⟨hAsub, hA.2⟩

/-- Trivial but useful ambient cardinality upper bound. -/
theorem extremalSize_le (N : ℕ) : extremalSize N ≤ N := by
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  have hIntervalCard : (Finset.Icc 1 N).card = N := by simp
  rw [← hcard, ← hIntervalCard]
  exact Finset.card_le_card hA.1

/-- The singleton `{1}` is valid. -/
theorem valid_singleton_one : Valid {1} := by
  simp [Valid, reciprocalSubsetSum]

/-- Every nonempty ambient interval has extremal size at least one. -/
theorem one_le_extremalSize {N : ℕ} (hN : 1 ≤ N) : 1 ≤ extremalSize N := by
  have hAdmissible : Admissible N {1} := by
    constructor
    · simp [hN]
    · exact valid_singleton_one
  simpa using card_le_extremalSize hAdmissible

end Erdos321
