import FinalResults

open Real

theorem erdos47_bloom :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      C * ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)) < rec_sum A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  sorry

theorem erdos47 :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      δ * log N < rec_sum A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  sorry
