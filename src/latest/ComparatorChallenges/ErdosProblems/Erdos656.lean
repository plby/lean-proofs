/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos656

noncomputable def countIn (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range N).filter (· ∈ A)).card

noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => (countIn A N : ℝ) / N) Filter.atTop

def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  0 < upperDensity A

def HasTranslatedRestrictedPairSums (A B : Set ℕ) : Prop :=
  ∃ t : ℤ, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
    ∃ a ∈ A, (a : ℤ) = (b₁ : ℤ) + b₂ + t

theorem erdos_656 {A : Set ℕ} (hA : HasPositiveUpperDensity A) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
      HasTranslatedRestrictedPairSums A B := by
  sorry

end Erdos656
