/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos702

def IsUniform {n : ℕ} (k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, A.card = k

def HasSingletonIntersection {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

def twoStarBound (n k : ℕ) : ℕ := Nat.choose (n - 2) (k - 2)

theorem not_erdos_702 :
    ¬ (∀ (n k : ℕ) (𝓕 : Finset (Finset (Fin n))),
      4 ≤ k →
      Erdos702.IsUniform k 𝓕 →
      Nat.choose (n - 2) (k - 2) < 𝓕.card →
      Erdos702.HasSingletonIntersection 𝓕) := by
  sorry

theorem erdos_702_eventually :
    ∀ k : ℕ, 4 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ 𝓕 : Finset (Finset (Fin n)),
        Erdos702.IsUniform k 𝓕 →
        Erdos702.twoStarBound n k < 𝓕.card →
        Erdos702.HasSingletonIntersection 𝓕 := by
  sorry

end Erdos702
