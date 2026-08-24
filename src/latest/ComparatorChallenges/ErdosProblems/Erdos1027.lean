/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

universe u

namespace Erdos1027

abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)

def IsUniform {α : Type*} [DecidableEq α] (𝓕 : Hypergraph α) (n : ℕ) : Prop :=
  ∀ A ∈ 𝓕, A.card = n

def groundSet {α : Type*} [DecidableEq α] (𝓕 : Hypergraph α) : Finset α :=
  𝓕.biUnion id

noncomputable def goodSets {α : Type*} [DecidableEq α]
    (𝓕 : Hypergraph α) : Finset (Finset α) := by
  classical
  exact (groundSet 𝓕).powerset.filter fun B ↦
    ∀ A ∈ 𝓕, (A ∩ B).Nonempty ∧ ¬A ⊆ B

theorem erdos_1027 :
    ∀ c : ℝ, 0 < c →
      ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
        ∀ (n : ℕ), N ≤ n →
        ∀ (α : Type u) [DecidableEq α] (𝓕 : Erdos1027.Hypergraph α),
          Erdos1027.IsUniform 𝓕 n →
            (𝓕.card : ℝ) ≤ c * (2 : ℝ) ^ n →
              δ * (2 : ℝ) ^ (Erdos1027.groundSet 𝓕).card ≤ (Erdos1027.goodSets 𝓕).card := by
  sorry

end Erdos1027
