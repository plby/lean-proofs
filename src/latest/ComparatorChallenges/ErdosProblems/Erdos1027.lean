import Mathlib

open scoped BigOperators
open Finset

noncomputable section


universe u

namespace Erdos1027

open scoped Classical in
abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)

end Erdos1027

namespace Erdos1027

open scoped Classical in
def IsUniform {α : Type*} [DecidableEq α] (𝓕 : Hypergraph α) (n : ℕ) : Prop :=
  ∀ A ∈ 𝓕, A.card = n

end Erdos1027

namespace Erdos1027

open scoped Classical in
def groundSet {α : Type*} [DecidableEq α] (𝓕 : Hypergraph α) : Finset α :=
  𝓕.biUnion id

end Erdos1027

namespace Erdos1027

open scoped Classical in
noncomputable def goodSets {α : Type*} [DecidableEq α]
    (𝓕 : Hypergraph α) : Finset (Finset α) := by
  classical
  exact (groundSet 𝓕).powerset.filter fun B ↦
    ∀ A ∈ 𝓕, (A ∩ B).Nonempty ∧ ¬A ⊆ B

end Erdos1027

namespace Erdos1027

open scoped Classical in
def RealBudgetResolution : Prop :=
  ∀ c : ℝ, 0 < c →
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (n : ℕ), N ≤ n →
      ∀ (α : Type u) [DecidableEq α] (𝓕 : Hypergraph α),
        IsUniform 𝓕 n →
          (𝓕.card : ℝ) ≤ c * (2 : ℝ) ^ n →
            δ * (2 : ℝ) ^ (groundSet 𝓕).card ≤ (goodSets 𝓕).card

end Erdos1027

namespace Erdos1027

open scoped Classical in
theorem erdos_1027 : RealBudgetResolution.{u} := by
  sorry

end Erdos1027

end
