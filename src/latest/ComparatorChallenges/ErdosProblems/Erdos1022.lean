/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1022

abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)
def TwoColorable {α : Type*} [DecidableEq α] (F : Hypergraph α) : Prop :=
  ∃ (c : α → Bool), ∀ A ∈ F, ∃ x y, x ∈ A ∧ y ∈ A ∧ c x ≠ c y

variable (t : ℕ)

theorem not_erdos_1022 :
    ¬ (∃ c : ℕ → ℝ, Filter.Tendsto c Filter.atTop Filter.atTop ∧
    ∀ t, ∀ {α : Type*} [DecidableEq α] (F : Erdos1022.Hypergraph α),
      (∀ A ∈ F, A.card ≥ t) →
      (∀ X : Finset α, X.Nonempty →
        (F.filter (fun A => A ⊆ X)).card < c t * (X.card : ℝ)) →
      Erdos1022.TwoColorable F) := by
  sorry

end Erdos1022
