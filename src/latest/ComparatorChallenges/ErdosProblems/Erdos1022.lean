/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1022

open Finset

abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)
def TwoColorable {α : Type*} [DecidableEq α] (F : Hypergraph α) : Prop :=
  ∃ (c : α → Bool), ∀ A ∈ F, ∃ x y, x ∈ A ∧ y ∈ A ∧ c x ≠ c y
open Finset

variable (t : ℕ)

def erdos_1022 : Prop :=
  ∃ c : ℕ → ℝ, Filter.Tendsto c Filter.atTop Filter.atTop ∧
  ∀ t, ∀ {α : Type*} [DecidableEq α] (F : Hypergraph α),
    (∀ A ∈ F, A.card ≥ t) →
    (∀ X : Finset α, X.Nonempty →
      (F.filter (fun A => A ⊆ X)).card < c t * (X.card : ℝ)) →
    TwoColorable F
end Erdos1022

open Finset

namespace Erdos1022

open scoped Classical in
theorem not_erdos_1022 : ¬ erdos_1022 := by
  sorry

end Erdos1022
