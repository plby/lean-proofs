import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

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

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos1022.not_erdos_1022 :
    Not Erdos1022.erdos_1022.{u_1}
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
