import Mathlib.Algebra.Group.Even
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Erdos363

open Finset

def is_interval (s : Finset ℕ) : Prop := ∃ a b, s = Icc a b
def is_valid_collection (S : List (Finset ℕ)) : Prop :=
  (∀ I ∈ S, is_interval I) ∧
  (∃ k, 4 ≤ k ∧ ∀ I ∈ S, I.card = k) ∧
  (S.Pairwise Disjoint) ∧
  IsSquare ((S.map (fun I => ∏ m ∈ I, m)).prod)
end Erdos363

attribute [local instance] Classical.propDecidable

theorem Erdos363.erdos_363 :
    Not
      (@Set.Finite.{0} (List.{0} (Finset.{0} Nat))
        (@setOf.{0} (List.{0} (Finset.{0} Nat)) fun (S : List.{0} (Finset.{0} Nat)) ↦
          Erdos363.is_valid_collection S))
  := by
  sorry
