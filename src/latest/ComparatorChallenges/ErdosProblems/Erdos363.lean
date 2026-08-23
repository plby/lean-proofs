import Mathlib

namespace Erdos363

open Finset

def is_interval (s : Finset ℕ) : Prop := ∃ a b, s = Icc a b
def is_valid_collection (S : List (Finset ℕ)) : Prop :=
  (∀ I ∈ S, is_interval I) ∧
  (∃ k, 4 ≤ k ∧ ∀ I ∈ S, I.card = k) ∧
  (S.Pairwise Disjoint) ∧
  IsSquare ((S.map (fun I => ∏ m ∈ I, m)).prod)
end Erdos363


open Finset

namespace Erdos363

open scoped Classical in
theorem erdos_363 : ¬ Set.Finite { S | is_valid_collection S } := by
  sorry

end Erdos363
