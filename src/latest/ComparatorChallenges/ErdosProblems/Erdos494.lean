/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped BigOperators

namespace Erdos494

noncomputable section

def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) : Prop :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card →
    sumMultiset A k = sumMultiset B k → A = B

theorem erdos_494.variants.card_eq_2k :
    ∀ k > 2, ¬ Erdos494Unique k (2 * k) := by
  sorry

end

end Erdos494
