/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1098

variable {G : Type*} [Group G]

def _root_.Set.PairwiseNonCommuting (S : Set G) : Prop :=
  S.Pairwise fun x y => x * y ≠ y * x

theorem erdos_1098 (G : Type*) [Group G]
    (h : ∀ S : Set G, S.PairwiseNonCommuting → S.Finite) :
    ∃ n : ℕ, ∀ S : Finset G,
      (↑S : Set G).PairwiseNonCommuting → S.card ≤ n := by
  sorry

end Erdos1098
