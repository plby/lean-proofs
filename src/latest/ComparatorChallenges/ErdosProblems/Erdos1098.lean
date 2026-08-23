import Mathlib

namespace Erdos1098

variable {G : Type*} [Group G]

def _root_.Set.PairwiseNonCommuting (S : Set G) : Prop :=
  S.Pairwise fun x y => x * y ≠ y * x


open scoped Classical in
theorem erdos1098 (G : Type*) [Group G]
    (h : ∀ S : Set G, S.PairwiseNonCommuting → S.Finite) :
    ∃ n : ℕ, ∀ S : Finset G,
      (↑S : Set G).PairwiseNonCommuting → S.card ≤ n := by
  sorry

end Erdos1098
