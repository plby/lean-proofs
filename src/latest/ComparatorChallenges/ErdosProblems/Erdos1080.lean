/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1080

universe u

def IsBipartition {V : Type u} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Set.univ ∧ ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∈ Y)

end Erdos1080

theorem Erdos1080.not_erdos_1080 :
    Not (∃ c > (0 : ℝ), ∀ (V : Type) [_finV : Fintype V] [_nonemptyV : Nonempty V]
      (G : SimpleGraph V) (X Y : Set V),
      Erdos1080.IsBipartition G X Y →
      X.ncard = ⌊(Fintype.card V : ℝ) ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
        ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length = 6) := by
  sorry
