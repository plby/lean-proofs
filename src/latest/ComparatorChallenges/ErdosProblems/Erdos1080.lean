import Mathlib

namespace Erdos1080

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

open SimpleGraph

universe u

def IsBipartition {V : Type u} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Set.univ ∧ ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∈ Y)

def erdos_1080 : Prop :=
    ∃ c > (0 : ℝ), ∀ (V : Type) [_finV : Fintype V] [_nonemptyV : Nonempty V]
      (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y →
      X.ncard = ⌊(Fintype.card V : ℝ) ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
        ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length = 6
end Erdos1080

attribute [local instance] Classical.propDecidable

theorem Erdos1080.not_erdos_1080 :
    Not Erdos1080.erdos_1080
  := by
  sorry
