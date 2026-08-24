/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos737

variable {V : Type u}

def ChromaticNumberAlephOne (G : SimpleGraph V) : Prop :=
  Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ IsEmpty (G.Coloring ℕ)

end Erdos737

def CycleThroughEdgeOfLength {V : Type} (G : SimpleGraph V)
    (e : Sym2 V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v,
    c.IsCycle ∧ c.length = n ∧ e ∈ c.edges

theorem erdos_737 :
    ∀ (V : Type) (G : SimpleGraph V), Erdos737.ChromaticNumberAlephOne G →
      ∃ e ∈ G.edgeSet, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        CycleThroughEdgeOfLength G e n := by
  sorry
