import Mathlib

open Function Set SimpleGraph
open scoped Ordinal Sym2

noncomputable section


namespace Erdos737

variable {V : Type u}

open scoped Classical in
def ChromaticNumberAlephOne (G : SimpleGraph V) : Prop :=
  Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ IsEmpty (G.Coloring ℕ)

end Erdos737

open scoped Classical in
def CycleThroughEdgeOfLength {V : Type} (G : SimpleGraph V)
    (e : Sym2 V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v,
    c.IsCycle ∧ c.length = n ∧ e ∈ c.edges

open scoped Classical in
theorem erdos_737 :
    ∀ (V : Type) (G : SimpleGraph V), Erdos737.ChromaticNumberAlephOne G →
      ∃ e ∈ G.edgeSet, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        CycleThroughEdgeOfLength G e n := by
  sorry

end
