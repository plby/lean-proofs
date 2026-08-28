import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Erdos19

universe u

def cliqueGraph {V : Type u} (s : Set V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ x ∈ s ∧ y ∈ s
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

structure Configuration (n : ℕ) (V : Type u) [Fintype V] where
  blocks : Fin n → Finset V
  card_blocks : ∀ i, (blocks i).card = n
  edge_disjoint : Pairwise fun i j ↦
    Disjoint (cliqueGraph (blocks i : Set V)) (cliqueGraph (blocks j : Set V))
  covers : ∀ v, ∃ i, v ∈ blocks i

namespace Configuration

def graph {n : ℕ} {V : Type u} [Fintype V]
    (C : Configuration n V) : SimpleGraph V :=
  ⨆ i, cliqueGraph (C.blocks i : Set V)

end Configuration

theorem erdos_19 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (V : Type) [Fintype V], ∀ C : Configuration n V,
        C.graph.chromaticNumber = n := by
  sorry

end Erdos19
