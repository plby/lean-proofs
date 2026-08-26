import Mathlib

open Set
open scoped SimpleGraph Function

namespace Erdos73

def EverySubgraphHasLargeIndepSet {V : Type*} [Finite V]
    (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, H.verts.ncard ≤ 2 * H.coe.indepNum + k

def BipartiteAfterDeletingAtMost {V : Type*}
    (C : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ X : Finset V, X.card ≤ C ∧
    (G.induce (X : Set V)ᶜ).IsBipartite

def Problem73 : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    EverySubgraphHasLargeIndepSet k G →
      BipartiteAfterDeletingAtMost C G

theorem erdos_73 : Problem73 := by
  sorry

end Erdos73
