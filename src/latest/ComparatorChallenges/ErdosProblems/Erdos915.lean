/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Erdos915

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- The vertices of a path other than its two endpoints. -/
def internalVertices (p : G.Path u v) : Set V :=
  {x | x ∈ (p : G.Walk u v).support ∧ x ≠ u ∧ x ≠ v}

/-- Some two distinct vertices are joined by `m` distinct paths whose interiors are
pairwise disjoint.  Injectivity is essential: a direct path has empty interior and must
not be counted repeatedly. -/
def HasMInternallyVertexDisjointPaths (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v : V, u ≠ v ∧ ∃ paths : Fin m → G.Path u v,
    Function.Injective paths ∧
      Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i))

theorem not_erdos_915 :
    ¬ (∀ (m n : ℕ), 2 ≤ m → 1 ≤ n →
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        Fintype.card V = 1 + n * (m - 1) →
          G.edgeSet.ncard = 1 + n * Nat.choose m 2 →
            Erdos915.HasMInternallyVertexDisjointPaths G m) := by
  sorry

end Erdos915
