/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Erdős Problem 915

The phrase “disjoint paths” in the original problem is ambiguous.  For internally
vertex-disjoint paths the Bollobás--Erdős assertion is false.  We formalize that literal
negative resolution with an explicit graph on `17 = 1 + 4 * (5 - 1)` vertices and
`41 = 1 + 4 * Nat.choose 5 2` edges.

The mathematical reconstruction, including the positive edge-disjoint result of Mader,
is in `tex/915.tex`.
-/

namespace Erdos915

open scoped Sym2

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

/-- The internally vertex-disjoint reading of Problem 915, quantified over every finite
simple graph with the stated vertex and edge counts. -/
def Erdos915VertexClaim : Prop :=
  ∀ (m n : ℕ), 2 ≤ m → 1 ≤ n →
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = 1 + n * (m - 1) →
        G.edgeSet.ncard = 1 + n * Nat.choose m 2 →
          HasMInternallyVertexDisjointPaths G m

theorem erdos_915 : ¬ Erdos915VertexClaim := by
  sorry

end Erdos915
