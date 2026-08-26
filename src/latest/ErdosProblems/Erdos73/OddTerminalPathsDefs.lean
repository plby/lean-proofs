import ErdosProblems.Erdos73.GraphPaths

/-! Ordinary odd terminal paths and vertex-disjoint families of them. -/

namespace Erdos73

open SimpleGraph
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure IsOddTerminalPath (A : Finset V) (P : GraphPath G) : Prop where
  source_mem : P.source ∈ A
  target_mem : P.target ∈ A
  odd_length : Odd P.walk.length
  internal_disjoint : ∀ v ∈ P.vertexSet, v ∈ A → v = P.source ∨ v = P.target

def HasOddTerminalPathPacking (G : SimpleGraph V) (A : Finset V) (k : ℕ) : Prop :=
  ∃ P : Fin k → GraphPath G, (∀ i, IsOddTerminalPath A (P i)) ∧
    Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet)

def HitsOddTerminalPaths (G : SimpleGraph V) (A X : Finset V) : Prop :=
  ∀ P : GraphPath G, IsOddTerminalPath A P → ¬ Disjoint P.vertexSet X

end Erdos73
