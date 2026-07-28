import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Cycle

universe u

namespace SimpleGraph

structure Cycle {α : Type*} (G : SimpleGraph α) where
  vertex : α
  walk : G.Walk vertex vertex
  isCycle : walk.IsCycle

namespace Cycle

def edges {α : Type*} [DecidableEq α] {G : SimpleGraph α}
    (C : G.Cycle) : Finset (Sym2 α) :=
  C.walk.edges.toFinset

end Cycle

structure CycleDoubleCover {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) where
  cycles : List G.Cycle
  coveredTwice :
    ∀ e ∈ G.edgeSet, (cycles.filter fun C ↦ e ∈ C.edges).length = 2

end SimpleGraph

namespace CycleDoubleCoverConjecture

theorem simpleGraph_cycleDoubleCover_iff_every_edge_mem_cycle
    {α : Type u} [Finite α] [DecidableEq α] (G : SimpleGraph α) :
    Nonempty (SimpleGraph.CycleDoubleCover G) ↔
      ∀ e ∈ G.edgeSet, ∃ Z : G.Cycle, e ∈ Z.edges := by
  sorry

end CycleDoubleCoverConjecture
