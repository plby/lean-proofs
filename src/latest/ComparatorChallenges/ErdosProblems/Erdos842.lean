/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open SimpleGraph

namespace Erdos842

def cyclePart {V : Type*} (n : ℕ) (cycleOrder : Fin (3 * n) ≃ V) : SimpleGraph V :=
  (cycleGraph (3 * n)).map cycleOrder.toEmbedding

def triangleFactor {V : Type*} (n : ℕ) (triangleCoord : V ≃ Fin n × Fin 3) :
    SimpleGraph V :=
  ((completeEquipartiteGraph n 3)ᶜ).comap triangleCoord

def IsCyclePlusTriangles {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (cycleOrder : Fin (3 * n) ≃ V) (triangleCoord : V ≃ Fin n × Fin 3),
    Disjoint (cyclePart n cycleOrder) (triangleFactor n triangleCoord) ∧
      G = cyclePart n cycleOrder ⊔ triangleFactor n triangleCoord

theorem erdos_842 {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (hG : IsCyclePlusTriangles G n) :
    G.chromaticNumber ≤ 3 := by
  sorry

end Erdos842
