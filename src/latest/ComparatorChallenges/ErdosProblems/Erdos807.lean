/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Erdos807.RandomGraph

abbrev Event (n : ℕ) := SimpleGraph (Fin n) → Prop

noncomputable def eventCard (n : ℕ) (P : Event n) : ℕ := by
  exact Set.ncard {G | P G}

noncomputable def probability (n : ℕ) (P : Event n) : ℝ :=
  (eventCard n P : ℝ) / (2 ^ n.choose 2 : ℕ)

def AlmostSurely (P : (n : ℕ) → Event n) : Prop :=
  Tendsto (fun n ↦ probability n (P n)) atTop (𝓝 1)

end Erdos807.RandomGraph

namespace Erdos807

structure Biclique (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  disjoint : Disjoint left right
  complete : ∀ u ∈ left, ∀ v ∈ right, G.Adj u v

namespace Biclique

variable {G : SimpleGraph V}

def edges (B : Biclique G) : Finset (Sym2 V) :=
  B.left.image₂ (fun u v ↦ s(u, v)) B.right

end Biclique

def coveredEdges {G : SimpleGraph V} (p : List (Biclique G)) : Finset (Sym2 V) :=
  p.foldr (fun B E ↦ B.edges ∪ E) ∅

def IsPartitionOn {G : SimpleGraph V} (E : Finset (Sym2 V))
    (p : List (Biclique G)) : Prop :=
  p.Pairwise (fun B C ↦ Disjoint B.edges C.edges) ∧ coveredEdges p = E

noncomputable def graphEdges (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset

def IsBicliquePartition (G : SimpleGraph V)
    (p : List (Biclique G)) : Prop :=
  IsPartitionOn (graphEdges G) p

noncomputable def bipartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ p : List (Biclique G),
    IsBicliquePartition G p ∧ p.length = n}

theorem not_erdos_807 :
    ¬ (RandomGraph.AlmostSurely (fun n G ↦
      Erdos807.bipartitionNumber G = n - G.indepNum)) := by
  sorry

end Erdos807
