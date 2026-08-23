import Mathlib

open Filter
open scoped Topology SimpleGraph

noncomputable section


variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Erdos807.RandomGraph

open scoped Classical in
abbrev Event (n : ℕ) := SimpleGraph (Fin n) → Prop

end Erdos807.RandomGraph

namespace Erdos807.RandomGraph

open scoped Classical in
noncomputable def eventCard (n : ℕ) (P : Event n) : ℕ := by
  exact Set.ncard {G | P G}

end Erdos807.RandomGraph

namespace Erdos807.RandomGraph

open scoped Classical in
noncomputable def probability (n : ℕ) (P : Event n) : ℝ :=
  (eventCard n P : ℝ) / (2 ^ n.choose 2 : ℕ)

end Erdos807.RandomGraph

namespace Erdos807.RandomGraph

open scoped Classical in
def AlmostSurely (P : (n : ℕ) → Event n) : Prop :=
  Tendsto (fun n ↦ probability n (P n)) atTop (𝓝 1)

end Erdos807.RandomGraph

namespace Erdos807

open scoped Classical in
structure Biclique (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  disjoint : Disjoint left right
  complete : ∀ u ∈ left, ∀ v ∈ right, G.Adj u v

end Erdos807

namespace Erdos807.Biclique

variable {G : SimpleGraph V}

open scoped Classical in
def edges (B : Biclique G) : Finset (Sym2 V) :=
  B.left.image₂ (fun u v ↦ s(u, v)) B.right

end Erdos807.Biclique

namespace Erdos807

open scoped Classical in
def coveredEdges {G : SimpleGraph V} (p : List (Biclique G)) : Finset (Sym2 V) :=
  p.foldr (fun B E ↦ B.edges ∪ E) ∅

end Erdos807

namespace Erdos807

open scoped Classical in
def IsPartitionOn {G : SimpleGraph V} (E : Finset (Sym2 V))
    (p : List (Biclique G)) : Prop :=
  p.Pairwise (fun B C ↦ Disjoint B.edges C.edges) ∧ coveredEdges p = E

end Erdos807

namespace Erdos807

open scoped Classical in
noncomputable def graphEdges (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset

end Erdos807

namespace Erdos807

open scoped Classical in
def IsBicliquePartition (G : SimpleGraph V)
    (p : List (Biclique G)) : Prop :=
  IsPartitionOn (graphEdges G) p

end Erdos807

namespace Erdos807

open scoped Classical in
noncomputable def bipartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ p : List (Biclique G),
    IsBicliquePartition G p ∧ p.length = n}

end Erdos807

namespace Erdos807

open scoped Classical in
def Erdos807Conjecture : Prop :=
  RandomGraph.AlmostSurely (fun n G ↦
    bipartitionNumber G = n - G.indepNum)

end Erdos807

namespace Erdos807

open scoped Classical in
theorem erdos_807 : ¬ Erdos807Conjecture := by
  sorry

end Erdos807

end
