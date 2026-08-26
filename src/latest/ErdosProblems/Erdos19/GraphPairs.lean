import ErdosProblems.Erdos19.MatchingFamilyHypergraph
import ErdosProblems.Erdos19.MatchingColorExtension
import ErdosProblems.Erdos19.EdgeDegreePartition

/-! # The hypergraph of all pairs in a graph -/

namespace Erdos19

open _root_.SimpleGraph

variable {V : Type*}

def graphPairs (G : _root_.SimpleGraph V) : SetHypergraph V :=
  matchingEdges (⊤ : G.Subgraph)

theorem graphPairs_pair_iff (G : _root_.SimpleGraph V) (x y : V) :
    ({x, y} : Set V) ∈ graphPairs G ↔ G.Adj x y :=
  matchingEdges_pair_iff _ x y

theorem graphPairs_size (G : _root_.SimpleGraph V) (e : graphPairs G) : e.1.ncard = 2 :=
  matchingEdges_size _ e.2

theorem graphPairs_twoGraph (G : _root_.SimpleGraph V) : (graphPairs G).twoGraph = G := by
  ext x y
  rw [SetHypergraph.twoGraph_adj, graphPairs_pair_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.ne, h⟩⟩

theorem graphPairs_subset (H : SetHypergraph V) (G : _root_.SimpleGraph V)
    (hG : G ≤ H.twoGraph) : graphPairs G ⊆ H := by
  intro e he
  obtain ⟨x, y, hxy, rfl⟩ := he
  exact (hG hxy).2

namespace SetHypergraph

theorem pair_neighbor_ncard_eq_incident [Fintype V] (H : SetHypergraph V)
    (hpair : ∀ e : H, e.1.ncard = 2) (v : V) :
    (H.twoGraph.neighborSet v).ncard = (H.incidentEdges v).ncard := by
  classical
  rw [H.twoGraph_neighbor_ncard]
  let equiv : {e : H.incidentEdges v // e.1.1.ncard = 2} ≃ H.incidentEdges v :=
    { toFun := Subtype.val
      invFun := fun e ↦ ⟨e, hpair e.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_congr equiv

theorem twoGraph_inter (H J : SetHypergraph V) : (H ∩ J).twoGraph = H.twoGraph ⊓ J.twoGraph := by
  ext x y
  change (x ≠ y ∧ (({x, y} : Set V) ∈ H ∧ {x, y} ∈ J)) ↔
    ((x ≠ y ∧ ({x, y} : Set V) ∈ H) ∧ (x ≠ y ∧ ({x, y} : Set V) ∈ J))
  tauto

theorem twoGraph_mono {H J : SetHypergraph V} (hHJ : H ⊆ J) : H.twoGraph ≤ J.twoGraph :=
  fun _ _ h ↦ ⟨h.1, hHJ h.2⟩

theorem graph_pair_inter_incident_degree [Fintype V] (H : SetHypergraph V)
    (G : _root_.SimpleGraph V) (v : V) :
    ((H ∩ graphPairs G).incidentEdges v).ncard =
      ((H.twoGraph ⊓ G).neighborSet v).ncard := by
  rw [← (H ∩ graphPairs G).pair_neighbor_ncard_eq_incident
    (fun e ↦ graphPairs_size G ⟨e.1, e.2.2⟩), twoGraph_inter, graphPairs_twoGraph]

#print axioms graph_pair_inter_incident_degree

end SetHypergraph

end Erdos19
