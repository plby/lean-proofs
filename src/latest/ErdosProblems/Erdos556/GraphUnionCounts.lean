import ErdosProblems.Erdos556.ThreeColourTools
import ErdosProblems.Erdos556.MappedDensity
import ErdosProblems.Erdos556.ComplementEdgeCounts

/-! Edge counts for disjoint finite unions of colour graphs. -/

namespace Erdos556

open SimpleGraph Finset

open scoped Classical in
theorem edgeFinset_iSup {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G : I → SimpleGraph V) : (⨆ i, G i).edgeFinset = univ.biUnion (fun i => (G i).edgeFinset) := by
  ext e
  simp only [mem_edgeFinset, edgeSet_iSup, Set.mem_iUnion, mem_biUnion, mem_univ, true_and]

theorem natCard_edges_iSup {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G : I → SimpleGraph V) (hdis : ∀ i j, i ≠ j → Disjoint (G i) (G j)) :
    Nat.card (⨆ i, G i).edgeSet = ∑ i, Nat.card (G i).edgeSet := by
  classical
  have hd : ((univ : Finset I) : Set I).Pairwise (fun i j => Disjoint (G i).edgeFinset (G j).edgeFinset) := by
    intro i _ j _ hij
    exact SimpleGraph.disjoint_edgeFinset.mpr (hdis i j hij)
  have h : (⨆ i, G i).edgeFinset.card = ∑ i, (G i).edgeFinset.card := by
    rw [edgeFinset_iSup, card_biUnion hd]
  simpa only [edgeFinset_card_eq_natCard_edgeSet] using h

theorem natCard_edges_sup {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (hdis : Disjoint G H) :
    Nat.card (G ⊔ H).edgeSet = Nat.card G.edgeSet + Nat.card H.edgeSet := by
  classical
  have h : (G ⊔ H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
    rw [edgeFinset_sup, card_union_of_disjoint (SimpleGraph.disjoint_edgeFinset.mpr hdis)]
  simpa only [edgeFinset_card_eq_natCard_edgeSet] using h

theorem natCard_edges_add_complement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Nat.card G.edgeSet + Nat.card Gᶜ.edgeSet = Nat.card (⊤ : SimpleGraph V).edgeSet := by
  classical
  have h := edge_count_add_complement G
  have ht := card_edgeFinset_top_eq_card_choose_two (V := V)
  simp only [edgeFinset_card_eq_natCard_edgeSet] at h ht
  exact h.trans ht.symm

theorem ThreeColouring.graphs_disjoint {V : Type*} (c : ThreeColouring V)
    (i j : Fin 3) (hij : i ≠ j) : Disjoint (c.graph i) (c.graph j) := by
  apply SimpleGraph.disjoint_left.mpr
  intro u v hi hj
  exact hij (hi.2.symm.trans hj.2)

theorem ThreeColouring.iSup_graph_eq_top {V : Type*} (c : ThreeColouring V) :
    (⨆ i, c.graph i) = ⊤ := by
  ext u v
  rw [iSup_adj, top_adj]
  constructor
  · rintro ⟨i, hi⟩
    exact hi.1
  · intro huv
    exact ⟨c.colour u v, huv, rfl⟩

theorem ThreeColouring.sum_edge_counts {V : Type*} [Fintype V] [DecidableEq V]
    (c : ThreeColouring V) :
    (∑ i, Nat.card (c.graph i).edgeSet) = Nat.card (⊤ : SimpleGraph V).edgeSet := by
  have h := natCard_edges_iSup c.graph c.graphs_disjoint
  rw [c.iSup_graph_eq_top] at h
  exact h.symm

#print axioms ThreeColouring.sum_edge_counts

end Erdos556
