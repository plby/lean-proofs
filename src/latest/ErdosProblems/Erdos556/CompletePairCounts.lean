import ErdosProblems.Erdos556.MappedDensity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Counting all off-diagonal pairs in two finite sets. -/

namespace Erdos556

open SimpleGraph Finset

theorem card_le_degree_add_one_of_adj_ne {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) (u : V)
    (h : ∀ v ∈ B, u ≠ v → G.Adj u v) : B.card ≤ G.degree u + 1 := by
  have hsub : B.erase u ⊆ G.neighborFinset u := by
    intro v hv
    exact (G.mem_neighborFinset u v).mpr (h v (mem_of_mem_erase hv) (mem_erase.mp hv).1.symm)
  have hc := card_le_card hsub
  rw [card_neighborFinset_eq_degree] at hc
  by_cases hu : u ∈ B
  · rw [card_erase_of_mem hu] at hc
    omega
  · rw [erase_eq_of_notMem hu] at hc
    omega

theorem complete_pair_card_product_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (h : ∀ u ∈ A, ∀ v ∈ B, u ≠ v → G.Adj u v) :
    A.card * B.card ≤ 2 * Nat.card G.edgeSet + Fintype.card V := by
  calc
    A.card * B.card = ∑ _u ∈ A, B.card := by simp
    _ ≤ ∑ u ∈ A, (G.degree u + 1) :=
      sum_le_sum (fun u hu => card_le_degree_add_one_of_adj_ne G B u (h u hu))
    _ = (∑ u ∈ A, G.degree u) + A.card := by rw [sum_add_distrib]; simp
    _ ≤ (∑ u, G.degree u) + Fintype.card V :=
      Nat.add_le_add (sum_le_sum_of_subset (subset_univ _)) (card_le_univ A)
    _ = _ := by rw [G.sum_degrees_eq_twice_card_edges, edgeFinset_card_eq_natCard_edgeSet]

theorem natCard_edges_mono {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (h : G ≤ H) : Nat.card G.edgeSet ≤ Nat.card H.edgeSet := by
  classical
  have hc := card_le_card (edgeFinset_mono h)
  simpa only [edgeFinset_card_eq_natCard_edgeSet] using hc

theorem natCard_edges_induce_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Nat.card (G.induce (S : Set V)).edgeSet ≤ Nat.card G.edgeSet := by
  classical
  let f := (Embedding.induce (G := G) (S : Set V)).toCopy.mapEdgeSet
  have h := Fintype.card_le_of_injective f f.injective
  simpa only [← Nat.card_eq_fintype_card] using h

#print axioms complete_pair_card_product_bound

end Erdos556
