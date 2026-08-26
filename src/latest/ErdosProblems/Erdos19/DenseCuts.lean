import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-! # Counting edges across cuts of a dense graph -/

namespace Erdos19

open Finset
open SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem between_degree_eq_card_filter (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) {v : V} (hv : v ∈ A) :
    (G.between (A : Set V) (B : Set V)).degree v = (B.filter (G.Adj v)).card := by
  classical
  have hvB : v ∉ B := fun hvB ↦ disjoint_left.mp hAB hv hvB
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp only [mem_neighborFinset, between_adj, mem_coe, mem_filter, hv, hvB,
    true_and, false_and, or_false, and_comm]

theorem cut_card_add_degree_deficit_ge (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (D : ℝ)
    (hD : ∀ v ∈ A, (Fintype.card V : ℝ) - G.degree v ≤ D) :
    (A.card : ℝ) * B.card ≤
      (G.between (A : Set V) (B : Set V)).edgeFinset.card + A.card * D := by
  classical
  let C := G.between (A : Set V) (B : Set V)
  have hper : ∀ v ∈ A, (B.card : ℝ) ≤ C.degree v + D := by
    intro v hv
    have hpart : (B.filter (G.Adj v)).card +
        (B.filter fun w ↦ ¬G.Adj v w).card = B.card := card_filter_add_card_filter_not _
    have hfull : G.degree v + (univ.filter fun w ↦ ¬G.Adj v w).card = Fintype.card V := by
      have h := @card_filter_add_card_filter_not V univ (G.Adj v) _ _
      simpa only [← G.neighborFinset_eq_filter, card_neighborFinset_eq_degree, card_univ] using h
    have hneg : (B.filter fun w ↦ ¬G.Adj v w).card ≤
        (univ.filter fun w ↦ ¬G.Adj v w).card :=
      card_le_card (filter_subset_filter _ (subset_univ B))
    have hpartR : ((B.filter (G.Adj v)).card : ℝ) +
        (B.filter fun w ↦ ¬G.Adj v w).card = B.card := by exact_mod_cast hpart
    have hfullR : (G.degree v : ℝ) +
        (univ.filter fun w ↦ ¬G.Adj v w).card = Fintype.card V := by exact_mod_cast hfull
    have hnegR : ((B.filter fun w ↦ ¬G.Adj v w).card : ℝ) ≤
        (univ.filter fun w ↦ ¬G.Adj v w).card := by exact_mod_cast hneg
    have hC : C.degree v = (B.filter (G.Adj v)).card :=
      between_degree_eq_card_filter G A B hAB hv
    rw [hC]
    linarith [hD v hv]
  have hsum := sum_le_sum hper
  have hcut : (∑ v ∈ A, C.degree v) = C.edgeFinset.card :=
    C.isBipartiteWith_sum_degrees_eq_card_edges
      (G.between_isBipartiteWith (Finset.disjoint_coe.mpr hAB))
  have hcutR : (∑ v ∈ A, (C.degree v : ℝ)) = C.edgeFinset.card := by exact_mod_cast hcut
  simpa only [sum_add_distrib, sum_const, nsmul_eq_mul, hcutR] using hsum

theorem cut_card_lower_of_min_degree (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (delta : ℝ)
    (hdegree : ∀ v, (1 - delta) * Fintype.card V ≤ (G.degree v : ℝ)) :
    (A.card : ℝ) * B.card ≤
      (G.between (A : Set V) (B : Set V)).edgeFinset.card +
        A.card * (delta * Fintype.card V) := by
  apply cut_card_add_degree_deficit_ge G A B hAB
  intro v _
  linarith [hdegree v]

#print axioms cut_card_lower_of_min_degree

end Erdos19
