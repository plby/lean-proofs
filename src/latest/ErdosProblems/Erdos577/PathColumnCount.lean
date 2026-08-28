import ErdosProblems.Erdos577.PathRowCounts

/-! Count path contacts when only the first two rows can share a column. -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma FourPath.contacts_le_card_add_common (p : FourPath G) (s : Finset V)
    (h02 : ∀ u ∈ s, ¬(G.Adj (p.vertices 0) u ∧ G.Adj (p.vertices 2) u))
    (h03 : ∀ u ∈ s, ¬(G.Adj (p.vertices 0) u ∧ G.Adj (p.vertices 3) u))
    (h12 : ∀ u ∈ s, ¬(G.Adj (p.vertices 1) u ∧ G.Adj (p.vertices 2) u))
    (h13 : ∀ u ∈ s, ¬(G.Adj (p.vertices 1) u ∧ G.Adj (p.vertices 3) u))
    (h23 : ∀ u ∈ s, ¬(G.Adj (p.vertices 2) u ∧ G.Adj (p.vertices 3) u)) :
    contacts G p.support s ≤ s.card +
      (s.filter (fun u ↦ G.Adj (p.vertices 0) u ∧ G.Adj (p.vertices 1) u)).card := by
  have hcol (u : V) (hu : u ∈ s) : degreeIn G u p.support ≤
      1 + if G.Adj (p.vertices 0) u ∧ G.Adj (p.vertices 1) u then 1 else 0 := by
    have hc02 := h02 u hu
    have hc03 := h03 u hu
    have hc12 := h12 u hu
    have hc13 := h13 u hu
    have hc23 := h23 u hu
    rw [FourPath.support, degreeIn_image G u univ p.vertices p.vertices.injective]
    simp only [Fin.sum_univ_four]
    by_cases h0 : G.Adj (p.vertices 0) u <;>
      by_cases h1 : G.Adj (p.vertices 1) u <;>
      by_cases h2 : G.Adj (p.vertices 2) u <;>
      by_cases h3 : G.Adj (p.vertices 3) u <;>
      simp_all [SimpleGraph.adj_comm]
  calc
    contacts G p.support s = ∑ u ∈ s, degreeIn G u p.support := contacts_comm G _ _
    _ ≤ ∑ u ∈ s, (1 + if G.Adj (p.vertices 0) u ∧ G.Adj (p.vertices 1) u then 1 else 0) :=
      sum_le_sum hcol
    _ = s.card + (s.filter (fun u ↦ G.Adj (p.vertices 0) u ∧ G.Adj (p.vertices 1) u)).card := by
      simp only [sum_add_distrib, card_eq_sum_ones, sum_filter]

lemma common_intersection_three (s i m : Finset V) (hi : i ⊆ s) (hm : m ⊆ s)
    (hs : s.card = 4) (h : 7 ≤ i.card + m.card) : 3 ≤ (i ∩ m).card := by
  have hbound := card_le_card (union_subset hi hm)
  have he := card_union_add_card_inter i m
  omega

end Erdos577
