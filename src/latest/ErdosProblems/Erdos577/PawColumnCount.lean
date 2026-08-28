import ErdosProblems.Erdos577.CommonReplacementAlternatives
import ErdosProblems.Erdos577.Paws

/-! A three-candidate clique replacement and a column count for the triangle beside a leaf. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma clique_replace_in_three_candidates {a : Finset V} (hcl : G.IsNClique 4 a)
    (z : V) (hz : z ∉ a) (hrow : 2 ≤ degreeIn G z a)
    (s : Finset V) (hs : s ⊆ a) (h3 : 3 ≤ s.card) :
    ∃ u ∈ s, QuadOn G (insert z (a.erase u)) := by
  by_cases hd3 : 3 ≤ degreeIn G z a
  · obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < s.card)
    exact ⟨u, hu, clique_replace_of_degree_three hcl hz hd3 (hs hu)⟩
  · have hn : ∃ u ∈ s, ¬G.Adj z u := by
      by_contra! hn
      have hsub : s ⊆ a.filter (G.Adj z) := fun u hu ↦ mem_filter.mpr ⟨hs hu, hn u hu⟩
      have hcard := card_le_card hsub
      change s.card ≤ degreeIn G z a at hcard
      omega
    obtain ⟨u, hu, hnu⟩ := hn
    have he := degreeIn_erase_add G z u (hs hu)
    rw [if_neg hnu] at he
    exact ⟨u, hu, (clique_replace_iff_two_contacts hcl hz (hs hu)).mpr (by omega)⟩

lemma Paw.leaf_triangle_count_bound (p : Paw G) (a : Finset V)
    (hcol : ∀ u ∈ a, degreeIn G u p.triangle ≤ 1)
    (hb : ∀ u ∈ a, G.Adj p.leaf u → ¬G.Adj (p.vertices 2) u)
    (hc : ∀ u ∈ a, G.Adj p.leaf u → ¬G.Adj (p.vertices 3) u) :
    contacts G p.triangle a + degreeIn G p.leaf a ≤ a.card + degreeIn G p.center a := by
  have hbound (u : V) (hu : u ∈ a) : degreeIn G u p.triangle +
      (if G.Adj p.leaf u then 1 else 0) ≤ 1 + (if G.Adj p.center u then 1 else 0) := by
    by_cases hxu : G.Adj p.leaf u
    · have hbu := hb u hu hxu
      have hcu := hc u hu hxu
      have he : degreeIn G u p.triangle = if G.Adj p.center u then 1 else 0 := by
        have hbu' : ¬G.Adj u (p.vertices 2) := fun hh ↦ hbu hh.symm
        have hcu' : ¬G.Adj u (p.vertices 3) := fun hh ↦ hcu hh.symm
        change degreeIn G u p.triangle = if G.Adj (p.vertices 1) u then 1 else 0
        by_cases hru : G.Adj (p.vertices 1) u
        · have hru' := hru.symm
          simp [degreeIn, Paw.triangle, filter_insert, filter_singleton, hru, hru', hbu', hcu']
        · have hru' : ¬G.Adj u (p.vertices 1) := fun hh ↦ hru hh.symm
          simp [degreeIn, Paw.triangle, filter_insert, filter_singleton, hru, hru', hbu', hcu']
      rw [he, if_pos hxu]
      omega
    · rw [if_neg hxu]
      have hl := hcol u hu
      omega
  have hsum := sum_le_sum hbound
  have hdeg (z : V) : (∑ u ∈ a, if G.Adj z u then 1 else 0) = degreeIn G z a := by
    simp only [degreeIn, card_eq_sum_ones, sum_filter]
  rw [sum_add_distrib, sum_add_distrib, hdeg p.leaf, hdeg p.center] at hsum
  have ht : (∑ u ∈ a, degreeIn G u p.triangle) = contacts G p.triangle a :=
    contacts_comm G a p.triangle
  simpa only [ht, sum_const, smul_eq_mul, Nat.mul_one] using hsum

end Erdos577
