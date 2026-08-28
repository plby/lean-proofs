import ErdosProblems.Erdos577.FullLeafHeavyDiamondCounts

/-! Exact first-triple bounds and a common neighbor distinct from a prescribed row. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma triple_contacts_le_five (q : Quadrilateral G) (t : Finset V) (ht : t.card = 3)
    (hno : ∀ x ∈ t, ¬(G.Adj x (q 0) ∧ G.Adj x (q 2)))
    (h1 : degreeIn G (q 1) t ≤ 1) (h3 : degreeIn G (q 3) t ≤ 1) :
    contacts G t q.support ≤ 5 := by
  have h02 : q 0 ≠ q 2 := q.injective.ne (by decide)
  have hhigh : contacts G t {q 0, q 2} ≤ 3 := by
    calc
      contacts G t {q 0, q 2} ≤ ∑ _ ∈ t, (1 : ℕ) :=
        sum_le_sum fun x hx ↦ (JointFinal.degree_pair_le_one_iff x (q 0) (q 2) h02).mpr (hno x hx)
      _ = 3 := by simp only [sum_const, smul_eq_mul, mul_one, ht]
  rw [contacts_comm, contacts, sum_pair h02] at hhigh
  have hsum := columns_sum q t
  omega

lemma triple_contacts_le_four (q : Quadrilateral G) (t : Finset V) (ht : t.card = 3)
    (hrows : ∀ x ∈ t, degreeIn G x q.support ≤ 2)
    (htouch : ∀ x ∈ t, degreeIn G x q.support = 2 → G.Adj x (q 1))
    (h1 : degreeIn G (q 1) t ≤ 1) : contacts G t q.support ≤ 4 := by
  have hrow (x : V) (hx : x ∈ t) :
      degreeIn G x q.support ≤ 1 + (if G.Adj (q 1) x then 1 else 0) := by
    have hb := hrows x hx
    by_cases ha : G.Adj (q 1) x
    · rw [if_pos ha]
      omega
    · rw [if_neg ha]
      have hne : degreeIn G x q.support ≠ 2 := fun hh ↦ ha (htouch x hx hh).symm
      omega
  have hsum := sum_le_sum hrow
  have he : (∑ x ∈ t, if G.Adj (q 1) x then 1 else 0) = degreeIn G (q 1) t := by
    rw [degreeIn, card_eq_sum_ones, sum_filter]
  rw [sum_add_distrib, he, sum_const, smul_eq_mul, mul_one, ht] at hsum
  change contacts G t q.support ≤ 3 + degreeIn G (q 1) t at hsum
  omega

omit [DecidableEq V] in
lemma common_neighbor_ne_of_card_add_two (t : Finset V) (v w u : V)
    (hcontacts : t.card + 2 ≤ degreeIn G v t + degreeIn G w t) :
    ∃ z ∈ t, z ≠ u ∧ G.Adj z v ∧ G.Adj z w := by
  classical
  have he := card_union_add_card_inter (t.filter (G.Adj v)) (t.filter (G.Adj w))
  have hb : ((t.filter (G.Adj v)) ∪ (t.filter (G.Adj w))).card ≤ t.card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  change _ + _ = degreeIn G v t + degreeIn G w t at he
  have hlarge : 1 < ((t.filter (G.Adj v)) ∩ (t.filter (G.Adj w))).card := by omega
  obtain ⟨z, hz, hzu⟩ := exists_mem_ne hlarge u
  obtain ⟨hzv, hzw⟩ := mem_inter.mp hz
  exact ⟨z, (mem_filter.mp hzv).1, hzu, (mem_filter.mp hzv).2.symm, (mem_filter.mp hzw).2.symm⟩

end Erdos577.FullLeafHeavy
