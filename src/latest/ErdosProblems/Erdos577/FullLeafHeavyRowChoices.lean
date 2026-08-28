import ErdosProblems.Erdos577.FullLeafHeavyCoreRoutes

/-! The finite row and common-neighbor choices used to normalize the opposite-pair case. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma three_row_without_low_pair (q : Quadrilateral G) (u : V)
    (hthree : degreeIn G u q.support = 3) (hlow : ¬(G.Adj u (q 1) ∧ G.Adj u (q 3))) :
    G.Adj u (q 0) ∧ G.Adj u (q 2) ∧
      ((G.Adj u (q 1) ∧ ¬G.Adj u (q 3)) ∨ (¬G.Adj u (q 1) ∧ G.Adj u (q 3))) := by
  rw [JointFinal.opposite_degree_split q u, JointFinal.degree_pair_eq u (q 0) (q 2)
    (q.injective.ne (by decide)), JointFinal.degree_pair_eq u (q 1) (q 3)
    (q.injective.ne (by decide))] at hthree
  by_cases h0 : G.Adj u (q 0) <;> by_cases h1 : G.Adj u (q 1) <;>
    by_cases h2 : G.Adj u (q 2) <;> by_cases h3 : G.Adj u (q 3) <;> simp_all

lemma high_contact_of_two (q : Quadrilateral G) (u : V)
    (htwo : degreeIn G u q.support = 2) (hlow : ¬(G.Adj u (q 1) ∧ G.Adj u (q 3))) :
    G.Adj u (q 0) ∨ G.Adj u (q 2) := by
  have hb := (JointFinal.degree_pair_le_one_iff (G := G) u (q 1) (q 3)
    (q.injective.ne (by decide))).mpr hlow
  rw [JointFinal.opposite_degree_split q u, JointFinal.degree_pair_eq u (q 0) (q 2)
    (q.injective.ne (by decide))] at htwo
  by_contra hh
  have h0 : ¬G.Adj u (q 0) := fun h0 ↦ hh (Or.inl h0)
  have h2 : ¬G.Adj u (q 2) := fun h2 ↦ hh (Or.inr h2)
  rw [if_neg h0, if_neg h2] at htwo
  omega

omit [DecidableEq V] in
lemma common_high_ne_of_nine (t : Finset V) (ht : t.card = 5) (v w u : V)
    (hnine : 9 ≤ degreeIn G v t + degreeIn G w t) :
    ∃ z ∈ t, z ≠ u ∧ G.Adj z v ∧ G.Adj z w := by
  classical
  have he := card_union_add_card_inter (t.filter (G.Adj v)) (t.filter (G.Adj w))
  have hb : ((t.filter (G.Adj v)) ∪ (t.filter (G.Adj w))).card ≤ 5 :=
    (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans_eq ht
  change _ + _ = degreeIn G v t + degreeIn G w t at he
  have hlarge : 1 < ((t.filter (G.Adj v)) ∩ (t.filter (G.Adj w))).card := by omega
  obtain ⟨z, hz, hzu⟩ := exists_mem_ne hlarge u
  obtain ⟨hzv, hzw⟩ := mem_inter.mp hz
  exact ⟨z, (mem_filter.mp hzv).1, hzu, (mem_filter.mp hzv).2.symm, (mem_filter.mp hzw).2.symm⟩

end Erdos577.FullLeafHeavy

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.first_avoids_two_lows (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (hhigh : 2 ≤ degreeIn G (q 0) (insert (p.vertices 3) a))
    {w : V} (hw : w ∈ insert p.leaf s) : ¬(G.Adj w (q 1) ∧ G.Adj w (q 3)) := by
  rintro ⟨hw1, hw3⟩
  have hout : w ∉ q.support := fun hh ↦ disjoint_left.mp (h.five_disjoint_block hj hjs) hw hh
  have hrep := JointFinal.low_pair_replace q w hout hw1 hw3 0 (Or.inl rfl)
  have hb := h.core_degree_of_first_replacement hcard hn hw hj hjs hja
    ((q.mem_support _).mpr ⟨0, rfl⟩) hrep
  have hmono := degreeIn_mono G (q 0) h.second_five_subset
  omega

end Erdos577.FullLeafCore
