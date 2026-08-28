import ErdosProblems.Erdos577.AlmostComplete

/-! Every four-set in a complete graph with at most one missing edge is a quadrilateral. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma four_distinct {a b c d : V} (h : ({a, b, c, d} : Finset V).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have ha : a ∉ ({b, c, d} : Finset V) := by
    intro ha
    rw [insert_eq_of_mem ha] at h
    have ht : ({b, c, d} : Finset V).card ≤ 3 := card_le_three
    omega
  have ht : ({b, c, d} : Finset V).card = 3 := by
    rw [card_insert_of_notMem ha] at h
    omega
  simp only [mem_insert, mem_singleton, not_or] at ha
  exact ⟨ha.1, ha.2.1, ha.2.2, (card_triple_eq_three_iff.mp ht)⟩

omit [DecidableRel G.Adj] in
lemma quad_of_near_clique {s : Finset V} {a b : V} (hs : s.card = 4)
    (hcl : (G ⊔ SimpleGraph.edge a b).IsClique s) : QuadOn G s := by
  classical
  apply QuadOn.of_degreeIn hs
  intro v hv
  let w := if v = a then b else a
  have hsize : 2 ≤ ((s.erase v).erase w).card := by
    have he : (s.erase v).card = 3 := by rw [card_erase_of_mem hv, hs]
    have hl := pred_card_le_card_erase (s := s.erase v) (a := w)
    omega
  have hsub : (s.erase v).erase w ⊆ s.filter (G.Adj v) := by
    intro z hz
    obtain ⟨hzw, hzv⟩ := mem_erase.mp hz
    obtain ⟨hzv, hzs⟩ := mem_erase.mp hzv
    refine mem_filter.mpr ⟨hzs, ?_⟩
    rcases (SimpleGraph.sup_adj _ _ _ _).mp (hcl hv hzs hzv.symm) with he | he
    · exact he
    · rcases ((SimpleGraph.edge_adj _ _ _ _).mp he).1 with ⟨hva, hzb⟩ | ⟨hvb, hza⟩
      · have hw : w = b := by simp [w, hva]
        exact False.elim (hzw (hzb.trans hw.symm))
      · by_cases hva : v = a
        · exact False.elim (hzv (hza.trans hva.symm))
        · have hw : w = a := by simp [w, hva]
          exact False.elim (hzw (hza.trans hw.symm))
  exact hsize.trans (card_le_card hsub)

lemma dense_four_subset {t a s : Finset V} (ht : G.IsNClique 3 t) (ha : G.IsNClique 4 a)
    (hd : Disjoint t a) (hc : 11 ≤ contacts G t a) (hsub : s ⊆ t ∪ a) (hs : s.card = 4) :
    QuadOn G s := by
  rcases dense_join_clique_or_cross_gap ht ha hd hc with hcl | ⟨x, _, y, _, _, _, hcl⟩
  · exact QuadOn.of_clique hs (hcl.subset (coe_subset.mpr hsub))
  · exact quad_of_near_clique hs (hcl.subset (coe_subset.mpr hsub))

lemma dense_complement_triple {t a : Finset V} (ht : G.IsNClique 3 t) (ha : G.IsNClique 4 a)
    (hd : Disjoint t a) (hc : 11 ≤ contacts G t a) (x y z : V)
    (hx : x ∈ t ∪ a) (hy : y ∈ t ∪ a) (hz : z ∈ t ∪ a)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    QuadOn G ((t ∪ a) \ {x, y, z}) := by
  have hsub : ({x, y, z} : Finset V) ⊆ t ∪ a :=
    insert_subset hx (insert_subset hy (singleton_subset_iff.mpr hz))
  apply dense_four_subset ht ha hd hc sdiff_subset
  rw [card_sdiff_of_subset hsub, card_union_of_disjoint hd, ht.card_eq, ha.card_eq,
    card_triple_eq_three_iff.mpr ⟨hxy, hxz, hyz⟩]

end Erdos577.JointCore
