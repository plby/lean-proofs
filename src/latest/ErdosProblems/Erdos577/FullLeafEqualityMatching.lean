import ErdosProblems.Erdos577.FullLeafEqualityExchange

/-! An unmatched first vertex gives an actual exchange increasing the additional maximum. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.matching_contacts_three (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    contacts G (s.erase y) (insert (p.vertices 3) a) = 3 := by
  let h := hm.1
  have hupper := h.matching_contacts_le_three hcard hn
  by_contra hne
  have hsmall : contacts G (s.erase y) (insert (p.vertices 3) a) < 3 := by omega
  obtain ⟨u, hu, huUnmatched⟩ := exists_mem_notMem_of_card_lt_card
    (show (FullLeafEquality.matchedFirst p s a y).card < (s.erase y).card by
      rw [h.matched_first_card hcard hn, h.first_triple_clique.card_eq]
      exact hsmall)
  obtain ⟨v, hv, hvUnmatched⟩ := exists_mem_notMem_of_card_lt_card
    (show (FullLeafEquality.matchedSecond p s a y).card < (insert (p.vertices 3) a).card by
      rw [h.matched_second_card hcard hn, h.second_five_card]
      omega)
  have hvFirst : v ∉ FullLeafEquality.matchedFirst p s a y := fun hh ↦
    disjoint_left.mp h.triple_second_disjoint (mem_filter.mp hh).1 hv
  have hvCovered : v ∈ FullLeafEquality.covered c p s a y := by
    rw [hm.equality_sparse_cover hcard hdeg hn]
    exact mem_sdiff.mpr ⟨mem_union_right _ hv, fun hh ↦
      (mem_union.mp hh).elim hvFirst hvUnmatched⟩
  obtain ⟨j, hjHeavy, hvj⟩ := FullLeafEquality.mem_covered.mp hvCovered
  obtain ⟨⟨hj, hjs, hja⟩, _⟩ := FullLeafEquality.mem_heavy.mp hjHeavy
  have htype : FullLeafHeavy.Type41 G p a j := by
    rcases hvj.1 with ⟨hvT, _⟩ | ⟨_, htype⟩
    · exact False.elim (disjoint_left.mp h.triple_second_disjoint hvT hv)
    · exact htype
  obtain ⟨d, hd⟩ := card_pos.mp (show 0 < degreeIn G v j by rw [hvj.2]; decide)
  obtain ⟨hdj, hvd⟩ := mem_filter.mp hd
  have hdOne : degreeIn G d (insert (p.vertices 3) a) = 1 := by
    have hb := htype.2 d hdj
    have hp : 0 < degreeIn G d (insert (p.vertices 3) a) :=
      card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, hvd.symm⟩⟩
    omega
  have huZero : degreeIn G u (insert (p.vertices 3) a) = 0 := by
    by_contra hh
    exact huUnmatched (mem_filter.mpr ⟨hu, by omega⟩)
  obtain ⟨e, he, _, _⟩ := h.unmarked_block_exchange hj hjs hja
    (hm.type41_full_first_matrix hcard hdeg hn hjHeavy htype) hu hdj
  have hmax := hm.2 e p (insert d (s.erase u)) a y he
  have hdOut : d ∉ s.erase u := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint hj h.first hjs) hdj (mem_erase.mp hh).2
  have herase := sum_erase_add (s := s) (fun w ↦ degreeIn G w (insert (p.vertices 3) a))
    (mem_erase.mp hu).2
  rw [huZero, add_zero] at herase
  have hscore : contacts G (insert (p.vertices 3) a) (insert d (s.erase u)) =
      contacts G (insert (p.vertices 3) a) s + 1 := by
    rw [contacts_comm G (insert (p.vertices 3) a) (insert d (s.erase u)), contacts,
      sum_insert hdOut, hdOne, herase, contacts_comm G (insert (p.vertices 3) a) s]
    change 1 + contacts G s (insert (p.vertices 3) a) =
      contacts G s (insert (p.vertices 3) a) + 1
    omega
  rw [hscore] at hmax
  omega

theorem Maximal.matched_first_eq (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    FullLeafEquality.matchedFirst p s a y = s.erase y := by
  apply eq_of_subset_of_card_le (filter_subset _ _)
  change (s.erase y).card ≤ (FullLeafEquality.matchedFirst p s a y).card
  rw [hm.1.matched_first_card hcard hn, hm.matching_contacts_three hcard hdeg hn,
    hm.1.first_triple_clique.card_eq]

theorem Maximal.matched_second_triangle (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    G.IsNClique 3 (FullLeafEquality.matchedSecond p s a y) := by
  refine ⟨(hm.equality_core_complete hcard hdeg hn).isClique.subset
    (coe_subset.mpr ((filter_subset _ _).trans hm.1.second_five_subset)), ?_⟩
  rw [hm.1.matched_second_card hcard hn, hm.matching_contacts_three hcard hdeg hn]

theorem Maximal.first_matching_degree (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {u : V} (hu : u ∈ s.erase y) : degreeIn G u (insert (p.vertices 3) a) = 1 := by
  have hmemb : u ∈ FullLeafEquality.matchedFirst p s a y :=
    (hm.matched_first_eq hcard hdeg hn).symm ▸ hu
  have hpos := (mem_filter.mp hmemb).2
  have hbound := (hm.1.matching_degrees hcard hn).1 u hu
  omega

end Erdos577.FullLeafCore
