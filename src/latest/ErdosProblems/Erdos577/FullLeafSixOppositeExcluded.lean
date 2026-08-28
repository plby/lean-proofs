import ErdosProblems.Erdos577.FullLeafSixOppositeFactor

/-! The eight-plus-four case has no second-side opposite pair in any cycle labeling. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.six_opposite_false (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (ht : G.IsNClique 3 (FullLeafEquality.matchedSecond p s a y))
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (height : contacts G (s.erase y) q.support = 8)
    (hfour : contacts G (FullLeafEquality.matchedSecond p s a y) q.support = 4)
    {u : V} (hu : u ∈ s.erase y) (hrow : 3 ≤ degreeIn G u q.support)
    {v : V} (hv : v ∈ FullLeafEquality.matchedSecond p s a y)
    (hv0 : G.Adj v (q 0)) (hv2 : G.Adj v (q 2)) : False := by
  have huFirst : u ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hu).2
  have hm (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hcol := FullLeafSix.columns_one q.card_support hfour
    (h.high_first_matched_columns hcard hn hj hjs hja huFirst hrow)
  obtain ⟨hc0, _, hc2, _, hd13⟩ :=
    h.six_opposite_columns hcard hn q hj hjs hja height hv hv0 hv2
  obtain ⟨hvn1, hvn3⟩ := h.six_opposite_no_lows hcard hn q hj hjs hja height hv hv0 hv2
  obtain ⟨w, hw⟩ := card_pos.mp (show
      0 < degreeIn G (q 1) (FullLeafEquality.matchedSecond p s a y) by rw [hcol _ (hm 1)]; decide)
  obtain ⟨hw, h1w⟩ := mem_filter.mp hw
  obtain ⟨z, hz⟩ := card_pos.mp (show
      0 < degreeIn G (q 3) (FullLeafEquality.matchedSecond p s a y) by rw [hcol _ (hm 3)]; decide)
  obtain ⟨hz, h3z⟩ := mem_filter.mp hz
  have hvw : v ≠ w := fun he ↦ hvn1 (he.symm ▸ h1w.symm)
  have hvz : v ≠ z := fun he ↦ hvn3 (he.symm ▸ h3z.symm)
  have hwout : w ∉ q.support := fun hh ↦
    disjoint_left.mp (h.matched_second_disjoint_block hj hja) hw hh
  have hwz : w ≠ z := by
    intro he
    have hrep := JointFinal.low_pair_replace q w hwout h1w.symm
      (he.symm ▸ h3z.symm) 0 (Or.inl rfl)
    have hb := h.triple_degree_of_second_replacement hcard hn (mem_filter.mp hw).1
      hj hjs hja (hm 0) hrep
    omega
  have htriple : ({v, w, z} : Finset V) = FullLeafEquality.matchedSecond p s a y := by
    apply eq_of_subset_of_card_le
      (insert_subset hv (insert_subset hw (singleton_subset_iff.mpr hz)))
    rw [ht.card_eq, card_triple_eq_three_iff.mpr ⟨hvw, hvz, hwz⟩]
  have hfull0 := (degreeIn_eq_card_iff (q 0) (s.erase y)).mp
    (hc0.trans h.first_triple_clique.card_eq.symm)
  have hfull2 := (degreeIn_eq_card_iff (q 2) (s.erase y)).mp
    (hc2.trans h.first_triple_clique.card_eq.symm)
  have hdis : Disjoint ({v, w, z} : Finset V) q.support := by
    rw [htriple]
    exact h.matched_second_disjoint_block hj hja
  have huout : u ∉ ({v, w, z} : Finset V) ∪ q.support := by
    rw [htriple]
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp h.matched_triples_disjoint hu hh
    · exact disjoint_left.mp (h.five_disjoint_block hj hjs) huFirst hh
  have hf := FullLeafSix.opposite_two_factor q hdis huout hvw hvz
    (ht.isClique hw hz hwz) hd13 (hfull0 u hu).symm (hfull2 u hu).symm
    hv0 hv2 h1w.symm h3z.symm
  rw [htriple] at hf
  exact h.first_no_factor hcard hn huFirst hj hjs hja h.matched_second_subset ht.card_eq hf

end Erdos577.FullLeafCore
