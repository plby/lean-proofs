import ErdosProblems.Erdos577.FullLeafSparseTenExcluded

/-! Two shared second-side sparse attachments contradict the common-column or equality argument. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.type41_shared_row_false (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j l : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hl : l ∈ c.blocks) (hls : l ≠ s) (hla : l ≠ a) (hjl : j ≠ l)
    (hjheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (hlheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) l)
    (hjtype : FullLeafHeavy.Type41 G p a j) (hltype : FullLeafHeavy.Type41 G p a l)
    {v : V} (hv : v ∈ insert (p.vertices 3) a)
    (hvj : 0 < degreeIn G v j) (hvl : 0 < degreeIn G v l) : False := by
  by_cases htenJ : contacts G (s.erase y) j = 10
  · exact hm.type41_ten_contacts_false hcard hn hj hjs hja hl hls hla hjl
      hjheavy hlheavy hjtype hltype htenJ
  by_cases htenL : contacts G (s.erase y) l = 10
  · exact hm.type41_ten_contacts_false hcard hn hl hls hla hj hjs hja hjl.symm
      hlheavy hjheavy hltype hjtype htenL
  have hJ : 11 ≤ contacts G (s.erase y) j := by
    have hh := (hm.type41_refinement hcard hn hj hjs hja hjheavy hjtype).2.1
    omega
  have hL : 11 ≤ contacts G (s.erase y) l := by
    have hh := (hm.type41_refinement hcard hn hl hls hla hlheavy hltype).2.1
    omega
  obtain ⟨d, hd⟩ := card_pos.mp hvj
  obtain ⟨e, he⟩ := card_pos.mp hvl
  obtain ⟨hdj, hvd⟩ := mem_filter.mp hd
  obtain ⟨hel, hve⟩ := mem_filter.mp he
  have hdrow := FullLeafSparse.contacts_le_other_rows (G := G) (j := s.erase y) hdj
  have herow := FullLeafSparse.contacts_le_other_rows (G := G) (j := s.erase y) hel
  rw [(c.property.blocks_quad j hj).card, hm.1.first_triple_clique.card_eq,
    contacts_comm G j (s.erase y)] at hdrow
  rw [(c.property.blocks_quad l hl).card, hm.1.first_triple_clique.card_eq,
    contacts_comm G l (s.erase y)] at herow
  obtain ⟨x, hx, hxd, hxe⟩ := FullLeafSparse.common_neighbor_of_degree_sum
    (G := G) (s.erase y) d e (by rw [hm.1.first_triple_clique.card_eq]; omega)
  exact hm.type41_common_column_false hcard hn hj hjs hja hl hls hla hjl
    hjheavy hlheavy hjtype hltype hv hdj hel hvd hve hx hxd hxe

end Erdos577.FullLeafCore
