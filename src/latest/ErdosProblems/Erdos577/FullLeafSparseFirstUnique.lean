import ErdosProblems.Erdos577.FullLeafSparseUniqueCounts

/-! A first-side vertex cannot meet two distinct heavy blocks of the first sparse type. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.type40_shared_row_false (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j l : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hl : l ∈ c.blocks) (hls : l ≠ s) (hla : l ≠ a) (hjl : j ≠ l)
    (hjheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (hlheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) l)
    (hjtype : FullLeafHeavy.Type40 G p s y j) (hltype : FullLeafHeavy.Type40 G p s y l)
    {v : V} (hv : v ∈ s.erase y) (hvj : 0 < degreeIn G v j) (hvl : 0 < degreeIn G v l) :
    False := by
  obtain ⟨d, hd⟩ := card_pos.mp hvj
  obtain ⟨e, he⟩ := card_pos.mp hvl
  obtain ⟨hdj, hvd⟩ := mem_filter.mp hd
  obtain ⟨hel, hve⟩ := mem_filter.mp he
  have hJ := h.type40_second_contacts hjheavy hjtype
  have hL := h.type40_second_contacts hlheavy hltype
  have hdrow := FullLeafSparse.contacts_le_other_rows (G := G)
    (j := insert (p.vertices 3) a) hdj
  have herow := FullLeafSparse.contacts_le_other_rows (G := G)
    (j := insert (p.vertices 3) a) hel
  rw [(c.property.blocks_quad j hj).card, h.second_five_card,
    contacts_comm G j (insert (p.vertices 3) a)] at hdrow
  rw [(c.property.blocks_quad l hl).card, h.second_five_card,
    contacts_comm G l (insert (p.vertices 3) a)] at herow
  obtain ⟨x, hx, hxd, hxe⟩ := FullLeafSparse.common_neighbor_of_degree_sum
    (G := G) (insert (p.vertices 3) a) d e (by rw [h.second_five_card]; omega)
  obtain ⟨u, hu, hux, _, huFull⟩ := FullLeafSparse.full_row_outside_pair_of_eighteen
    h.second_five_card (c.property.blocks_quad j hj).card hJ x x
  obtain ⟨w, hw, hwx, hwu, hwFull⟩ := FullLeafSparse.full_row_outside_pair_of_eighteen
    h.second_five_card (c.property.blocks_quad l hl).card hL x u
  have ht : ({x, u, w} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset (h.second_five_subset hx) (insert_subset (h.second_five_subset hu)
      (singleton_subset_iff.mpr (h.second_five_subset hw)))
  have ht3 : ({x, u, w} : Finset V).card = 3 :=
    card_triple_eq_three_iff.mpr ⟨hux.symm, hwx.symm, hwu.symm⟩
  have hKJ := h.core_disjoint_block hj hja
  have hKL := h.core_disjoint_block hl hla
  have hvFirst : v ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hv).2
  have hvout : v ∉ ({x, u, w} : Finset V) ∪ (j ∪ l) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp h.five_disjoint_core hvFirst (ht hh)
    · rcases mem_union.mp hh with hh | hh
      · exact disjoint_left.mp (h.five_disjoint_block hj hjs) hvFirst hh
      · exact disjoint_left.mp (h.five_disjoint_block hl hls) hvFirst hh
  have hrepJ := (c.property.blocks_quad j hj).replace_of_degree_four
    (fun hh ↦ disjoint_left.mp hKJ (h.second_five_subset hu) hh) huFull hdj
  have hrepL := (c.property.blocks_quad l hl).replace_of_degree_four
    (fun hh ↦ disjoint_left.mp hKL (h.second_five_subset hw) hh) hwFull hel
  have hf := FullLeafSparse.common_column_partition
    ((disjoint_union_right.mpr ⟨hKJ, hKL⟩).mono_left ht)
    (c.property.blocks_disjoint hj hl hjl) hvout hux.symm hwx.symm hwu.symm
    hdj hel hvd hxd hxe hve hrepJ hrepL
  exact h.first_no_double_partition hcard hn hvFirst hj hjs hja hl hls hla ht ht3 hf

end Erdos577.FullLeafCore
