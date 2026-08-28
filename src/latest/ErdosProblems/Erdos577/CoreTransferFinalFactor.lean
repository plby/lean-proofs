import ErdosProblems.Erdos577.CoreTransferMissingContact
import ErdosProblems.Erdos577.TriangleContactBounds
import ErdosProblems.Erdos577.PathMiddleReplacements

/-! Two dense outside blocks meeting the same low give a forbidden three-cycle factor. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Route.no_two_dense_low_blocks {c : TriangleChain G} {q : Quadrilateral G}
    {bs : Finset (Finset V)} (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (i : Fin 4) (hi : i = 1 ∨ i = 3)
    {a b : Finset V} (ha : a ∈ c.blocks) (hb : b ∈ c.blocks)
    (hna : a ∉ bs) (hnb : b ∉ bs) (hab : a ≠ b)
    (hda : 11 ≤ contacts G c.triangle a) (hdb : 11 ≤ contacts G c.triangle b)
    (hla : 0 < degreeIn G (q i) a) (hlb : 0 < degreeIn G (q i) b)
    (hra : ∀ x ∈ c.triangle, ∀ u ∈ a, QuadOn G (insert x (a.erase u)))
    (hrb : ∀ x ∈ c.triangle, ∀ u ∈ b, QuadOn G (insert x (b.erase u))) : False := by
  obtain ⟨w, hw⟩ := card_pos.mp hla
  obtain ⟨v, hv⟩ := card_pos.mp hlb
  obtain ⟨hwa, hlw⟩ := mem_filter.mp hw
  obtain ⟨hvb, hlv⟩ := mem_filter.mp hv
  have htcard : c.triangle.card = 3 := c.property.triangle_clique.card_eq
  have hw2 := triangle_column_ge_two_of_eleven htcard (c.property.blocks_quad a ha).card hda hwa
  have hv2 := triangle_column_ge_two_of_eleven htcard (c.property.blocks_quad b hb).card hdb hvb
  have hbound : ((c.triangle.filter (G.Adj w)) ∪ (c.triangle.filter (G.Adj v))).card ≤ 3 := by
    rw [← htcard]
    exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  obtain ⟨u, hu, hwu, hvu⟩ := common_neighbor_of_union_bound w v c.triangle 3 hbound (by omega)
  obtain ⟨x, z, hxz, hux, huz, ht⟩ :=
    exists_pair_in_three_set (t := c.triangle) htcard u hu
  have hx : x ∈ c.triangle := by rw [ht]; simp only [mem_insert, mem_singleton]; tauto
  have hz : z ∈ c.triangle := by rw [ht]; simp only [mem_insert, mem_singleton]; tauto
  have hlo : q i ∉ ({u, x, z} : Finset V) ∪ (a ∪ b) := by
    rw [← ht]
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact r.cycle_not_mem_triangle i hh
    · exact (mem_union.mp hh).elim (r.cycle_not_mem_block ha hna i)
        (r.cycle_not_mem_block hb hnb i)
  have hf := triangle_two_block_factor u x z (q i) w v hux huz hxz
    (ht ▸ c.triangle_disjoint_block ha) (ht ▸ c.triangle_disjoint_block hb)
    (c.property.blocks_disjoint ha hb hab) hlo hwa hvb hwu.symm hlw.symm hlv hvu
    (hra x hx w hwa) (hrb z hz v hvb)
  have hsel : ({a, b} : Finset (Finset V)) ⊆ c.blocks := by
    intro d hd
    rcases mem_insert.mp hd with hd | hd
    · exact hd ▸ ha
    · exact (mem_singleton.mp hd) ▸ hb
  have hdis : Disjoint ({a, b} : Finset (Finset V)) bs := by
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨hna, hnb⟩
  apply r.no_selected_factor hcard hn i hi {a, b} hsel hdis
  simpa only [ht, biUnion_insert, singleton_biUnion, id_eq] using hf

end Erdos577.CoreTransfer
