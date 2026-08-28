import ErdosProblems.Erdos577.FullLeafSparseGeometry

/-! Complete second-sparse blocks and dense-core triangles through prescribed vertices. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.type41_preparation {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j) :
    G.IsNClique 4 j ∧ 17 ≤ contacts G (insert p.leaf s) j ∧ 9 ≤ contacts G (s.erase y) j := by
  have hj4 := (c.property.blocks_quad j hj).card
  have hsecond := htype.contacts_le_four hj4
  rw [h.combined_contacts] at hheavy
  have hfirst : 17 ≤ contacts G (insert p.leaf s) j := by omega
  have hfull : ∃ x ∈ insert p.leaf s, degreeIn G x j = 4 := by
    by_contra! hnone
    have hsum : contacts G (insert p.leaf s) j ≤ 15 := by
      calc
        contacts G (insert p.leaf s) j ≤ ∑ _ ∈ insert p.leaf s, (3 : ℕ) := by
          apply sum_le_sum
          intro x hx
          have hb := degreeIn_le_card G x j
          rw [hj4] at hb
          have hne := hnone x hx
          omega
        _ = 15 := by simp only [sum_const, smul_eq_mul, h.first_five_clique.card_eq]
    omega
  obtain ⟨x, hx, hrow⟩ := hfull
  have hcl := h.complete_of_first_full hx hj hjs hrow
  have hX := degreeIn_le_card G p.leaf j
  have hY := degreeIn_le_card G y j
  rw [hj4] at hX hY
  have hsplit := h.first_contacts j
  exact ⟨hcl, hfirst, by omega⟩

lemma Configuration.second_neighbor {u : V} (hu : u ∈ insert (p.vertices 3) a) :
    ∃ v ∈ insert (p.vertices 3) a, G.Adj u v := by
  rcases mem_insert.mp hu with rfl | hua
  · have hthree := every_row_high_of_eleven p.triangle_clique.card_eq h.core_clique.card_eq
      h.dense (show p.vertices 3 ∈ p.triangle by simp [Paw.triangle])
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (a.filter (G.Adj (p.vertices 3))).card by
      change 0 < degreeIn G (p.vertices 3) a
      omega)
    exact ⟨v, mem_insert_of_mem (mem_filter.mp hv).1, (mem_filter.mp hv).2⟩
  · obtain ⟨v, hv, hvu⟩ := exists_mem_ne (show 1 < a.card by rw [h.core_clique.card_eq]; decide) u
    exact ⟨v, mem_insert_of_mem hv, h.core_clique.isClique hua hv hvu.symm⟩

theorem Configuration.second_triangle_through {u : V} (hu : u ∈ insert (p.vertices 3) a) :
    ∃ t ⊆ insert (p.vertices 3) a, G.IsNClique 3 t ∧ u ∈ t ∧
      G.IsNClique 4 ((p.triangle ∪ a) \ t) := by
  obtain ⟨v, hv, huv⟩ := h.second_neighbor hu
  obtain ⟨t, ht, hcl, hut, _, hrem⟩ := h.second_triangle_extension hu hv huv
  exact ⟨t, ht, hcl, hut, hrem⟩

end Erdos577.FullLeafCore
