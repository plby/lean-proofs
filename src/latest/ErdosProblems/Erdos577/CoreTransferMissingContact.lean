import ErdosProblems.Erdos577.CoreTransferConsequences
import ErdosProblems.Erdos577.DenseTriangle
import ErdosProblems.Erdos577.ThreeSetChoice
import ErdosProblems.Erdos577.TriangleOneBlockFactor
import ErdosProblems.Erdos577.TriangleTwoBlockFactor

/-! The distinguished core vertex forces a missing triangle contact at each low neighbor. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {q : Quadrilateral G} {bs : Finset (Finset V)}

lemma Route.cycle_not_mem_triangle (r : Route c q bs) (i : Fin 4) : q i ∉ c.triangle := by
  intro hi
  exact disjoint_left.mp (c.triangle_disjoint_block (r.blocks_subset r.contains_cycle))
    hi ((q.mem_support _).mpr ⟨i, rfl⟩)

lemma Route.cycle_not_mem_block (r : Route c q bs) {a : Finset V}
    (ha : a ∈ c.blocks) (hna : a ∉ bs) (i : Fin 4) : q i ∉ a := by
  have hqa : q.support ≠ a := fun he ↦ hna (he ▸ r.contains_cycle)
  exact fun hi ↦ disjoint_left.mp
    (c.property.blocks_disjoint (r.blocks_subset r.contains_cycle) ha hqa)
    ((q.mem_support _).mpr ⟨i, rfl⟩) hi

theorem Route.missing_triangle_contact (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hnb : b ∉ bs)
    {z : V} (hz : z ∈ c.triangle ∪ b) (hzl : G.Adj z (q 1))
    (hzrep : z ∈ b → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z x ∧ QuadOn G (insert y (b.erase z)))
    {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs) (hab : a ≠ b)
    (hreplace : ∀ x ∈ c.triangle, ∀ u ∈ a, QuadOn G (insert x (a.erase u)))
    {w : V} (hw : w ∈ a) (hlw : G.Adj (q 1) w) :
    ∃ x ∈ c.triangle, ¬G.Adj x w := by
  by_contra! hall
  have hlowt := r.cycle_not_mem_triangle 1
  have hlowa := r.cycle_not_mem_block ha hna 1
  rcases mem_union.mp hz with hzt | hzb
  · obtain ⟨x, y, hxy, hzx, hzy, ht⟩ :=
      exists_pair_in_three_set (t := c.triangle) c.property.triangle_clique.card_eq z hzt
    have hxt : x ∈ c.triangle := by rw [ht]; simp only [mem_insert, mem_singleton]; tauto
    have hyt : y ∈ c.triangle := by rw [ht]; simp only [mem_insert, mem_singleton]; tauto
    have he : ({x, y, z} : Finset V) = c.triangle := by
      rw [ht, insert_comm z x, pair_comm z y]
    have hd : Disjoint {x, y, z} a := he.symm ▸ c.triangle_disjoint_block ha
    have hlo : q 1 ∉ ({x, y, z} : Finset V) ∪ a := by
      rw [he]
      exact fun hh ↦ (mem_union.mp hh).elim hlowt hlowa
    have hf := triangle_one_block_factor x y z (q 1) w hxy hzy.symm hd hlo hw
      (c.property.triangle_clique.isClique hxt hzt hzx.symm) hzl hlw (hall x hxt).symm
      (hreplace y hyt w hw)
    rw [he] at hf
    exact r.no_local_factor hcard hn 1 (Or.inl rfl) ha hna hf
  · obtain ⟨x, hx, y, hy, hxy, hzx, hyrep⟩ := hzrep hzb
    obtain ⟨v, hvx, hvy, ht⟩ :=
      exists_third_in_three_set (t := c.triangle) c.property.triangle_clique.card_eq x y hx hy hxy
    have hv : v ∈ c.triangle := by rw [ht]; simp only [mem_insert, mem_singleton]; tauto
    have hlowb := r.cycle_not_mem_block hb hnb 1
    have hlo : q 1 ∉ ({x, y, v} : Finset V) ∪ (b ∪ a) := by
      rw [← ht]
      intro hh
      rcases mem_union.mp hh with hh | hh
      · exact hlowt hh
      · exact (mem_union.mp hh).elim hlowb hlowa
    have hf := triangle_two_block_factor x y v (q 1) z w hxy hvx.symm hvy.symm
      (ht ▸ c.triangle_disjoint_block hb) (ht ▸ c.triangle_disjoint_block ha)
      (c.property.blocks_disjoint hb ha hab.symm) hlo hzb hw hzx.symm hzl hlw
      (hall x hx).symm hyrep (hreplace v hv w hw)
    have hsel : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
      intro d hd
      rcases mem_insert.mp hd with hd | hd
      · exact hd ▸ hb
      · exact (mem_singleton.mp hd) ▸ ha
    have hdis : Disjoint ({b, a} : Finset (Finset V)) bs := by
      simp only [disjoint_insert_left, disjoint_singleton_left]
      exact ⟨hnb, hna⟩
    apply r.no_selected_factor hcard hn 1 (Or.inl rfl) {b, a} hsel hdis
    simpa only [ht, biUnion_insert, singleton_biUnion, id_eq] using hf

end Erdos577.CoreTransfer
