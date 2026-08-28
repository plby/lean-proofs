import ErdosProblems.Erdos577.ClaimTwoSix
import ErdosProblems.Erdos577.AttachmentCount

/-! The exact weighted degree partition forcing Property A's nine-contact block. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Paw.noncentral_support_degrees (p : Paw G) (hn : ¬QuadOn G p.support) :
    degreeIn G (p.vertices 2) p.support = 2 ∧
      degreeIn G (p.vertices 3) p.support = 2 := by
  have hrow (i : Fin 4) (hi : i = 2 ∨ i = 3) :
      degreeIn G (p.vertices i) p.support = 2 := by
    have hm : p.vertices i ∈ p.triangle := by
      rcases hi with rfl | rfl <;> simp [Paw.triangle]
    have hnot : ¬G.Adj (p.vertices i) p.leaf := by
      intro he
      rcases hi with rfl | rfl
      · exact (p.nonadjacent_of_no_quad hn).1 he.symm
      · exact (p.nonadjacent_of_no_quad hn).2 he.symm
    rw [p.support_eq, degreeIn_insert G _ _ p.leaf_not_mem_triangle,
      if_neg hnot, zero_add, degreeIn_clique G p.triangle_clique.isClique hm,
      p.triangle_clique.card_eq]
  exact ⟨hrow 2 (Or.inl rfl), hrow 3 (Or.inr rfl)⟩

lemma Paw.doubled_leaf_inside (p : Paw G) (hn : ¬QuadOn G p.support) :
    2 * degreeIn G p.leaf p.support + degreeIn G (p.vertices 2) p.support +
      degreeIn G (p.vertices 3) p.support = 6 := by
  have hl : degreeIn G p.leaf p.support = 1 := by
    rw [p.support_eq, degreeIn_insert G _ _ p.leaf_not_mem_triangle,
      if_neg G.irrefl, zero_add, p.leaf_triangle_degree_eq_one hn]
  obtain ⟨h2, h3⟩ := p.noncentral_support_degrees hn
  rw [hl, h2, h3]

variable [Fintype V]

lemma TriangleChain.degree_partition (c : TriangleChain G) (v : V) :
    G.degree v = degreeIn G v c.remainder + ∑ s ∈ c.blocks, degreeIn G v s := by
  simpa only [contacts_singleton_left, degreeIn_univ] using c.contacts_partition {v}

theorem TriangleChain.exists_doubled_leaf_heavy (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder) :
    ∃ s ∈ c.blocks, 9 ≤ 2 * degreeIn G p.leaf s +
      degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s := by
  by_contra! hsmall
  have hsum : (∑ s ∈ c.blocks, (2 * degreeIn G p.leaf s +
      degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)) ≤ 8 * c.blocks.card := by
    calc
      _ ≤ ∑ _ ∈ c.blocks, (8 : ℕ) := sum_le_sum (fun s hs ↦ by have := hsmall s hs; omega)
      _ = _ := by simp [Nat.mul_comm]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at hsum
  have hinside := p.doubled_leaf_inside (by rw [hp]; exact c.no_quad_remainder hcard hn)
  rw [hp] at hinside
  have hX := c.degree_partition p.leaf
  have h2 := c.degree_partition (p.vertices 2)
  have h3 := c.degree_partition (p.vertices 3)
  have hXmin := hdeg p.leaf
  have h2min := hdeg (p.vertices 2)
  have h3min := hdeg (p.vertices 3)
  have hsize := c.card_vertices
  omega

end Erdos577
