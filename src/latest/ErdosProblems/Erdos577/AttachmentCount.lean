import ErdosProblems.Erdos577.Refinement

/-! The exact global degree contradiction for an unattached refined chain. -/

namespace Erdos577.TriangleChain

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma contacts_partition (c : TriangleChain G) (s : Finset V) :
    contacts G s univ = contacts G s c.remainder + ∑ b ∈ c.blocks, contacts G s b := by
  rw [← c.property.cover, contacts_union_right G s c.property.remainder_disjoint,
    contacts_biUnion_right G _ _ _ c.property.blocks_disjoint]
  rfl

lemma triangle_internal_contacts (c : TriangleChain G) : contacts G c.triangle c.triangle = 6 := by
  calc
    contacts G c.triangle c.triangle = ∑ _ ∈ c.triangle, (2 : ℕ) := by
      apply sum_congr rfl
      intro v hv
      rw [degreeIn_clique G c.property.triangle_clique.isClique hv,
        c.property.triangle_clique.card_eq]
    _ = 6 := by simp [c.property.triangle_clique.card_eq]

lemma terminal_remainder_degree (c : TriangleChain G) :
    degreeIn G c.terminal c.remainder = c.attachmentScore := by
  change degreeIn G c.terminal (insert c.terminal c.triangle) = _
  rw [degreeIn_insert G c.terminal c.terminal c.property.terminal_not_mem]
  simp only [SimpleGraph.irrefl, if_false, Nat.zero_add, attachmentScore]

lemma triangle_remainder_contacts (c : TriangleChain G) :
    contacts G c.triangle c.remainder = c.attachmentScore + 6 := by
  change contacts G c.triangle (insert c.terminal c.triangle) = _
  rw [← singleton_union, contacts_union_right G _
    (disjoint_singleton_left.mpr c.property.terminal_not_mem),
    contacts_singleton_right, c.triangle_internal_contacts]
  rfl

/-- A weighted local bound of twelve is incompatible with an unattached
terminal and the target's exact degree threshold. -/
lemma unattached_degree_contradiction (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hzero : c.attachmentScore = 0)
    (hweight : ∀ b ∈ c.blocks, 3 * degreeIn G c.terminal b + contacts G c.triangle b ≤ 12) :
    False := by
  have ht := minimum_degree_sum G c.triangle (2 * k) (fun v _ ↦ hdeg v)
  rw [c.property.triangle_clique.card_eq] at ht
  have hx := hdeg c.terminal
  have hdx := c.contacts_partition {c.terminal}
  simp only [contacts_singleton_left, degreeIn_univ, c.terminal_remainder_degree] at hdx
  have hdt := c.contacts_partition c.triangle
  rw [c.triangle_remainder_contacts] at hdt
  have hsum : (∑ b ∈ c.blocks, (3 * degreeIn G c.terminal b + contacts G c.triangle b)) ≤
      12 * c.blocks.card := by
    calc
      _ ≤ ∑ _ ∈ c.blocks, (12 : ℕ) := sum_le_sum hweight
      _ = _ := by simp [Nat.mul_comm]
  rw [sum_add_distrib, ← mul_sum] at hsum
  have hc := c.card_vertices
  omega

end Erdos577.TriangleChain
