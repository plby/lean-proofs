import ErdosProblems.Erdos577.TripleHighExcluded

/-! Low-contact counts and completeness when the original leaf is not full. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V}

theorem Configuration.heavy_low_counts (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hheavy : 11 ≤ contacts G (insert (q 3) p.support) a) :
    contacts G p.triangle a ≤ 4 ∧ 7 ≤ degreeIn G p.leaf a + degreeIn G (q 3) a ∧
      G.IsNClique 4 a := by
  have hlow := h.heavy_paw_contacts_le_eight hc hcard hdeg hn ha haq hheavy
  rw [h.five_contacts] at hheavy
  have hY : 3 ≤ degreeIn G (q 3) a := by omega
  have hT := h.exposed_triangle_contacts hc hcard hn ha haq hY
  have hF := p.contacts_support a
  have hsum : 7 ≤ degreeIn G p.leaf a + degreeIn G (q 3) a := by omega
  have hX4 := degreeIn_le_card G p.leaf a
  have hY4 := degreeIn_le_card G (q 3) a
  rw [(c.property.blocks_quad a ha).card] at hX4 hY4
  refine ⟨hT, hsum, ?_⟩
  by_cases hfull : degreeIn G p.leaf a = 4
  · exact (hc.presentPaw_feasible p h.paw).clique_of_terminal_degree_four ha hfull
  · obtain ⟨d, hd, ht, _, _, _, hblocks⟩ := h.exists_exposed_chain hc
    have ha' : a ∈ d.blocks := by
      rw [hblocks]
      exact mem_union_left _ (mem_erase.mpr ⟨haq, ha⟩)
    apply hd.clique_of_terminal_degree_four ha'
    rw [ht]
    omega

structure LowCore (c : TriangleChain G) (p : Paw G) (q : Quadrilateral G)
    (a : Finset V) : Prop extends Configuration c p q where
  core_block : a ∈ c.blocks
  core_ne : a ≠ q.support
  core_complete : G.IsNClique 4 a
  leaf_three : degreeIn G p.leaf a = 3
  exposed_four : degreeIn G (q 3) a = 4
  triangle_four : contacts G p.triangle a = 4

theorem Configuration.low_core_of_not_full (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hheavy : 11 ≤ contacts G (insert (q 3) p.support) a)
    (hnot : degreeIn G p.leaf a ≠ 4) : LowCore c p q a := by
  obtain ⟨hT, hsum, hcl⟩ := h.heavy_low_counts hc hcard hdeg hn ha haq hheavy
  have hX4 := degreeIn_le_card G p.leaf a
  have hY4 := degreeIn_le_card G (q 3) a
  rw [hcl.card_eq] at hX4 hY4
  rw [h.five_contacts, p.contacts_support] at hheavy
  exact ⟨h, ha, haq, hcl, by omega, by omega, by omega⟩

lemma LowCore.exposed_adj (h : LowCore c p q a) {u : V} (hu : u ∈ a) : G.Adj (q 3) u :=
  (degreeIn_eq_card_iff (q 3) a).mp (h.exposed_four.trans h.core_complete.card_eq.symm) u hu

end Erdos577.UniversalTriple
