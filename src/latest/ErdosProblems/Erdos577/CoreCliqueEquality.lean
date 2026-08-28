import ErdosProblems.Erdos577.CoreBridgeBounds

/-! Twelve paw contacts force a complete seven-vertex core in a strong chain. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Strong.complete_core_of_twelve {c : TriangleChain G} (hc : c.Strong) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (htwelve : contacts G c.remainder b = 12) :
    G.IsNClique 7 (c.triangle ∪ b) := by
  have hzero : degreeIn G c.terminal b = 0 := by
    by_contra hz
    obtain ⟨p, hx, _, hp⟩ := hc.exists_paw
    obtain ⟨q, hq⟩ := c.property.blocks_quad b hb
    have hh := hc.toFeasible.positive_leaf_contacts_le_nine hcard hdeg hn p hp hb q hq
      (by rw [hx, hq]; omega)
    rw [hp, hq, htwelve] at hh
    omega
  have hid := CoreTransfer.remainder_contacts c b
  have htri : contacts G c.triangle b = 12 := by omega
  obtain ⟨hbc, _⟩ := hc.toFeasible.all_triangle_universal_replacements hb (by omega)
  have htcard : c.triangle.card = 3 := c.property.triangle_clique.card_eq
  have hsize : (c.triangle ∪ b).card = 7 := by
    rw [card_union_of_disjoint (c.triangle_disjoint_block hb), htcard, hbc.card_eq]
  refine ⟨isClique_of_choose_le_edgeCount ?_, hsize⟩
  rw [hsize, edgeCount_union G (c.triangle_disjoint_block hb),
    edgeCount_clique c.property.triangle_clique.isClique, edgeCount_clique hbc.isClique,
    htcard, hbc.card_eq, htri]
  decide +kernel

end Erdos577.TriangleChain
