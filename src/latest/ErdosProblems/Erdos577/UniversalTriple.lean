import ErdosProblems.Erdos577.UniversalTripleWeight
import ErdosProblems.Erdos577.LargeLeafPreparation

/-! Property A for every feasible paw presentation, with the bound on every block. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.exists_three_leaf_block {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder) :
    ∃ s ∈ c.blocks, degreeIn G p.leaf s = 3 ∧ G.IsNClique 4 s ∧
      (∀ a ∈ c.blocks, contacts G p.triangle a ≤ 10) ∧
      ((s.filter (G.Adj (p.vertices 2)) = s.filter (G.Adj p.leaf) ∧
        s.filter (G.Adj (p.vertices 3)) = ∅) ∨
       (s.filter (G.Adj (p.vertices 3)) = s.filter (G.Adj p.leaf) ∧
        s.filter (G.Adj (p.vertices 2)) = ∅)) := by
  obtain ⟨s, hs, hheavy⟩ := c.exists_doubled_leaf_heavy hcard hdeg hn p hp
  obtain ⟨q, hq⟩ := c.property.blocks_quad s hs
  have hsmall : ¬degreeIn G p.leaf s ≤ 2 := by
    intro hh
    have hbound := hc.small_leaf_weight_le_eight hcard hdeg hn p hp hs q hq
      (by rw [hq]; exact hh)
    rw [hq] at hbound
    omega
  have hfour : degreeIn G p.leaf s ≠ 4 := by
    intro hh
    obtain ⟨h2, h3⟩ := hc.claim_two_six hcard hdeg hn p hp hs hh
    omega
  have hmax := degreeIn_le_card G p.leaf s
  rw [(c.property.blocks_quad s hs).card] at hmax
  have hthree : degreeIn G p.leaf s = 3 := by omega
  obtain ⟨hcl, hother, hrows⟩ := hc.three_leaf_preparation hcard hdeg hn p hp hs
    hthree (by omega)
  refine ⟨s, hs, hthree, hcl, ?_, hrows⟩
  intro a ha
  by_cases he : a = s
  · subst a
    exact (JointClaims.triangle_contacts_le_four hc hcard hn p hp hs (by omega)).trans
      (by decide)
  · exact hother a ha he

theorem TriangleChain.Feasible.paw_triangle_block_bound {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) :
    ∀ a ∈ c.blocks, contacts G p.triangle a ≤ 10 := by
  obtain ⟨_, _, _, _, hb, _⟩ := hc.exists_three_leaf_block hcard hdeg hn p hp
  exact hb

theorem TriangleChain.Feasible.exists_ordered_three_leaf_block {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) :
    ∃ (p' : Paw G) (s : Finset V), p'.leaf = p.leaf ∧ p'.triangle = p.triangle ∧
      p'.support = p.support ∧ s ∈ c.blocks ∧ degreeIn G p'.leaf s = 3 ∧
      G.IsNClique 4 s ∧ (∀ a ∈ c.blocks, contacts G p'.triangle a ≤ 10) ∧
      s.filter (G.Adj (p'.vertices 2)) = s.filter (G.Adj p'.leaf) ∧
      s.filter (G.Adj (p'.vertices 3)) = ∅ := by
  obtain ⟨s, hs, hthree, hcl, hb, hrows⟩ :=
    hc.exists_three_leaf_block hcard hdeg hn p hp
  rcases hrows with ⟨h2, h3⟩ | ⟨h3, h2⟩
  · exact ⟨p, s, rfl, rfl, rfl, hs, hthree, hcl, hb, h2, h3⟩
  · refine ⟨p.swapNoncentral, s, p.swapNoncentral_leaf, p.swapNoncentral_triangle,
      p.swapNoncentral_support, hs, ?_, hcl, ?_, ?_, ?_⟩
    · simpa only [Paw.swapNoncentral_leaf] using hthree
    · simpa only [Paw.swapNoncentral_triangle] using hb
    · change s.filter (G.Adj (p.vertices 3)) = s.filter (G.Adj p.leaf)
      exact h3
    · simpa only [Paw.swapNoncentral_apply, Equiv.swap_apply_right] using h2

end Erdos577
