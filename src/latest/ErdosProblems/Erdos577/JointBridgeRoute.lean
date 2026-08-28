import ErdosProblems.Erdos577.JointBridgeTerminal

/-! Each positive alternative exposes a center-neighbor through one or two equal-score swaps. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_center_route {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s b : Finset V} (hs : s ∈ c.blocks) (hb : b ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseTwo p q)
    (hpositive : Positive p q b) :
    ∃ u ∈ b, G.Adj p.center u ∧ ∃ d : TriangleChain G,
      d.Strong ∧ d.terminal = u ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      ∀ j ∈ c.blocks, j ≠ s → j ≠ b → j ∈ d.blocks := by
  obtain ⟨_, hr3, hcases⟩ := positive_degrees p q (c.property.blocks_quad b hb).card hpositive
  have hneighbor : ∃ u ∈ b, G.Adj p.center u := by
    obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (b.filter (G.Adj p.center)).card from by
      change 0 < degreeIn G p.center b
      omega)
    exact ⟨u, (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  rcases hcases with ht4 | ⟨ht3, hr4⟩ | ⟨hx4, _⟩
  · obtain ⟨u, hu, hru⟩ := hneighbor
    obtain ⟨d, hd, ht, hT, _, he, hcomp, _, hkeep⟩ :=
      JointClaims.exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
    obtain ⟨e, hed, het, heT, hee, hec, hblocks⟩ := full_row_exposes_neighbor hd.toFeasible
      hcard hn p hT (hkeep b hb hbs) (by rw [ht]; exact ht4) u hu hru
    refine ⟨u, hu, hru, e, hed, het, heT, hee.trans he, hec.trans hcomp, ?_⟩
    intro j hj hjs hjb
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hjb, hkeep j hj hjs⟩)
  · have hmiss : ∃ u ∈ b, ¬G.Adj (q 3) u := by
      by_contra! hall
      have he := (degreeIn_eq_card_iff (q 3) b).mpr hall
      rw [(c.property.blocks_quad b hb).card, ht3] at he
      contradiction
    obtain ⟨u, hu, hmiss⟩ := hmiss
    have hru := (degreeIn_eq_card_iff p.center b).mp
      (hr4.trans (c.property.blocks_quad b hb).card.symm) u hu
    obtain ⟨d, hd, ht, hT, _, he, hcomp, _, hkeep⟩ :=
      JointClaims.exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
    obtain ⟨e, hed, het, heT, hee, hec, hblocks⟩ := missed_row_exposes_neighbor hd.toFeasible
      hcard hn p hT (hkeep b hb hbs) (by rw [ht]; exact ht3) u hu
      (by rw [ht]; exact hmiss) hru
    refine ⟨u, hu, hru, e, hed, het, heT, hee.trans he, hec.trans hcomp, ?_⟩
    intro j hj hjs hjb
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hjb, hkeep j hj hjs⟩)
  · obtain ⟨u, hu, hru⟩ := hneighbor
    obtain ⟨d, hd, ht, hT, he, hcomp, hblocks⟩ :=
      full_row_exposes_neighbor (hc.presentPaw_feasible p hp) hcard hn p rfl hb hx4 u hu hru
    refine ⟨u, hu, hru, d, hd, ht, hT, he, hcomp, ?_⟩
    intro j hj _ hjb
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hjb, hj⟩)

end Erdos577.JointBridge
