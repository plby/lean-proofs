import ErdosProblems.Erdos577.CoreObstructionCounts

/-! The direct route has inside upper bound 34, giving both direct core consequences. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem direct_inside_upper {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (hdiag : ¬G.Adj (q 1) (q 3))
    (h0 : G.Adj c.terminal (q 0)) (h2 : G.Adj c.terminal (q 2))
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : ∀ v, v ∉ c.triangle ∪ b → 2 ≤ degreeIn G v (c.triangle ∪ b) →
      LocalFactor G (insert v (c.triangle ∪ b))) :
    contacts G (rows c q) (c.remainder ∪ (b ∪ q.support)) ≤ 34 := by
  have hrow := hc.toFeasible.high_pair_row q hq hdiag h0 h2
  have r := direct hc.toFeasible q hq hdiag hrow
  have hnb : b ∉ ({q.support} : Finset (Finset V)) := by
    simpa only [mem_singleton] using hbq
  have h1 := r.low_core_degree_le_one hcard hn hb hnb hcore 1 (Or.inl rfl)
  have h3 := r.low_core_degree_le_one hcard hn hb hnb hcore 3 (Or.inr rfl)
  have hlows := low_contacts_remainder_block c q hb
  rw [terminal_low_degree_zero q c.terminal hrow] at hlows
  have hself := hc.remainder_self_contacts hcard hn
  have hB := hc.block_contacts_le_twelve hcard hdeg hn hb
  have htwo : degreeIn G c.terminal q.support = 2 := by
    rw [q.degree_eq_mask c.terminal 5 hrow]
    decide +kernel
  have hC := hc.block_contacts_le_eight_of_terminal_two hcard hdeg hn hq (by omega)
  have hid := rows_inside_two_blocks c q hq hb hbq hdiag
  omega

theorem direct_core_factor_false {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (hdiag : ¬G.Adj (q 1) (q 3))
    (h0 : G.Adj c.terminal (q 0)) (h2 : G.Adj c.terminal (q 2))
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : ∀ v, v ∉ c.triangle ∪ b → 2 ≤ degreeIn G v (c.triangle ∪ b) →
      LocalFactor G (insert v (c.triangle ∪ b)))
    (hfactor : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {z : V} (hz : z ∈ c.triangle ∪ b) (hzl : G.Adj z (q 1))
    (hzrep : z ∈ b → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z x ∧ QuadOn G (insert y (b.erase z))) : False := by
  have hu := direct_inside_upper hc q hq hcard hdeg hn hdiag h0 h2 hb hbq hcore
  have hl := direct_inside_bound_of_highs hc q hq hcard hdeg hn hdiag h0 h2
    hb hbq hfactor hz hzl hzrep
  omega

theorem direct_core_degree_le_one {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (hdiag : ¬G.Adj (q 1) (q 3))
    (h0 : G.Adj c.terminal (q 0)) (h2 : G.Adj c.terminal (q 2))
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : ∀ v, v ∉ c.triangle ∪ b → 2 ≤ degreeIn G v (c.triangle ∪ b) →
      LocalFactor G (insert v (c.triangle ∪ b)))
    {z : V} (hz : z ∈ c.triangle ∪ b) (hzl : G.Adj z (q 1))
    (hzrep : z ∈ b → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z x ∧ QuadOn G (insert y (b.erase z))) :
    degreeIn G (q 2) (c.triangle ∪ b) ≤ 1 := by
  by_contra! hh
  have r := direct_of_highs hc.toFeasible q hq hdiag h0 h2
  have hnb : b ∉ ({q.support} : Finset (Finset V)) := by
    simpa only [mem_singleton] using hbq
  have hout : q 2 ∉ c.triangle ∪ b := by
    intro hh
    exact (mem_union.mp hh).elim (r.cycle_not_mem_triangle 2) (r.cycle_not_mem_block hb hnb 2)
  exact direct_core_factor_false hc q hq hcard hdeg hn hdiag h0 h2 hb hbq hcore
    (hcore (q 2) hout (by omega)) hz hzl hzrep

end Erdos577.CoreTransfer
