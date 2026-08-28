import ErdosProblems.Erdos577.JointSetupCount

/-! TeX9.47: the full joint initial exchange and its six-row outside sum. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem initial_exchange_and_six_row_sum {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (h : CaseOne p q ∨ CaseTwo p q) :
    degreeIn G (p.vertices 3) q.support = 0 ∧
      Disjoint (q.support.filter (G.Adj p.center)) (q.support.filter (G.Adj (p.vertices 2))) ∧
      (∃ (d : TriangleChain G) (p' : Paw G), d.Strong ∧ d.terminal = q 3 ∧
        d.triangle = p.triangle ∧ p'.leaf = q 3 ∧ p'.center = p.vertices 2 ∧
        p'.vertices 2 = p.center ∧ p'.vertices 3 = p.vertices 3 ∧ p'.triangle = p.triangle ∧
        p'.support = d.remainder ∧ d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
        d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))} ∧
        ∀ a ∈ c.blocks, a ≠ s → a ∈ d.blocks) ∧
      (∃ a ∈ c.blocks, a ≠ s ∧
        13 ≤ degreeIn G p.leaf a + degreeIn G (q 3) a + degreeIn G p.center a +
          degreeIn G (p.vertices 2) a + 2 * degreeIn G (p.vertices 3) a) ∧
      (¬QuadOn G (insert (p.vertices 2) (q.support.erase (q 3))) → CaseOne p q) := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hthree : 3 ≤ degreeIn G p.leaf s := hq ▸ leaf_lower p q h
  have hdis := triangle_rows_disjoint hc hcard hn p hp hs hthree p.center (p.vertices 2)
    p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  rw [← hq] at hdis
  obtain ⟨d, hstrong, ht, hT, hp', he, hcomp, hblocks, hkeep⟩ :=
    exists_exposed_chain hc hcard hn p hp hs q hq hd h
  obtain ⟨a, ha, has, hheavy⟩ := exists_heavy_block hc hcard hdeg hn p hp hs q hq h
  rw [sixWeight_eq_rows] at hheavy
  exact ⟨third_row_zero hc hcard hn p hp hs q hq h, hdis,
    ⟨d, exposedPaw p q hd h, hstrong, ht, hT, rfl, rfl, rfl, rfl,
      exposedPaw_triangle p q hd h, hp', he, hcomp, hblocks, hkeep⟩,
    ⟨a, ha, has, hheavy⟩, case_one_of_failed_replacement hc p hp hs q hq h⟩

end Erdos577.JointClaims
