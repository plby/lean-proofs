import ErdosProblems.Erdos577.CoreReplacementFactor
import ErdosProblems.Erdos577.FeasibleHighPair
import ErdosProblems.Erdos577.CoreTransferSourceBounds

/-! High contacts suffice to obtain the two exact core routes and their low-neighbor bounds. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem bridge_row {c : TriangleChain G} (hc : c.Feasible)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks)
    (hdiag : ¬G.Adj (q 1) (q 3)) {d : Finset V} (hd : d ∈ c.blocks) (hdq : d ≠ q.support)
    (y : V) (hy : y ∈ d) (hrep : QuadOn G (insert c.terminal (d.erase y)))
    (hscore : edgeCount G (insert c.terminal (d.erase y)) = edgeCount G d)
    (h0 : G.Adj y (q 0)) (h2 : G.Adj y (q 2)) :
    ∀ j : Fin 4, G.Adj y (q j) ↔ (5 : ℕ).testBit j.val = true := by
  obtain ⟨d', hd', ht, _, _, _, hblocks⟩ := hc.exists_terminal_swap hd hy hrep hscore
  have hq' : q.support ∈ d'.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hdq.symm, hq⟩)
  have hr := hd'.high_pair_row q hq' hdiag (by rw [ht]; exact h0) (by rw [ht]; exact h2)
  simpa only [ht] using hr

theorem direct_of_highs {c : TriangleChain G} (hc : c.Feasible)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks)
    (hdiag : ¬G.Adj (q 1) (q 3))
    (h0 : G.Adj c.terminal (q 0)) (h2 : G.Adj c.terminal (q 2)) :
    Route c q {q.support} := direct hc q hq hdiag (hc.high_pair_row q hq hdiag h0 h2)

theorem bridge_of_highs {c : TriangleChain G} (hc : c.Feasible)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks)
    (hdiag : ¬G.Adj (q 1) (q 3)) {d : Finset V} (hd : d ∈ c.blocks) (hdq : d ≠ q.support)
    (y : V) (hy : y ∈ d) (hrep : QuadOn G (insert c.terminal (d.erase y)))
    (hscore : edgeCount G (insert c.terminal (d.erase y)) = edgeCount G d)
    (h0 : G.Adj y (q 0)) (h2 : G.Adj y (q 2)) (hhigh : G.Adj c.terminal (q 0)) :
    Route c q {q.support, d} :=
  bridge hc q hq hdiag hd hdq y hy hrep hscore
    (bridge_row hc q hq hdiag hd hdq y hy hrep hscore h0 h2) hhigh

theorem Route.low_core_degree_le_one {c : TriangleChain G} {q : Quadrilateral G}
    {bs : Finset (Finset V)} (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hnb : b ∉ bs)
    (hcore : ∀ v, v ∉ c.triangle ∪ b → 2 ≤ degreeIn G v (c.triangle ∪ b) →
      LocalFactor G (insert v (c.triangle ∪ b)))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : degreeIn G (q i) (c.triangle ∪ b) ≤ 1 := by
  by_contra! hh
  have hout : q i ∉ c.triangle ∪ b := by
    intro hh
    exact (mem_union.mp hh).elim (r.cycle_not_mem_triangle i) (r.cycle_not_mem_block hb hnb i)
  exact r.no_local_factor hcard hn i hi hb hnb (hcore (q i) hout (by omega))

theorem direct_inside_bound_of_highs {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (hdiag : ¬G.Adj (q 1) (q 3))
    (h0 : G.Adj c.terminal (q 0)) (h2 : G.Adj c.terminal (q 2))
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {z : V} (hz : z ∈ c.triangle ∪ b) (hzl : G.Adj z (q 1))
    (hzrep : z ∈ b → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z x ∧ QuadOn G (insert y (b.erase z))) :
    35 ≤ contacts G (rows c q) (c.remainder ∪ (b ∪ q.support)) :=
  direct_inside_bound hc q hq hcard hdeg hn hdiag (hc.toFeasible.high_pair_row q hq hdiag h0 h2)
    hb hbq hcore hz hzl hzrep

end Erdos577.CoreTransfer
