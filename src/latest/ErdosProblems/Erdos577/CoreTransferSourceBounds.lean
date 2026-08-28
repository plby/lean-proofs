import ErdosProblems.Erdos577.CoreTransferInsideBound

/-! The explicit direct and bridge cases of TeX 9.37, with inside bounds 35 and 47. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem direct_inside_bound {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (hdiag : ¬G.Adj (q 1) (q 3))
    (hrow : ∀ j : Fin 4, G.Adj c.terminal (q j) ↔ (5 : ℕ).testBit j.val = true)
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {z : V} (hz : z ∈ c.triangle ∪ b) (hzl : G.Adj z (q 1))
    (hzrep : z ∈ b → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z x ∧ QuadOn G (insert y (b.erase z))) :
    35 ≤ contacts G (rows c q) (c.remainder ∪ (b ∪ q.support)) := by
  have hnb : b ∉ ({q.support} : Finset (Finset V)) := by
    simpa only [mem_singleton] using hbq
  have hh := inside_bound hc (direct hc.toFeasible q hq hdiag hrow)
    hcard hdeg hn hb hnb hcore hz hzl hzrep
  rw [card_insert_of_notMem hnb, card_singleton] at hh
  simp only [biUnion_insert, singleton_biUnion, id_eq] at hh
  omega

theorem bridge_inside_bound {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (hdiag : ¬G.Adj (q 1) (q 3)) {d : Finset V} (hd : d ∈ c.blocks) (hdq : d ≠ q.support)
    (y : V) (hy : y ∈ d) (hrep : QuadOn G (insert c.terminal (d.erase y)))
    (hscore : edgeCount G (insert c.terminal (d.erase y)) = edgeCount G d)
    (hrow : ∀ j : Fin 4, G.Adj y (q j) ↔ (5 : ℕ).testBit j.val = true)
    (hhigh : G.Adj c.terminal (q 0))
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support) (hbd : b ≠ d)
    (hcore : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {z : V} (hz : z ∈ c.triangle ∪ b) (hzl : G.Adj z (q 1))
    (hzrep : z ∈ b → ∃ x ∈ c.triangle, ∃ x' ∈ c.triangle,
      x ≠ x' ∧ G.Adj z x ∧ QuadOn G (insert x' (b.erase z))) :
    47 ≤ contacts G (rows c q) (c.remainder ∪ (b ∪ (q.support ∪ d))) := by
  have hnb : b ∉ ({q.support, d} : Finset (Finset V)) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hbq, hbd⟩
  have hh := inside_bound hc (bridge hc.toFeasible q hq hdiag hd hdq y hy hrep hscore hrow hhigh)
    hcard hdeg hn hb hnb hcore hz hzl hzrep
  rw [card_insert_of_notMem hnb, card_pair hdq.symm] at hh
  simp only [biUnion_insert, singleton_biUnion, id_eq] at hh
  omega

end Erdos577.CoreTransfer
