import ErdosProblems.Erdos577.FullRowFirstBlock

/-! The actual swapped chain is strong and its new first block has at most eight paw contacts. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_strong_first_swap {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hb3 : G.Adj (p.vertices 2) (q 3)) :
    ∃ d : TriangleChain G, d.Strong ∧ d.terminal = q 3 ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))} := by
  obtain ⟨d, hdf, ht, hT, he, hcomp, hblocks⟩ := exists_first_swap hc p hp hs q hq hrow
  have hbnd := d.terminal_degree_le_one hcard hn
  rw [ht, hT] at hbnd
  have hpos : 0 < degreeIn G (q 3) p.triangle := card_pos.mpr
    ⟨p.vertices 2, mem_filter.mpr ⟨by simp [Paw.triangle], hb3.symm⟩⟩
  have hattach : d.attachmentScore = 1 := by
    change degreeIn G d.terminal d.triangle = 1
    rw [ht, hT]
    omega
  exact ⟨d, ⟨hdf, hattach⟩, ht, hT, he, hcomp, hblocks⟩

theorem replacement_last_degree {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j)) :
    3 ≤ degreeIn G (q 3) (insert p.leaf (q.support.erase (q 3))) := by
  have hd := last_diagonal hc p hp hs q hq hrow
  have hthree : degreeIn G (q 3) q.support = 3 := by
    rw [q.degreeIn_eq]
    change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 3
    rw [if_pos hd.symm]
  have hh := degreeIn_mono G (q 3) (subset_insert p.leaf (q.support.erase (q 3)))
  rw [degreeIn_erase_self G (q 3) ((q.mem_support _).mpr ⟨3, rfl⟩), hthree] at hh
  exact hh

theorem exists_bounded_first_swap {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hb3 : G.Adj (p.vertices 2) (q 3)) :
    ∃ d : TriangleChain G, d.Strong ∧ d.terminal = q 3 ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))} ∧
      contacts G d.remainder (insert p.leaf (s.erase (q 3))) ≤ 8 := by
  obtain ⟨d, hd, ht, hT, he, hcomp, hblocks⟩ :=
    exists_strong_first_swap hc hcard hn p hp hs q hq hrow hb3
  have hnew : insert p.leaf (s.erase (q 3)) ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_right _ (mem_singleton_self _)
  have hrow' := replacement_last_degree hc p hp hs q hq hrow
  rw [hq] at hrow'
  have htwo : 2 ≤ degreeIn G d.terminal (insert p.leaf (s.erase (q 3))) := by rw [ht]; omega
  exact ⟨d, hd, ht, hT, he, hcomp, hblocks,
    hd.block_contacts_le_eight_of_terminal_two hcard hdeg hn hnew htwo⟩

end Erdos577.FullRow
