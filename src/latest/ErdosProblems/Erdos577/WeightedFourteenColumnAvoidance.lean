import ErdosProblems.Erdos577.WeightedFourteenTerminals

/-! A terminal replacement cannot leave two contacts into the retained triangle. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem replacement_triangle_degree_le_one {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) (tag : Fin 3)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (u : V) (hu : u ∈ a)
    (hrep : QuadOn G (insert (terminal p q tag) (a.erase u))) :
    degreeIn G u p.triangle ≤ 1 := by
  obtain ⟨d, _, hdx, hdt, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h tag
  have ha' := hkeep a ha hab
  rw [← hdx] at hrep
  have hl := (d.replaceBlock a ha' (d.swapTerminal ha' hu hrep)).terminal_degree_le_one hcard hn
  change degreeIn G u d.triangle ≤ 1 at hl
  rwa [hdt] at hl

theorem low_pair_not_both {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) (tag : Fin 3)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v : Quadrilateral G) (hv : v.support = a) (hcolumn : 2 ≤ degreeIn G (v 0) p.triangle) :
    ¬(G.Adj (terminal p q tag) (v 1) ∧ G.Adj (terminal p q tag) (v 3)) := by
  intro hedge
  obtain ⟨d, _, hdx, _, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h tag
  have hout : terminal p q tag ∉ v.support := by
    rw [← hdx, hv]
    exact d.terminal_not_mem_block (hkeep a ha hab)
  have hrep := v.quad_replaceAt 0 (terminal p q tag) hout (fun j hj ↦ by
    have hidx : ∀ j : Fin 4, (SimpleGraph.cycleGraph 4).Adj 0 j → j = 1 ∨ j = 3 := by
      decide +kernel
    have hj' := hidx j hj
    rcases hj' with rfl | rfl
    · exact hedge.1
    · exact hedge.2)
  rw [hv] at hrep
  have hl := replacement_triangle_degree_le_one hc hcard hn p hp hb q hq hd h tag ha hab
    (v 0) (hv ▸ (v.mem_support _).mpr ⟨0, rfl⟩) hrep
  omega

end Erdos577.WeightedFourteen
