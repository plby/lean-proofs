import ErdosProblems.Erdos577.HighPairLeafExchange

/-! Equal-score terminal swaps apply to arbitrary triangle chains,
including an intermediate terminal with no triangle attachment. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Feasible.exists_terminal_swap {c : TriangleChain G} (hc : c.Feasible)
    {b : Finset V} (hb : b ∈ c.blocks) {u : V} (hu : u ∈ b)
    (hq : QuadOn G (insert c.terminal (b.erase u)))
    (he : edgeCount G (insert c.terminal (b.erase u)) = edgeCount G b) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = u ∧ d.triangle = c.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase b ∪ {insert c.terminal (b.erase u)} := by
  let l := c.swapTerminal hb hu hq
  let d := c.replaceBlock b hb l
  have hs := c.replaceBlock_scores_eq hb l he
  exact ⟨d, hc.replaceBlock_feasible hb l he, rfl, rfl, hs.1, hs.2, rfl⟩

theorem Feasible.exists_high_pair_terminal {c : TriangleChain G} (hc : c.Feasible)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks)
    (hn : ¬G.Adj (q 1) (q 3))
    (hrow : ∀ j : Fin 4, G.Adj c.terminal (q j) ↔ (5 : ℕ).testBit j.val = true)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q i ∧ d.triangle = c.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase q.support ∪ {insert c.terminal (q.support.erase (q i))} := by
  have hx := c.terminal_not_mem_block hq
  exact hc.exists_terminal_swap hq ((q.mem_support _).mpr ⟨i, rfl⟩)
    (q.high_pair_replace c.terminal hx hrow i hi)
    (q.high_pair_replace_score c.terminal hx hn hrow i hi)

end Erdos577.TriangleChain
