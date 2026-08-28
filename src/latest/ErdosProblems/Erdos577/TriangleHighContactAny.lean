import ErdosProblems.Erdos577.TriangleHighContact
import ErdosProblems.Erdos577.CliqueLabels

/-! The complete-block case of the high-column contact argument, without a score premise. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Feasible.terminal_high_contact_any_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hfull : ∀ u ∈ c.triangle, G.Adj (q 0) u)
    (hrow : degreeIn G c.terminal q.support = 2) : G.Adj c.terminal (q 0) := by
  by_cases hscore : edgeCount G b ≤ 5
  · exact hc.terminal_high_contact hcard hn hb q hq hfull hscore hrow
  by_contra hnon
  have hbound := (c.property.blocks_quad b hb).edgeCount_le_six
  have hcl : G.IsNClique 4 b := clique_of_four_six (c.property.blocks_quad b hb).card (by omega)
  have hu : q 0 ∈ b := hq ▸ (q.mem_support _).mpr ⟨0, rfl⟩
  have he := degreeIn_erase_add G c.terminal (q 0) hu
  rw [if_neg hnon, ← hq, hrow] at he
  have hrep := (clique_replace_iff_two_contacts hcl (c.terminal_not_mem_block hb) hu).mpr
    (by rw [← hq]; omega)
  have hl := (c.replaceBlock b hb (c.swapTerminal hb hu hrep)).terminal_degree_le_one hcard hn
  change degreeIn G (q 0) c.triangle ≤ 1 at hl
  have hcol := (degreeIn_eq_card_iff (q 0) c.triangle).mpr hfull
  rw [c.property.triangle_clique.card_eq] at hcol
  omega

end Erdos577.TriangleChain
