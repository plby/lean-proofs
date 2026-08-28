import ErdosProblems.Erdos577.FullLeafSparseCounts

/-! A full terminal row permits an actual equal-score swap, without a paw premise. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_terminal_swap {c : TriangleChain G} (hc : c.Feasible)
    {j : Finset V} (hj : j ∈ c.blocks) (hrow : degreeIn G c.terminal j = 4)
    {v : V} (hv : v ∈ j) :
    ∃ e : TriangleChain G, e.Feasible ∧ e.terminal = v ∧ e.triangle = c.triangle ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      e.blocks = c.blocks.erase j ∪ {insert c.terminal (j.erase v)} := by
  have hcl := hc.clique_of_terminal_degree_four hj hrow
  have hout := c.terminal_not_mem_block hj
  have hrep := (c.property.blocks_quad j hj).replace_of_degree_four hout hrow hv
  have hvrow := degreeIn_clique G hcl.isClique hv
  rw [hcl.card_eq] at hvrow
  have hadj := (degreeIn_eq_card_iff c.terminal j).mp (hrow.trans hcl.card_eq.symm) v hv
  have herase := degreeIn_erase_add G c.terminal v hv
  rw [hrow, if_pos hadj] at herase
  have hscore := edgeCount_replace G v c.terminal hv hout
  exact hc.exists_terminal_swap hj hv hrep (by omega)

end Erdos577.FullLeafSparse
