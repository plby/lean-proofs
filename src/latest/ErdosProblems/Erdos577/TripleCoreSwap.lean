import ErdosProblems.Erdos577.TripleCoreCount
import ErdosProblems.Erdos577.TerminalSwap

/-! The actual feasible exposed-terminal chain; no attachment to its triangle is assumed. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G}

lemma Configuration.leaf_replacement_score (h : Configuration c p q) :
    edgeCount G (insert p.leaf (q.support.erase (q 3))) = edgeCount G q.support := by
  rw [edgeCount_clique h.leaf_replacement_complete.isClique,
    h.leaf_replacement_complete.card_eq, edgeCount_clique h.complete.isClique,
    h.complete.card_eq]

theorem Configuration.exists_exposed_chain (h : Configuration c p q) (hc : c.Feasible) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q 3 ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase q.support ∪ {insert p.leaf (q.support.erase (q 3))} := by
  exact (hc.presentPaw_feasible p h.paw).exists_terminal_swap h.block
    ((q.mem_support _).mpr ⟨3, rfl⟩)
    (QuadOn.of_clique h.leaf_replacement_complete.card_eq h.leaf_replacement_complete.isClique)
    h.leaf_replacement_score

theorem Configuration.exposed_triangle_column (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {a : Finset V} (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hrow : 3 ≤ degreeIn G (q 3) a) {v : V} (hv : v ∈ a) :
    degreeIn G v p.triangle ≤ 1 := by
  obtain ⟨d, hd, hY, hT, _, _, hblocks⟩ := h.exists_exposed_chain hc
  have ha' : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨haq, ha⟩)
  have hrep := hd.terminal_universal_replace ha' (by rw [hY]; exact hrow) hv
  have hb := (d.replaceBlock a ha' (d.swapTerminal ha' hv hrep)).terminal_degree_le_one hcard hn
  change degreeIn G v d.triangle ≤ 1 at hb
  rwa [hT] at hb

theorem Configuration.exposed_triangle_contacts (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {a : Finset V} (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hrow : 3 ≤ degreeIn G (q 3) a) : contacts G p.triangle a ≤ 4 := by
  rw [contacts_comm]
  calc
    _ ≤ ∑ _ ∈ a, 1 := sum_le_sum (fun _ hv ↦ h.exposed_triangle_column hc hcard hn ha haq hrow hv)
    _ = 4 := by simp [(c.property.blocks_quad a ha).card]

end Erdos577.UniversalTriple
