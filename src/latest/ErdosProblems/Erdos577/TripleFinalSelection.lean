import ErdosProblems.Erdos577.TripleFinalRows

/-! Both later blocks belong to the untouched original family, with all final replacements. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {u : V}

lemma HeavyChoice.leaf_ge_three (h : HeavyChoice c p q a u) : 3 ≤ degreeIn G p.leaf a := by
  have hr := degreeIn_le_card G p.center a
  have hy := degreeIn_le_card G (q 3) a
  rw [h.heavy_complete.card_eq] at hr hy
  have hs := h.three_rows
  omega

lemma HeavyChoice.leaf_replaces_chosen (h : HeavyChoice c p q a u) :
    QuadOn G (insert p.leaf (a.erase u)) :=
  clique_replace_of_degree_three h.heavy_complete (h.paw_vertex_outside 0)
    h.leaf_ge_three h.chosen_mem

theorem HeavyChoice.exists_final_blocks (h : HeavyChoice c p q a u) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) :
    ∃ (j : Quadrilateral G) (s : Finset V) (z : V),
      j.support ∈ c.blocks ∧ j.support ≠ q.support ∧ j.support ≠ a ∧
      s ∈ c.blocks ∧ s ≠ q.support ∧ s ≠ a ∧ s ≠ j.support ∧
      (z = p.leaf ∨ z = u) ∧ QuadOn G (insert z (j.support.erase (j 3))) ∧
      CommonReplacement G p.center (p.vertices 3) (j 3) s := by
  obtain ⟨d, hd, hp, _, _, _, _, hblocks⟩ := h.exists_final_chain hc hcard hn
  obtain ⟨p', j, hleaf, hcenter, _, hsecond, hj⟩ :=
    hd.toFeasible.exists_triple_configuration_marked hcard hdeg hn h.finalPaw hp
  change p'.leaf = p.vertices 3 at hleaf
  change p'.center = p.center at hcenter
  change p'.vertices 2 = p.leaf ∨ p'.vertices 2 = u at hsecond
  have hjrow : 3 ≤ degreeIn G (p.vertices 3) j.support := by
    rw [← hleaf]
    exact hj.row_degrees.1.ge
  obtain ⟨hjold, hjQ, hja⟩ := h.original_block_of_third_three hblocks hj.block hjrow
  obtain ⟨s, hs, hsj, hheavy⟩ := hj.exists_heavy_block hcard hdeg hn
  obtain ⟨hcl, _, _, hsum⟩ := hj.heavy_block hd.toFeasible hcard hdeg hn hs hsj hheavy
  rw [hleaf, hcenter] at hsum
  have hsrow : 3 ≤ degreeIn G (p.vertices 3) s := by
    have hr := degreeIn_le_card G p.center s
    have hy := degreeIn_le_card G (j 3) s
    rw [hcl.card_eq] at hr hy
    omega
  obtain ⟨hsold, hsQ, hsa⟩ := h.original_block_of_third_three hblocks hs hsrow
  obtain ⟨w, hw, hcw, hrw, hrep⟩ :=
    three_rows_choose_complete_replacement hcl (p.vertices 3) p.center (j 3) hsum
  have hjcl := hj.second_replacement_complete
  exact ⟨j, s, p'.vertices 2, hjold, hjQ, hja, hsold, hsQ, hsa, hsj, hsecond,
    QuadOn.of_clique hjcl.card_eq hjcl.isClique,
    w, hw, hrw, hcw, QuadOn.of_clique hrep.card_eq hrep.isClique⟩

end Erdos577.UniversalTriple
