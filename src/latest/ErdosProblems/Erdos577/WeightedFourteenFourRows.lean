import ErdosProblems.Erdos577.FirstPawFourExact
import ErdosProblems.Erdos577.TriangleHighContactAny
import ErdosProblems.Erdos577.WeightedFourteenFactors
import ErdosProblems.Erdos577.WeightedFourteenTerminals
import ErdosProblems.Erdos577.PairReplacements

/-! The exact case-(4) rows at pattern (14)'s heavy block, including its sole diagonal. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem four_center_obstructions {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v : Quadrilateral G) (hv : v.support = a) (swap : Bool)
    (h4 : PawBlock.Pattern4 (FirstPaw.normalizedPaw p swap) v)
    (hx2 : degreeIn G p.leaf a = 2) (hy2 : degreeIn G (q 1) a = 2)
    (hcolumn : degreeIn G (v 0) p.triangle = 3) :
    ¬G.Adj (v 1) (v 3) ∧ ¬(G.Adj p.center (v 1) ∧ G.Adj p.center (v 3)) := by
  have hxrow := h4.leaf_exact (FirstPaw.normalizedPaw p swap) v
    (by rw [FirstPaw.normalizedPaw_leaf, hv]; exact hx2)
  have hx0 := (hxrow 0).mpr (by decide)
  change G.Adj (FirstPaw.normalizedPaw p swap).leaf (v 0) at hx0
  rw [FirstPaw.normalizedPaw_leaf] at hx0
  obtain ⟨d, hdF, hdx, hdt, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h 1
  change d.terminal = q 1 at hdx
  have hfull : ∀ u ∈ p.triangle, G.Adj (v 0) u :=
    (degreeIn_eq_card_iff (v 0) p.triangle).mp (hcolumn.trans p.triangle_clique.card_eq.symm)
  have hy0 := hdF.terminal_high_contact_any_block hcard hn (hkeep a ha hab) v hv
    (by rw [hdt]; exact hfull) (by rw [hdx, hv]; exact hy2)
  rw [hdx] at hy0
  have hu : v 0 ∈ a := hv ▸ (v.mem_support _).mpr ⟨0, rfl⟩
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab 8
  change ¬CommonReplacement G p.leaf (q 1) p.center a at hno
  have hnr : ¬QuadOn G (insert p.center (a.erase (v 0))) := fun hr ↦
    hno ⟨v 0, hu, hx0, hy0, hr⟩
  have hrout : p.center ∉ v.support := by
    intro hh
    have hmem : p.center ∈ c.remainder := by
      rw [← hp, p.support_eq]
      exact mem_insert_of_mem p.center_mem_triangle
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha (hv ▸ hh))).2 hmem
  have hr3 := h4.2.1
  rw [FirstPaw.normalizedPaw_center] at hr3
  constructor
  · intro he
    have hcl := v.clique_of_diagonals h4.1 he
    have hrep := clique_replace_of_degree_three hcl hrout hr3
      ((v.mem_support _).mpr ⟨0, rfl⟩)
    rw [hv] at hrep
    exact hnr hrep
  · intro he
    have hrep := v.quad_replaceAt 0 p.center hrout (fun j hj ↦ by
      have hidx : ∀ j : Fin 4, (SimpleGraph.cycleGraph 4).Adj 0 j → j = 1 ∨ j = 3 := by
        decide +kernel
      rcases hidx j hj with rfl | rfl
      · exact he.1
      · exact he.2)
    rw [hv] at hrep
    exact hnr hrep

theorem four_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v : Quadrilateral G) (hv : v.support = a) (swap : Bool)
    (h4 : PawBlock.Pattern4 (FirstPaw.normalizedPaw p swap) v)
    (hx2 : degreeIn G p.leaf a = 2) (hy2 : degreeIn G (q 1) a = 2)
    (hE : 9 ≤ contacts G p.support a) :
    contacts G p.support a = 9 ∧ ∃ w : Quadrilateral G, w.support = a ∧
      PawBlock.OnlyFirst w ∧ PawBlock.ExactRows p w ![5, 13, 5, 5] := by
  let z := FirstPaw.normalizedPaw p swap
  obtain ⟨w, hws, hw4, hcol⟩ := h4.exists_full_first z v
    (by rw [FirstPaw.normalizedPaw_leaf, hv]; exact hx2)
    (by rw [FirstPaw.normalizedPaw_support, hv]; exact hE)
  have hwa : w.support = a := hws.trans hv
  rw [FirstPaw.normalizedPaw_triangle] at hcol
  obtain ⟨hdiag, hnot⟩ := four_center_obstructions hc hcard hn p hp hb q hq hd h ha hab
    w hwa swap hw4 hx2 hy2 hcol
  obtain ⟨htotal, hrows⟩ := hw4.exact_rows_of_center_no_both z w
    (by rw [FirstPaw.normalizedPaw_leaf, hwa]; exact hx2)
    (by rw [FirstPaw.normalizedPaw_support, hwa]; exact hE)
    (by rw [FirstPaw.normalizedPaw_center]; exact hnot)
  rw [FirstPaw.normalizedPaw_support, hwa] at htotal
  refine ⟨htotal, ?_⟩
  rcases hrows with hr | hr
  · exact ⟨w, hwa, ⟨hw4.1, hdiag⟩, hr.four_unnormalize p w swap⟩
  · refine ⟨w.reverse, (w.reverse_support).trans hwa, ?_, ?_⟩
    · constructor
      · exact hw4.1
      · exact fun he ↦ hdiag he.symm
    · exact (hr.four_reverse z w).four_unnormalize p w.reverse swap

end Erdos577.WeightedFourteen
