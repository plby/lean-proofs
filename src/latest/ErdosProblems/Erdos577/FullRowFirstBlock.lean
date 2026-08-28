import ErdosProblems.Erdos577.ClaimTwoTwo
import ErdosProblems.Erdos577.PawColumnCount

/-! The seven-contact dichotomy and exact first-block swap in Wang's full-row obstruction. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem last_diagonal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j)) : G.Adj (q 1) (q 3) := by
  have he := q.degree_after_erase_eq_three p.leaf 3 hrow
  rw [hq] at he
  have hh := (hc.presentPaw_feasible p hp).terminal_replacement_diagonal hs q hq 3 he
  exact hh.symm

theorem row_dichotomy {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support) :
    (G.IsNClique 4 q.support ∧ 3 ≤ degreeIn G (p.vertices 2) q.support) ∨
      (degreeIn G p.leaf q.support = 3 ∧ degreeIn G (p.vertices 2) q.support = 4) := by
  have hleaf := degreeIn_le_card G p.leaf q.support
  have hb := degreeIn_le_card G (p.vertices 2) q.support
  rw [q.card_support] at hleaf hb
  by_cases hfour : degreeIn G p.leaf q.support = 4
  · have hcl := (hc.presentPaw_feasible p hp).clique_of_terminal_degree_four hs
      (by change degreeIn G p.leaf s = 4; rwa [← hq])
    exact Or.inl ⟨hq.symm ▸ hcl, by omega⟩
  · have hthree : 3 ≤ degreeIn G p.leaf q.support := by
      have hh := degreeIn_mono G p.leaf (erase_subset (q 3) q.support)
      rw [q.degree_after_erase_eq_three p.leaf 3 hrow] at hh
      exact hh
    exact Or.inr ⟨by omega, by omega⟩

theorem noncentral_universal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hd : Disjoint p.support q.support)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    (u : V) (hu : u ∈ q.support) : QuadOn G (insert (p.vertices 2) (q.support.erase u)) := by
  have hout : p.vertices 2 ∉ q.support := fun hh ↦ disjoint_left.mp hd
    ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩) hh
  rcases row_dichotomy hc p hp hs q hq hrow hseven with ⟨hcl, hb⟩ | ⟨_, hb⟩
  · exact clique_replace_of_degree_three hcl hout hb hu
  · exact (show QuadOn G q.support from ⟨q, rfl⟩).replace_of_degree_four hout hb hu

theorem first_replacement {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j)) :
    QuadOn G (insert p.leaf (q.support.erase (q 3))) ∧
      edgeCount G (insert p.leaf (q.support.erase (q 3))) = edgeCount G q.support := by
  have hout : p.leaf ∉ q.support := by
    rw [hq]
    exact (c.presentPaw p hp).terminal_not_mem_block hs
  have hm : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hthree := q.degree_after_erase_eq_three p.leaf 3 hrow
  have hlast : degreeIn G (q 3) q.support = 3 := by
    have hh := (hc.presentPaw_feasible p hp).terminal_replacement_degree hs (hq ▸ hm)
      (by change degreeIn G p.leaf (s.erase (q 3)) = 3; rwa [← hq])
    rwa [← hq] at hh
  refine ⟨(show QuadOn G q.support from ⟨q, rfl⟩).replace_of_three_after_erase hout hm hthree, ?_⟩
  have he := edgeCount_replace G (q 3) p.leaf hm hout
  omega

theorem exists_first_swap {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j)) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q 3 ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))} := by
  obtain ⟨hr, he⟩ := first_replacement hc p hp hs q hq hrow
  rw [hq] at hr he
  exact (hc.presentPaw_feasible p hp).exists_terminal_swap hs
    (hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩) hr he

theorem last_triangle_row {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hb3 : G.Adj (p.vertices 2) (q 3)) :
    ∀ u ∈ p.triangle, G.Adj (q 3) u ↔ u = p.vertices 2 := by
  obtain ⟨d, _, ht, hT, _, _, _⟩ := exists_first_swap hc p hp hs q hq hrow
  have hbnd := d.terminal_degree_le_one hcard hn
  rw [ht, hT] at hbnd
  have hm : p.vertices 2 ∈ p.triangle.filter (G.Adj (q 3)) :=
    mem_filter.mpr ⟨by simp [Paw.triangle], hb3.symm⟩
  have he : ({p.vertices 2} : Finset V) = p.triangle.filter (G.Adj (q 3)) :=
    eq_of_subset_of_card_le (singleton_subset_iff.mpr hm)
      (by simpa only [card_singleton, degreeIn] using hbnd)
  intro u hu
  constructor
  · intro hh
    exact mem_singleton.mp (he.symm ▸ mem_filter.mpr ⟨hu, hh⟩)
  · rintro rfl
    exact hb3.symm

end Erdos577.FullRow
