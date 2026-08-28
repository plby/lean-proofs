import ErdosProblems.Erdos577.LargeLeafThreeComplete

/-! TeX9.70: complete full-leaf and three-leaf preparations in the original graph and labels. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.full_leaf_preparation {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (hfull : degreeIn G p.leaf s = 4)
    (hpositive : 1 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s) :
    degreeIn G p.center s = 0 ∧ degreeIn G (p.vertices 2) s ≤ 1 ∧
      degreeIn G (p.vertices 3) s ≤ 1 ∧
      ∃ a ∈ c.blocks, a ≠ s ∧ 11 ≤ contacts G p.triangle a :=
  LargeLeaf.full_preparation hc hcard hdeg hn p hp hs hfull hpositive

theorem TriangleChain.Feasible.three_leaf_preparation {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s) :
    G.IsNClique 4 s ∧ (∀ a ∈ c.blocks, a ≠ s → contacts G p.triangle a ≤ 10) ∧
      ((s.filter (G.Adj (p.vertices 2)) = s.filter (G.Adj p.leaf) ∧
        s.filter (G.Adj (p.vertices 3)) = ∅) ∨
       (s.filter (G.Adj (p.vertices 3)) = s.filter (G.Adj p.leaf) ∧
        s.filter (G.Adj (p.vertices 2)) = ∅)) := by
  have hbound (a : Finset V) (ha : a ∈ c.blocks) (has : a ≠ s) :
      contacts G p.triangle a ≤ 10 :=
    LargeLeaf.three_triangle_bound hc hcard hdeg hn p hp hs hthree hnon ha has
  by_cases hb : 2 ≤ degreeIn G (p.vertices 2) s
  · obtain ⟨hcl, hrow, hzero⟩ := LargeLeaf.three_preparation_ordered hc hcard hdeg hn p hp hs
      hthree hnon hb
    exact ⟨hcl, hbound, Or.inl ⟨hrow, hzero⟩⟩
  · have hnon' : 3 ≤ degreeIn G (p.swapNoncentral.vertices 2) s +
        degreeIn G (p.swapNoncentral.vertices 3) s := by
      simp only [Paw.swapNoncentral_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      omega
    have hb' : 2 ≤ degreeIn G (p.swapNoncentral.vertices 2) s := by
      simp only [Paw.swapNoncentral_apply, Equiv.swap_apply_left]
      omega
    obtain ⟨hcl, hrow, hzero⟩ := LargeLeaf.three_preparation_ordered hc hcard hdeg hn
      p.swapNoncentral
      (by rw [Paw.swapNoncentral_support, hp]) hs
      (by simpa only [Paw.swapNoncentral_leaf] using hthree) hnon' hb'
    simp only [Paw.swapNoncentral_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Paw.swapNoncentral_leaf] at hrow hzero
    exact ⟨hcl, hbound, Or.inr ⟨hrow, hzero⟩⟩

end Erdos577
