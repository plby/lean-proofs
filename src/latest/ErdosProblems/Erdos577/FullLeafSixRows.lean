import ErdosProblems.Erdos577.FullLeafSixDiamondExcluded

/-! TeX9.77: every twelve-contact further block satisfies the full six-row alternative. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.six_row_alternative (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (htotal : 12 ≤ contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j) :
    contacts G (s.erase y) j = 0 ∨
      contacts G (FullLeafEquality.matchedSecond p s a y) j = 0 ∨
      (contacts G (FullLeafEquality.matchedSecond p s a y) j = 6 ∧
        ∀ u ∈ s.erase y, degreeIn G u j = 2) := by
  by_cases hlow : ∀ u ∈ s.erase y, degreeIn G u j ≤ 2
  · rcases hm.low_first_rows_alternative hcard hdeg hn hj hjs hja htotal hlow with hz | hmix
    · exact Or.inl hz
    · exact Or.inr (Or.inr hmix)
  · push Not at hlow
    obtain ⟨u, hu, hrow⟩ := hlow
    have hthree : 3 ≤ degreeIn G u j := by omega
    rcases hm.1.high_first_rows_alternative hcard hn hj hjs hja htotal hu hthree with hz | h84
    · exact Or.inr (Or.inl hz)
    · obtain ⟨q, hq⟩ := c.property.blocks_quad j hj
      exact False.elim (hm.1.six_eight_four_false hcard hn
        (hm.matched_second_triangle hcard hdeg hn) q (by rwa [hq]) (by rwa [hq])
        (by rwa [hq]) (by rw [hq]; exact h84.1) (by rw [hq]; exact h84.2) hu (by rwa [hq]))

end Erdos577.FullLeafCore
