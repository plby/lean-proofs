import ErdosProblems.Erdos577.FullLeafHeavyOppositeCounts

/-! Five first-triple contacts prohibit universal second rows.
Eleven second-side contacts select a row of degree three. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.second_not_universal {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hfive : 5 ≤ contacts G (s.erase y) j) {u : V} (hu : u ∈ insert (p.vertices 3) a) :
    ¬(∀ v ∈ j, QuadOn G (insert u (j.erase v))) := by
  intro hall
  have hcol (v : V) (hv : v ∈ j) : degreeIn G v (s.erase y) ≤ 1 :=
    h.triple_degree_of_second_replacement hcard hn hu hj hjs hja hv (hall v hv)
  have hfour : contacts G (s.erase y) j ≤ 4 := by
    rw [contacts_comm]
    calc
      contacts G j (s.erase y) ≤ ∑ _ ∈ j, (1 : ℕ) := sum_le_sum hcol
      _ = 4 := by simp only [sum_const, smul_eq_mul, mul_one, (c.property.blocks_quad j hj).card]
  omega

theorem Configuration.second_rows_le_three {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hfive : 5 ≤ contacts G (s.erase y) j) {u : V} (hu : u ∈ insert (p.vertices 3) a) :
    degreeIn G u j ≤ 3 := by
  have hquad := c.property.blocks_quad j hj
  have hout : u ∉ j := fun hh ↦ disjoint_left.mp (h.core_disjoint_block hj hja)
    (h.second_five_subset hu) hh
  by_contra hlarge
  have hbound := degreeIn_le_card G u j
  have hfour : degreeIn G u j = 4 := by rw [hquad.card] at hbound; omega
  exact h.second_not_universal hcard hn hj hjs hja hfive hu
    (fun _ hv ↦ hquad.replace_of_degree_four hout hfour hv)

theorem Configuration.exists_second_three {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hfive : 5 ≤ contacts G (s.erase y) j)
    (heleven : 11 ≤ contacts G (insert (p.vertices 3) a) j) :
    ∃ u ∈ insert (p.vertices 3) a, degreeIn G u j = 3 := by
  by_contra! hnot
  have htwo (u : V) (hu : u ∈ insert (p.vertices 3) a) : degreeIn G u j ≤ 2 := by
    have hb := h.second_rows_le_three hcard hn hj hjs hja hfive hu
    have hh := hnot u hu
    omega
  have hten : contacts G (insert (p.vertices 3) a) j ≤ 10 := by
    calc
      contacts G (insert (p.vertices 3) a) j ≤ ∑ _ ∈ insert (p.vertices 3) a, (2 : ℕ) :=
        sum_le_sum htwo
      _ = 10 := by simp only [sum_const, smul_eq_mul, h.second_five_card]
  omega

end Erdos577.FullLeafCore
