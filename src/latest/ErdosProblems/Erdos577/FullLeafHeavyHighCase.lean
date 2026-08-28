import ErdosProblems.Erdos577.FullLeafHeavyRemovable

/-! The high first-row branch of TeX9.72 gives the second-side matching type. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.high_first_matching (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    {x : V} (hx : x ∈ insert p.leaf s) (hrow : 3 ≤ degreeIn G x j) :
    (∀ u ∈ insert (p.vertices 3) a, degreeIn G u j ≤ 1) ∧
      (∀ v ∈ j, degreeIn G v (insert (p.vertices 3) a) ≤ 1) := by
  obtain ⟨hcol, _, _, hcl, hnine⟩ := h.high_first_preparation hcard hn hj hjs hja hheavy hx hrow
  refine ⟨?_, fun v hv ↦ (degreeIn_mono G v h.second_five_subset).trans (hcol v hv)⟩
  intro u hu
  have hout : u ∉ j := fun hh ↦ disjoint_left.mp (h.core_disjoint_block hj hja)
    (h.second_five_subset hu) hh
  by_contra htwo
  obtain ⟨v, hv, w, hw, hvw, hr, hr'⟩ := FullLeafHeavy.two_clique_replacements hcl hout (by omega)
  have hvone := h.triple_degree_of_second_replacement hcard hn hu hj hjs hja hv hr
  have hwone := h.triple_degree_of_second_replacement hcard hn hu hj hjs hja hw hr'
  have he := FullLeafHeavy.two_low_columns_le_eight h.first_triple_clique.card_eq hcl.card_eq
    hv hw hvw hvone hwone
  omega

end Erdos577.FullLeafCore
