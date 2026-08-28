import ErdosProblems.Erdos577.FullLeafSixHighRows

/-! At eight first contacts, an opposite second row forces both high columns and a diagonal. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.six_opposite_columns (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (height : contacts G (s.erase y) q.support = 8)
    {v : V} (hv : v ∈ FullLeafEquality.matchedSecond p s a y)
    (h0 : G.Adj v (q 0)) (h2 : G.Adj v (q 2)) :
    degreeIn G (q 0) (s.erase y) = 3 ∧ degreeIn G (q 1) (s.erase y) = 1 ∧
      degreeIn G (q 2) (s.erase y) = 3 ∧ degreeIn G (q 3) (s.erase y) = 1 ∧
      G.Adj (q 1) (q 3) := by
  have hout : v ∉ q.support := fun hh ↦
    disjoint_left.mp (h.matched_second_disjoint_block hj hja) hv hh
  have hlow (i : Fin 4) (hi : i = 1 ∨ i = 3) : degreeIn G (q i) (s.erase y) ≤ 1 :=
    h.triple_degree_of_second_replacement hcard hn (mem_filter.mp hv).1 hj hjs hja
      ((q.mem_support _).mpr ⟨i, rfl⟩) (JointFinal.opposite_replace q v hout h0 h2 i hi)
  have hlo1 := hlow 1 (Or.inl rfl)
  have hlo3 := hlow 3 (Or.inr rfl)
  have hhi0 := (degreeIn_le_card G (q 0) (s.erase y)).trans_eq h.first_triple_clique.card_eq
  have hhi2 := (degreeIn_le_card G (q 2) (s.erase y)).trans_eq h.first_triple_clique.card_eq
  have hsum := FullLeafHeavy.columns_sum q (s.erase y)
  have he0 : degreeIn G (q 0) (s.erase y) = 3 := by omega
  have he1 : degreeIn G (q 1) (s.erase y) = 1 := by omega
  have he2 : degreeIn G (q 2) (s.erase y) = 3 := by omega
  have he3 : degreeIn G (q 3) (s.erase y) = 1 := by omega
  have hfull0 := (degreeIn_eq_card_iff (q 0) (s.erase y)).mp
    (he0.trans h.first_triple_clique.card_eq.symm)
  have hfull2 := (degreeIn_eq_card_iff (q 2) (s.erase y)).mp
    (he2.trans h.first_triple_clique.card_eq.symm)
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < degreeIn G (q 1) (s.erase y) by omega)
  obtain ⟨hx, h1x⟩ := mem_filter.mp hx
  refine ⟨he0, he1, he2, he3, h.first_last_diagonal q hj hjs
    (mem_insert_of_mem (mem_erase.mp hx).2) ?_⟩
  intro i hi
  fin_cases i
  · exact (hfull0 x hx).symm
  · exact h1x.symm
  · exact (hfull2 x hx).symm
  · exact False.elim (hi rfl)

theorem Configuration.six_opposite_no_lows (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (height : contacts G (s.erase y) q.support = 8)
    {v : V} (hv : v ∈ FullLeafEquality.matchedSecond p s a y)
    (h0 : G.Adj v (q 0)) (h2 : G.Adj v (q 2)) :
    ¬G.Adj v (q 1) ∧ ¬G.Adj v (q 3) := by
  obtain ⟨hcol, _, _, _, hdiag⟩ := h.six_opposite_columns hcard hn q hj hjs hja height hv h0 h2
  have hout : v ∉ q.support := fun hh ↦
    disjoint_left.mp (h.matched_second_disjoint_block hj hja) hv hh
  have hno : ¬QuadOn G (insert v (q.support.erase (q 0))) :=
    h.second_no_replacement hcard hn (mem_filter.mp hv).1 hj hjs hja
      ((q.mem_support _).mpr ⟨0, rfl⟩) (by omega)
  constructor
  · intro h1
    exact hno (q.replace_using_path v hout 0 1 3 2 (by decide) (by decide)
      h1 hdiag (q.adjacent 2).symm h2)
  · intro h3
    exact hno (q.replace_using_path v hout 0 2 1 3 (by decide) (by decide)
      h2 (q.adjacent 1).symm hdiag h3)

end Erdos577.FullLeafCore
