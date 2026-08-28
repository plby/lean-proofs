import ErdosProblems.Erdos577.JointThreeOldGain

/-! Reflection excludes the second old-terminal pair and forces the exact four degrees. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma reflect_six_row (v : Quadrilateral G) (u : V)
    (hrow : ∀ i : Fin 4, G.Adj u (v i) ↔ (6 : ℕ).testBit i.val = true) :
    ∀ i : Fin 4, G.Adj u ((v.rotate 2).reverse i) ↔ (3 : ℕ).testBit i.val = true := by
  intro i
  fin_cases i
  · exact hrow 2
  · exact hrow 1
  · exact hrow 0
  · exact hrow 3

theorem FinalRows.three_old_degree {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3) :
    degreeIn G x v.support = 1 := by
  have hnot : degreeIn G x v.support ≠ 2 := by
    intro htwo
    rcases h.three_leaf_rows hz x (Or.inl rfl) htwo with hrow | hrow
    · exact h.three_old_first_false hz hrow
    · exact h.reflect_highs.three_old_first_false
        (by simpa only [Quadrilateral.reverse_support, Quadrilateral.rotate_support] using hz)
        (reflect_six_row v x hrow)
  have hx := h.x_bound
  have hp := h.x_pos
  omega

theorem FinalRows.three_exact_degrees {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (hw : degreeIn G w v.support ≤ 3) :
    degreeIn G x v.support = 1 ∧ degreeIn G y v.support = 2 ∧
      degreeIn G w v.support = 3 ∧
      degreeIn G x v.support + degreeIn G y v.support +
        degreeIn G z v.support + degreeIn G w v.support = 9 := by
  have hx := h.three_old_degree hz
  have hy := h.y_bound
  have hn := h.nine
  omega

end Erdos577.JointFinal
