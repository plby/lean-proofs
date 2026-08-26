import ErdosProblems.Erdos633b.CaseSevenRationality
import ErdosProblems.Erdos633b.LocalAngleTypes
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! Case-(7) necessity for an incommensurable outer triangle, with arbitrary
initial orderings of both triangles and no rational-side assumption. -/

namespace Erdos633b.Tiling

theorem caseSeven_necessary_of_outer_incommensurable {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : EightCases T := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  exact d.caseSeven_necessary hn (d.groupOne_first_angle_irrational hrel hirr) h0 h1 h2

theorem caseSeven_necessary_of_reindex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (e f : Equiv.Perm (Fin 3))
    (h0 : Triangle.angle (T.reindex f) 0 = 2 * Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 = Triangle.angle (d.tile.reindex e) 1)
    (h2 : Triangle.angle (T.reindex f) 2 =
      Triangle.angle (d.tile.reindex e) 0 + Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  have hirrU : ¬ ∀ i, IsRational (U.angle i / Real.pi) := by
    intro h
    apply hirr
    intro i
    have hh := h (f i)
    simpa only [U, Triangle.angle_reindex, Equiv.symm_apply_apply] using hh
  apply eightCases_of_reindex T f
  exact d'.caseSeven_necessary_of_outer_incommensurable hn hirrU h0 h1 h2

end Erdos633b.Tiling
