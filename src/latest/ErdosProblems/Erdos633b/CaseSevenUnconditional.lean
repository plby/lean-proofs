import ErdosProblems.Erdos633b.GroupOneConjugateExclusion
import ErdosProblems.Erdos633b.CaseSevenRationality
import ErdosProblems.Erdos633b.LocalAngleTypes
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! The second group-1 necessity branch with its irrationality premise
discharged by the negative-cosine conjugate obstruction. -/

namespace Erdos633b.Tiling

theorem groupOne_second_first_angle_irrational {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    Irrational (d.tile.angle 0 / Real.pi) := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have hh := T.angle_sum
    rw [h0, h1, h2] at hh
    linarith
  exact d.tile.irrational_first_of_angle_relation 3 2 (by decide) hrel
    (d.groupOne_second_tile_incommensurable h0 h1 h2)

theorem caseSeven_necessary_unconditional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : EightCases T :=
  d.caseSeven_necessary hn (d.groupOne_second_first_angle_irrational h0 h1 h2) h0 h1 h2

theorem caseSeven_necessary_unconditional_reindex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (e f : Equiv.Perm (Fin 3))
    (h0 : Triangle.angle (T.reindex f) 0 = 2 * Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 =
      Triangle.angle (d.tile.reindex e) 1)
    (h2 : Triangle.angle (T.reindex f) 2 =
      Triangle.angle (d.tile.reindex e) 0 + Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  apply eightCases_of_reindex T f
  exact d'.caseSeven_necessary_unconditional hn h0 h1 h2

end Erdos633b.Tiling
