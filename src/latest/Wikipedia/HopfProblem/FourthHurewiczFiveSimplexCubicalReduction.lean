import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhisker
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexEvaluatorUncurry
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexEvaluatorPaths
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexAlternating

/-!
# The genuine cubical boundary relation lowers dimension

The whiskered cell has all the original remaining facets, except that
its final upper facet contains the two cyclically ordered closing paths.
Their contribution is exactly the missing pair of first-coordinate
facets.  This proves a literal identity of evaluated boundary values.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
variable {A : Type*} [AddCommGroup A]

theorem whiskeredCell_lower_value (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1)) :
    E.uncurry (cubicalLowerFace (whiskeredCell F) i) = E (cubicalLowerFace F i.succ) := by
  rw [CubicalEvaluator.uncurry_apply,
    whiskeredCell_face_normal F i 0 (Or.inl rfl) (Or.inr rfl)]
  exact E.map_constantClosingPaths _

theorem whiskeredCell_upper_value (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) (i : Fin n) :
    E.uncurry (cubicalUpperFace (whiskeredCell F) i.castSucc) =
      E (cubicalUpperFace F i.castSucc.succ) := by
  rw [CubicalEvaluator.uncurry_apply,
    whiskeredCell_face_normal F i.castSucc 1 (Or.inr rfl)
      (Or.inl (Fin.castSucc_ne_last i))]
  exact E.map_constantClosingPaths _

theorem whiskeredCell_last_upper_value (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) :
    E.uncurry (cubicalUpperFace (whiskeredCell F) (Fin.last n)) =
      E (cubicalUpperFace F (Fin.last (n + 1))) - (-1 : ℤ) ^ n •
        (E (cubicalUpperFace F 0) - E (cubicalLowerFace F 0)) := by
  rw [CubicalEvaluator.uncurry_apply, whiskeredCell_face_last_upper]
  exact E.map_cyclicClosingPaths _ _ _

/-- The entire boundary value is the negative boundary value in the loop space. -/
theorem cubicalBoundaryValue_dimension_reduction (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) :
    cubicalBoundaryValue E F = -cubicalBoundaryValue E.uncurry (whiskeredCell F) := by
  unfold cubicalBoundaryValue
  apply alternatingSum_dimension_reduction n
  · intro i
    rw [whiskeredCell_upper_value, whiskeredCell_lower_value]
  · rw [whiskeredCell_last_upper_value, whiskeredCell_lower_value, Fin.succ_last]
    abel

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
