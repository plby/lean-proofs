import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubicalBasic
import Mathlib.Tactic.Abel

/-!
# Evaluating the actual three-part closing paths

Constant closing paths contribute zero.  On the final upper facet the
two closing paths are the original endpoint cubes with a cyclic input
permutation, and therefore contribute the usual alternating sign.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

open NativeSubdivision

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
variable {A : Type*} [AddCommGroup A]

theorem CubicalEvaluator.map_constantClosingPaths (E : CubicalEvaluator (n + 1) x A)
    (p : GenLoop (Fin (n + 1)) X x) :
    E (GenLoop.transAt 0 GenLoop.const (GenLoop.transAt 0 p GenLoop.const)) = E p := by
  rw [E.map_transAt, E.map_transAt, E.map_const, zero_add, add_zero]

theorem CubicalEvaluator.map_cyclicClosingPaths (E : CubicalEvaluator (n + 1) x A)
    (l p r : GenLoop (Fin (n + 1)) X x) :
    E (GenLoop.transAt 0 (permuteCubeLoop l (finRotate (n + 1)))
      (GenLoop.transAt 0 p
        (GenLoop.symmAt 0 (permuteCubeLoop r (finRotate (n + 1)))))) =
      E p - (-1 : ℤ) ^ n • (E r - E l) := by
  rw [E.map_transAt, E.map_transAt, E.map_symmAt,
    E.map_finRotate, E.map_finRotate]
  simp only [Nat.add_sub_cancel, smul_sub]
  abel

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
