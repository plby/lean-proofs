import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubicalBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexUncurry

/-!
# Inducing a cubical evaluator on the actual loop space

The inner loop coordinate is prepended, without changing any map to the
original space.  Literal uncurrying commutes with native concatenation,
reversal, coordinate swaps, and relative homotopies, so every evaluator
law is inherited.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
variable {A : Type*} [AddCommGroup A]

/-- Evaluation of loop-space cubes by their literal uncurried native cubes. -/
def CubicalEvaluator.uncurry (E : CubicalEvaluator (n + 1) x A) :
    CubicalEvaluator n (GenLoop.const : GenLoop (Fin 1) X x) A where
  evaluate p := E (uncurryLoop p)
  map_const := by rw [uncurryLoop_const]; exact E.map_const
  map_homotopic h := E.map_homotopic (uncurryLoop_homotopic h)
  map_transAt i p q := by
    rw [uncurryLoop_transAt]
    exact E.map_transAt i.succ _ _
  map_symmAt i p := by
    rw [uncurryLoop_symmAt]
    exact E.map_symmAt i.succ _
  map_swap p i j hij := by
    rw [uncurryLoop_swap]
    exact E.map_swap _ i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))

@[simp] theorem CubicalEvaluator.uncurry_apply (E : CubicalEvaluator (n + 1) x A)
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    E.uncurry p = E (uncurryLoop p) := rfl

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
