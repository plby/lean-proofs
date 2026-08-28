import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalBasic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Evaluation on the literal formal period products

The calculations use the existing coned edge cross product, not a
replacement exterior algebra. The positive period-product convention is
kept explicit and is not identified here with complex orientation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open SingularMayerVietoris PeriodTorusHigherHomology

private theorem cons_three_last {V : Type*} (a : V) (v : Fin 2 → V) :
    Fin.cons (α := fun _ => V) a v (2 : Fin 3) = v 1 := rfl

/-- Evaluation on two original positive period edges is the distinguished
alternating integer form. -/
theorem formalEtaEvaluation_periodProduct (x y : Lattice) :
    formalEtaEvaluation (formalPeriodProduct 1 (formalPeriodEdge x) (formalPeriodEdge y)) =
      x 1 * y 2 - x 2 * y 1 + 6 * (x 0 * y 3 - x 3 * y 0) := by
  simp only [formalPeriodProduct_apply, formalPeriodEdge,
    formalEdgeCrossProduct_simplex_succ, formalBoundary_simplex]
  simp [etaTriangle, Function.comp_def, cons_three_last]
  ring

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
