import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalBasic
import Mathlib.Tactic.Ring

/-!
# Coordinate-pair evaluation on the literal formal period products

The front/back edge formula for two coordinate one-cochains evaluates on
the original positive period-edge product as the corresponding alternating
coordinate pairing. The computation uses the existing coned cross product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The front/back edge evaluation for the ordered pair of coordinates. -/
def pairTriangle (i j : Fin 4) (v : Fin 3 → Lattice) : ℤ :=
  (v 1 i - v 0 i) * (v 2 j - v 1 j)

/-- Linear extension of the literal coordinate-pair simplex evaluation. -/
def formalPairEvaluation (i j : Fin 4) : FormalChains Lattice 3 →ₗ[ℤ] ℤ :=
  formalLift (pairTriangle i j)

@[simp] theorem formalPairEvaluation_simplex (i j : Fin 4) (v : Fin 3 → Lattice) :
    formalPairEvaluation i j (formalSimplex v) = pairTriangle i j v :=
  formalLift_simplex _ _

private theorem pair_cons_three_last {V : Type*} (a : V) (v : Fin 2 → V) :
    Fin.cons (α := fun _ => V) a v (2 : Fin 3) = v 1 := rfl

/-- The coordinate cup-pair formula on two positive period edges, with the
order and signs fixed by the actual formal cross-product convention. -/
theorem formalPairEvaluation_periodProduct (i j : Fin 4) (x y : Lattice) :
    formalPairEvaluation i j
        (formalPeriodProduct 1 (formalPeriodEdge x) (formalPeriodEdge y)) =
      x i * y j - x j * y i := by
  simp only [formalPeriodProduct_apply, formalPeriodEdge,
    formalEdgeCrossProduct_simplex_succ, formalBoundary_simplex]
  simp [pairTriangle, Function.comp_def, pair_cons_three_last]
  ring

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
