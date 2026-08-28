import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormal
import Wikipedia.HopfProblem.Lattice

/-!
# Integral-vertex chains for the period-torus cup calculation

These are the existing ordered formal chains and the existing coned
edge cross product, followed by literal addition of the period vertices.
The evaluation functions are the Alexander--Whitney front/back formulas.
The comparison with genuine singular cochains is a separate construction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The oriented period edge from the origin to the given integral column. -/
def formalPeriodEdge (x : Lattice) : FormalChains Lattice 2 :=
  formalSimplex ![0, x]

/-- The actual formal edge product followed by addition of the period vertices. -/
def formalPeriodProduct (q : ℕ) :
    FormalChains Lattice 2 →ₗ[ℤ] FormalChains Lattice (q + 1) →ₗ[ℤ]
      FormalChains Lattice (q + 2) :=
  (formalEdgeCrossProduct q).compr₂
    (formalMap (fun p : Lattice × Lattice => p.1 + p.2) (q + 2))

@[simp] theorem formalPeriodProduct_apply (q : ℕ)
    (c : FormalChains Lattice 2) (d : FormalChains Lattice (q + 1)) :
    formalPeriodProduct q c d =
      formalMap (fun p : Lattice × Lattice => p.1 + p.2) (q + 2)
        (formalEdgeCrossProduct q c d) := rfl

/-- The positive ordered fourfold product of the four original period columns. -/
def formalPositiveTop : FormalChains Lattice 5 :=
  formalPeriodProduct 3 (formalPeriodEdge (Pi.single 0 1))
    (formalPeriodProduct 2 (formalPeriodEdge (Pi.single 1 1))
      (formalPeriodProduct 1 (formalPeriodEdge (Pi.single 2 1))
        (formalPeriodEdge (Pi.single 3 1))))

/-- The front/back edge formula for the distinguished two-cochain. -/
def etaTriangle (v : Fin 3 → Lattice) : ℤ :=
  (v 1 1 - v 0 1) * (v 2 2 - v 1 2) +
    6 * (v 1 0 - v 0 0) * (v 2 3 - v 1 3)

def formalEtaEvaluation : FormalChains Lattice 3 →ₗ[ℤ] ℤ :=
  formalLift etaTriangle

@[simp] theorem formalEtaEvaluation_simplex (v : Fin 3 → Lattice) :
    formalEtaEvaluation (formalSimplex v) = etaTriangle v :=
  formalLift_simplex _ _

/-- The literal Alexander--Whitney two-by-two product on five vertices. -/
def etaSquareSimplex (v : Fin 5 → Lattice) : ℤ :=
  etaTriangle ![v 0, v 1, v 2] * etaTriangle ![v 2, v 3, v 4]

def formalEtaSquareEvaluation : FormalChains Lattice 5 →ₗ[ℤ] ℤ :=
  formalLift etaSquareSimplex

@[simp] theorem formalEtaSquareEvaluation_simplex (v : Fin 5 → Lattice) :
    formalEtaSquareEvaluation (formalSimplex v) = etaSquareSimplex v :=
  formalLift_simplex _ _

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
