import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalPrism
import Mathlib.Tactic.FinCases

/-!
# Coning recursion for the literal formal period products

A positive period edge times an ordered simplex is coned at the first vertex
of that simplex. Its recursive cone chain retains the endpoint translation
and the signed sum of products with all faces.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The degree-zero product is the edge from the original vertex to its
translate by the period vector. -/
theorem formalPeriodProduct_edge_zero (x : Lattice) (w : Fin 1 → Lattice) :
    formalPeriodProduct 0 (formalPeriodEdge x) (formalSimplex w) =
      formalCone (w 0) 1 (formalSimplex (fun _ : Fin 1 => x + w 0)) := by
  simp only [formalPeriodProduct_apply, formalPeriodEdge,
    formalEdgeCrossProduct_zero_simplex_right, formalMap_simplex, formalCone_simplex]
  congr 1
  funext i
  fin_cases i <;> simp [Function.comp_def]

/-- One unfolding of the original coned product, with the two endpoint
insertions written as translation and the original simplex. -/
theorem formalPeriodProduct_edge_succ_boundary (q : ℕ) (x : Lattice)
    (w : Fin (q + 2) → Lattice) :
    formalPeriodProduct (q + 1) (formalPeriodEdge x) (formalSimplex w) =
      formalCone (w 0) (q + 2)
        (formalSimplex (fun i => x + w i) - formalSimplex w -
          formalPeriodProduct q (formalPeriodEdge x)
            (formalBoundary (q + 1) (formalSimplex w))) := by
  simp only [formalPeriodProduct_apply, formalPeriodEdge,
    formalEdgeCrossProduct_simplex_succ, formalMap_cone,
    formalPointCrossProduct_edge_boundary, map_sub, formalMap_simplex,
    Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_def, zero_add]

/-- The explicit signed recursion on the actual ordered formal face chains. -/
theorem formalPeriodProduct_edge_succ (q : ℕ) (x : Lattice)
    (w : Fin (q + 2) → Lattice) :
    formalPeriodProduct (q + 1) (formalPeriodEdge x) (formalSimplex w) =
      formalCone (w 0) (q + 2)
        (formalSimplex (fun i => x + w i) - formalSimplex w -
          ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
            formalPeriodProduct q (formalPeriodEdge x)
              (formalSimplex (w ∘ i.succAbove))) := by
  rw [formalPeriodProduct_edge_succ_boundary, formalBoundary_simplex, map_sum]
  simp only [map_smul]

/-- Every formal period-edge product is a cone at the first vertex of the
right-hand simplex, in every degree including zero. -/
theorem formalPeriodProduct_edge_isCone (q : ℕ) (x : Lattice)
    (w : Fin (q + 1) → Lattice) :
    ∃ c : FormalChains Lattice (q + 1),
      formalPeriodProduct q (formalPeriodEdge x) (formalSimplex w) =
        formalCone (w 0) (q + 1) c := by
  cases q with
  | zero =>
      exact ⟨formalSimplex (fun _ : Fin 1 => x + w 0),
        formalPeriodProduct_edge_zero x w⟩
  | succ q =>
      exact ⟨formalSimplex (fun i => x + w i) - formalSimplex w -
          formalPeriodProduct q (formalPeriodEdge x)
            (formalBoundary (q + 1) (formalSimplex w)),
        formalPeriodProduct_edge_succ_boundary q x w⟩

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
