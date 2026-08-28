import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsFormalBoundary
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsFormalPrism
import Mathlib.Tactic.Abel

/-!
# Comparing the frozen cone product with the literal shuffle prism

The discrepancy is an actual formal chain. Its cone recursion separates
the source face, the discrepancy of the first face, and the other signed
faces. The canonical-index version exposes exactly the terms needed for
support and shared-face cancellation, without expanding higher products.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open SingularMayerVietoris PeriodTorusHigherHomology
open scoped BigOperators

variable {V W V' W' : Type*}

/-- The difference of the original cone product and the literal shuffle prism. -/
def prismDiscrepancy (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    FormalChains (V × W) (q + 2) :=
  formalEdgeCrossProduct q (formalSimplex v) (formalSimplex w) - standardPrism q v w

@[simp] theorem prismDiscrepancy_zero (v : Fin 2 → V) (w : Fin 1 → W) :
    prismDiscrepancy 0 v w = 0 := by
  simp only [prismDiscrepancy, formalEdgeCrossProduct_zero_simplex_right,
    formalMap_simplex, standardPrism_zero, Function.comp_def, sub_self]

/-- The discrepancy is natural for arbitrary maps of the two vertex sets. -/
theorem formalMap_prismDiscrepancy (f : V → V') (g : W → W') (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    formalMap (Prod.map f g) (q + 2) (prismDiscrepancy q v w) =
      prismDiscrepancy q (f ∘ v) (g ∘ w) := by
  simp only [prismDiscrepancy, map_sub, formalMap_edgeCrossProduct,
    formalMap_standardPrism, formalMap_simplex]

/-- The same discrepancy on the literal universal sets of vertex indices. -/
def canonicalPrismDiscrepancy (q : ℕ) :
    FormalChains (Fin 2 × Fin (q + 1)) (q + 2) :=
  prismDiscrepancy q (fun i => i) (fun j => j)

@[simp] theorem canonicalPrismDiscrepancy_zero : canonicalPrismDiscrepancy 0 = 0 :=
  prismDiscrepancy_zero _ _

/-- Every discrepancy is the image of the canonical indexed discrepancy. -/
theorem prismDiscrepancy_eq_map_canonical (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    prismDiscrepancy q v w =
      formalMap (Prod.map v w) (q + 2) (canonicalPrismDiscrepancy q) := by
  simpa only [canonicalPrismDiscrepancy, Function.comp_def] using
    (formalMap_prismDiscrepancy v w q (fun i => i) (fun j => j)).symm

/-- The direct comparison keeps the complete original right boundary intact. -/
theorem prismDiscrepancy_succ (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      formalCone (v 0, w 0) (q + 2)
        (-formalMap (fun z => (v 0, z)) (q + 2) (formalSimplex w) -
          formalEdgeCrossProduct q (formalSimplex v)
            (formalBoundary (q + 1) (formalSimplex w)) +
          standardPrism q v (Fin.tail w)) := by
  rw [prismDiscrepancy, formalEdgeCrossProduct_simplex_succ,
    formalPointCrossProduct_edge_boundary, standardPrism_succ]
  simp only [map_sub, map_add, map_neg]
  abel

/-- Separating the first face leaves only faces that retain the original first vertex. -/
theorem prismDiscrepancy_succ_retained (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      formalCone (v 0, w 0) (q + 2)
        (-formalMap (fun z => (v 0, z)) (q + 2) (formalSimplex w) -
          prismDiscrepancy q v (Fin.tail w) -
          formalEdgeCrossProduct q (formalSimplex v)
            (retainedFirstBoundary q (formalSimplex w))) := by
  rw [prismDiscrepancy_succ, formalBoundary_firstFace_split_simplex,
    map_add, prismDiscrepancy]
  simp only [map_sub, map_add, map_neg]
  abel

/-- In universal indices, the recursive discrepancy either stays on the source
side or comes from a right face omitting a noninitial vertex. -/
theorem canonicalPrismDiscrepancy_succ (q : ℕ) :
    canonicalPrismDiscrepancy (q + 1) =
      formalCone ((0 : Fin 2), (0 : Fin (q + 2))) (q + 2)
        (-formalSimplex (fun j : Fin (q + 2) => ((0 : Fin 2), j)) -
          formalMap (Prod.map (fun i : Fin 2 => i) Fin.succ) (q + 2)
            (canonicalPrismDiscrepancy q) -
          ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i.val + 1) •
            formalEdgeCrossProduct q (formalSimplex (fun j : Fin 2 => j))
              (formalSimplex i.succ.succAbove)) := by
  change prismDiscrepancy (q + 1) (fun i : Fin 2 => i)
    (fun j : Fin (q + 2) => j) = _
  rw [prismDiscrepancy_succ_retained, prismDiscrepancy_eq_map_canonical]
  simp only [retainedFirstBoundary_simplex, map_sum, map_smul, formalMap_simplex,
    Function.comp_def]
  rfl

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
