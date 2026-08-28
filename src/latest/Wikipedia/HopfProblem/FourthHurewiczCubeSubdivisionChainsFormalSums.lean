import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsFormalComparison

/-!
# Shared-first-vertex sums of the original prism chains

These formulas collect the signed sum under one common cone. In the
comparison formula the full right boundary is kept as a single chain,
allowing shared faces to cancel before any product is expanded.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open SingularMayerVietoris PeriodTorusHigherHomology
open scoped BigOperators

variable {V W ι : Type*}

/-- The standard shuffle recursion commutes with sums sharing the first right vertex. -/
theorem standardPrism_sum_common_first (q : ℕ) (s : Finset ι) (c : ι → ℤ)
    (v : Fin 2 → V) (w : ι → Fin (q + 2) → W) (a : W)
    (hfirst : ∀ j ∈ s, w j 0 = a) :
    (∑ j ∈ s, c j • standardPrism (q + 1) v (w j)) =
      formalCone (v 0, a) (q + 2)
        (formalMap (fun z => (v 1, z)) (q + 2) (∑ j ∈ s, c j • formalSimplex (w j)) -
          ∑ j ∈ s, c j • standardPrism q v (Fin.tail (w j))) := by
  calc
    _ = ∑ j ∈ s, c j • formalCone (v 0, a) (q + 2)
        (formalMap (fun z => (v 1, z)) (q + 2) (formalSimplex (w j)) -
          standardPrism q v (Fin.tail (w j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [standardPrism_succ, hfirst j hj]
    _ = _ := by
      simp only [map_sum, map_smul, map_sub, smul_sub, Finset.sum_sub_distrib]

/-- The exact original-minus-shuffle comparison for a common-vertex signed sum. -/
theorem formalEdgeCrossProduct_sub_standardPrism_sum_common_first
    (q : ℕ) (s : Finset ι) (c : ι → ℤ) (v : Fin 2 → V)
    (w : ι → Fin (q + 2) → W) (a : W) (hfirst : ∀ j ∈ s, w j 0 = a) :
    formalEdgeCrossProduct (q + 1) (formalSimplex v)
        (∑ j ∈ s, c j • formalSimplex (w j)) -
      (∑ j ∈ s, c j • standardPrism (q + 1) v (w j)) =
      formalCone (v 0, a) (q + 2)
        (-formalMap (fun z => (v 0, z)) (q + 2) (∑ j ∈ s, c j • formalSimplex (w j)) -
          formalEdgeCrossProduct q (formalSimplex v)
            (formalBoundary (q + 1) (∑ j ∈ s, c j • formalSimplex (w j))) +
          ∑ j ∈ s, c j • standardPrism q v (Fin.tail (w j))) := by
  rw [formalEdgeCrossProduct_sum_common_first q s c v w a hfirst,
    standardPrism_sum_common_first q s c v w a hfirst]
  simp only [map_sub, map_add, map_neg]
  abel

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
