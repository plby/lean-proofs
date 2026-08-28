import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsBadSupportBasic
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsFormalComparison

/-!
# Universal support bound for the original prism discrepancy

The cone recursion puts the discrepancy in the bad-prism submodule in every
right degree. The proof is inductive: the bottom face has initial left
coordinate, tail discrepancies preserve their support under the successor
map, and every remaining right face omits a noninitial right vertex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open SingularMayerVietoris PeriodTorusHigherHomology
open scoped BigOperators

/-- The original edge product differs from the shuffle prism only by chains
in the initial-endpoint and noninitial-vertex-omission submodules. -/
theorem canonicalPrismDiscrepancy_mem_badPrism (q : ℕ) :
    canonicalPrismDiscrepancy q ∈ badPrism q (q + 2) := by
  induction q with
  | zero =>
      rw [canonicalPrismDiscrepancy_zero]
      exact Submodule.zero_mem _
  | succ q ih =>
      rw [canonicalPrismDiscrepancy_succ]
      apply formalCone_mem_badPrism
      apply Submodule.sub_mem
      · apply Submodule.sub_mem
        · apply Submodule.neg_mem
          exact mem_badPrism_of_left_zero (formalSimplex_mem_supported fun _ => rfl)
        · exact formalMap_succ_mem_badPrism ih
      · apply Submodule.sum_mem
        intro i hi
        apply Submodule.smul_mem
        exact formalEdgeCrossProduct_mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i) _
          (formalSimplex_mem_supported fun j => Fin.succAbove_ne i.succ j)

/-- Arbitrary vertex-labelled discrepancies are images of universally
boundary-supported chains. -/
theorem prismDiscrepancy_mem_map_badPrism {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    prismDiscrepancy q v w ∈
      (badPrism q (q + 2)).map (formalMap (Prod.map v w) (q + 2)) := by
  exact Submodule.mem_map.mpr ⟨canonicalPrismDiscrepancy q,
    canonicalPrismDiscrepancy_mem_badPrism q, (prismDiscrepancy_eq_map_canonical q v w).symm⟩

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
