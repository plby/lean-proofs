import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsShuffleGeometry
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsPermutations

/-!
# The signed standard prism realizes the full native cube-cell sum

After the literal shuffle-simplex identification, insertion reindexes
the actual finite sum over all coordinate permutations in one higher
dimension. No normalization or quotient of singular chains is used.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris HigherHurewicz.CubeTriangulation

/-- The actual signed prism realization is the full permutation-simplex chain. -/
theorem orientedPrismRealization_standardPrism {X : Type} [TopologicalSpace X]
    {n : ℕ} (p : C(CubeN (n + 1), X)) :
    orientedPrismRealization p (n + 1)
      (standardPrism n (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j)) =
        ∑ perm : Equiv.Perm (Fin (n + 1)),
          cubeOrientation perm • simplexChain X (n + 1) (p.comp (cubeSimplex perm)) := by
  simp only [standardPrism, map_sum, map_zsmul, orientedPrismRealization_simplex,
    prismCubeSimplex_shuffle, ← Finset.sum_zsmul, cubeOrientation]
  exact PermutationInsertion.sum_sign_smul_insert
    (fun perm => simplexChain X (n + 1) (p.comp (cubeSimplex perm)))

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
