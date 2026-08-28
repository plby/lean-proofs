import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsRealization
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsFormalPrism
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsPermutationsBasic
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsShuffleArithmetic

/-!
# Each actual shuffle prism is the inserted cube simplex

The universal shuffle vertex sequence, realized in the interval-first
native cube, is literally the vertex sequence of its inserted permutation.
Barycentric interpolation therefore gives equality of continuous simplices.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris HigherHurewicz.CubeTriangulation

/-- The actual vertices agree at every position and every cube coordinate. -/
theorem prismCubeVertex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) (r : Fin (n + 2)) :
    prismCubeVertex e (shufflePrismVertices (fun i : Fin 2 => i)
      (fun j : Fin (n + 1) => j) k r) =
        cubeVertex (PermutationInsertion.insert k e) r := by
  funext coord
  refine Fin.cases ?_ (fun j => ?_) coord
  · by_cases h : r ≤ k.castSucc
    · have h' : ¬ k.val < r.val := by
        simpa only [Fin.le_def, Fin.val_castSucc, not_lt] using h
      simp [shufflePrismVertices, h, cubeVertex, h', stdVertices]
    · have h' : k.val < r.val := by
        simpa only [Fin.le_def, Fin.val_castSucc, not_le] using h
      simp [shufflePrismVertices, h, cubeVertex, h', stdVertices]
  · simp only [shufflePrismVertices, prismCubeVertex_succ, cubeVertex,
      PermutationInsertion.insert_symm_apply_succ]
    simp only [lt_predAbove_iff_succAbove_lt]

/-- Every shuffle prism is the original cube simplex with the new coordinate inserted. -/
theorem prismCubeSimplex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    prismCubeSimplex e (shufflePrismVertices (fun i : Fin 2 => i)
      (fun j : Fin (n + 1) => j) k) =
        cubeSimplex (PermutationInsertion.insert k e) := by
  apply congrArg cubeAffineSimplex
  funext r
  exact prismCubeVertex_shuffle e k r

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
