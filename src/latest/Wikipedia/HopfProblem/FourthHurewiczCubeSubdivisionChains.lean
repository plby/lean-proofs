import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsAffine
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsAnnihilation
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsFormal
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsRealizationSum
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsShuffle

/-!
# Exact twenty-four-simplex expansion of the original fourth Hurewicz chain

The starting chain is the genuine recursive interval cross product with
the frozen third fundamental cube chain. Currying uses its proven six
tetrahedra without discarding any unnormalized correction. The general
prism comparison then cancels the correction in actual singular chains,
and coordinate insertion identifies the twenty-four native affine cells.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original four-cube chain is the signed realization of the genuine
recursive edge product on the six frozen right-cube tetrahedra. -/
theorem cubeChain_eq_orientedPrismRealization (p : GenLoop (Fin 4) X x) :
    cubeChain p = orientedPrismRealization p.val 4
      (formalEdgeCrossProduct 3 (formalSimplex (fun i : Fin 2 => i))
        (formalSimplex (fun j : Fin 4 => j))) := by
  rw [cubeChain_eq_sum_prisms, orientedPrismRealization_eq_sum]
  simp only [intervalTetrahedronChain_eq_prismCubeRealization,
    ThirdHurewicz.Geometry.cubeOrientation, cubeOrientation]

/-- The chain of every original native based four-cube is exactly the sum
of its twenty-four affine four-simplices with their actual permutation signs. -/
theorem cubeChain_eq_sum_simplices (p : GenLoop (Fin 4) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 4),
      cubeOrientation e • simplexChain X 4 (p.val.comp (cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization,
    orientedPrismRealization_edge_eq_standard (n := 1) p,
    orientedPrismRealization_standardPrism]

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
