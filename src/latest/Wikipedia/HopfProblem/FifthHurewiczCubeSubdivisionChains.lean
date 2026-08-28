import Wikipedia.HopfProblem.FifthHurewiczCubeSubdivisionChainsAffine

/-!
# Exact 120-simplex expansion of the original fifth Hurewicz chain

The chain starts with the genuine recursive interval cross product and
the frozen fourth fundamental cube chain. Actual currying gives its
twenty-four prisms; the proved general prism correction and coordinate
insertion then identify the signed native five-simplex sum.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision
  (orientedPrismRealization orientedPrismRealization_eq_sum
    orientedPrismRealization_edge_eq_standard orientedPrismRealization_standardPrism)

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original five-cube chain is the signed affine realization of the
actual recursive edge product on its twenty-four right-cube simplices. -/
theorem cubeChain_eq_orientedPrismRealization (p : GenLoop (Fin 5) X x) :
    cubeChain p = orientedPrismRealization p.val 5
      (formalEdgeCrossProduct 4 (formalSimplex (fun i : Fin 2 => i))
        (formalSimplex (fun j : Fin 5 => j))) := by
  rw [cubeChain_eq_sum_prisms, orientedPrismRealization_eq_sum]
  simp only [intervalFourSimplexChain_eq_prismCubeRealization]

/-- Every original native based five-cube chain is exactly the sum of its
120 affine five-simplices with their permutation orientations. -/
theorem cubeChain_eq_sum_simplices (p : GenLoop (Fin 5) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 5),
      cubeOrientation e • simplexChain X 5 (p.val.comp (cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization,
    orientedPrismRealization_edge_eq_standard (n := 2) p,
    orientedPrismRealization_standardPrism]

end Wikipedia.HopfProblem.FifthHurewicz.CubeSubdivision
