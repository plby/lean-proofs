import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivisionChainsAffine

/-!
# Exact 5040-simplex expansion of the original seventh Hurewicz chain

The chain starts with the genuine recursive interval cross product and
the frozen sixth fundamental cube chain. Actual currying gives its
720 prisms; the proved general prism correction and coordinate
insertion then identify the signed native seven-simplex sum.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivision

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision
  (orientedPrismRealization orientedPrismRealization_eq_sum
    orientedPrismRealization_edge_eq_standard orientedPrismRealization_standardPrism)

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original seven-cube chain is the signed affine realization of the
actual recursive edge product on its 720 right-cube simplices. -/
theorem cubeChain_eq_orientedPrismRealization (p : GenLoop (Fin 7) X x) :
    cubeChain p = orientedPrismRealization p.val 7
      (formalEdgeCrossProduct 6 (formalSimplex (fun i : Fin 2 => i))
        (formalSimplex (fun j : Fin 7 => j))) := by
  rw [cubeChain_eq_sum_prisms, orientedPrismRealization_eq_sum]
  simp only [intervalSixSimplexChain_eq_prismCubeRealization]

/-- Every original native based seven-cube chain is exactly the sum of its
5040 affine seven-simplices with their permutation orientations. -/
theorem cubeChain_eq_sum_simplices (p : GenLoop (Fin 7) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 7),
      cubeOrientation e • simplexChain X 7 (p.val.comp (cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization,
    orientedPrismRealization_edge_eq_standard (n := 4) p,
    orientedPrismRealization_standardPrism]

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivision
