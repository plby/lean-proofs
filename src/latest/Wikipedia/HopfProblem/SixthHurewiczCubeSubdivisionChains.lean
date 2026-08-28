import Wikipedia.HopfProblem.SixthHurewiczCubeSubdivisionChainsAffine

/-!
# Exact 720-simplex expansion of the original sixth Hurewicz chain

The chain starts with the genuine recursive interval cross product and
the frozen fifth fundamental cube chain. Actual currying gives its
120 prisms; the proved general prism correction and coordinate
insertion then identify the signed native six-simplex sum.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision
  (orientedPrismRealization orientedPrismRealization_eq_sum
    orientedPrismRealization_edge_eq_standard orientedPrismRealization_standardPrism)

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original six-cube chain is the signed affine realization of the
actual recursive edge product on its 120 right-cube simplices. -/
theorem cubeChain_eq_orientedPrismRealization (p : GenLoop (Fin 6) X x) :
    cubeChain p = orientedPrismRealization p.val 6
      (formalEdgeCrossProduct 5 (formalSimplex (fun i : Fin 2 => i))
        (formalSimplex (fun j : Fin 6 => j))) := by
  rw [cubeChain_eq_sum_prisms, orientedPrismRealization_eq_sum]
  simp only [intervalFiveSimplexChain_eq_prismCubeRealization]

/-- Every original native based six-cube chain is exactly the sum of its
720 affine six-simplices with their permutation orientations. -/
theorem cubeChain_eq_sum_simplices (p : GenLoop (Fin 6) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 6),
      cubeOrientation e • simplexChain X 6 (p.val.comp (cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization,
    orientedPrismRealization_edge_eq_standard (n := 3) p,
    orientedPrismRealization_standardPrism]

end Wikipedia.HopfProblem.SixthHurewicz.CubeSubdivision
