import Wikipedia.HopfProblem.ThirdHurewiczCube
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChainsTetrahedra
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChainsCorrection

/-!
# Exact six-tetrahedron expansion of the original third Hurewicz cube chain

The frozen fundamental square contains four actual triangles, two of
which are boundary-supported.  Their genuine interval products are
expanded in the original unnormalized singular chain group. The side
terms and common diagonal cone correction cancel, leaving exactly the
six affine tetrahedra with their actual permutation signs.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology Geometry
open SecondHurewicz SecondHurewicz.SimplyConnected

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The four actual prisms of the original cone-defined fundamental cube chain. -/
theorem fundamentalCubeChain_four_prisms :
    fundamentalCubeChain =
      intervalTriangleChain ![(0, 0), (1, 0), (1, 1)] -
        intervalTriangleChain ![(0, 0), (0, 0), (0, 1)] -
        intervalTriangleChain ![(0, 0), (0, 1), (1, 1)] +
        intervalTriangleChain ![(0, 0), (0, 0), (1, 0)] := by
  rw [fundamentalCubeChain, productCubeChain, fundamentalSquareChain,
    productSquareChain_four_triangles]
  simp only [map_add, map_sub]
  rfl

variable {X : Type} [TopologicalSpace X] {x : X}

/-- All correction terms cancel in the actual singular chain group. -/
theorem induced_fundamentalCubeChain_eq_principal (p : GenLoop (Fin 3) X x) :
    inducedChain p.val 3 fundamentalCubeChain =
      diagonalPrismPrincipal p (1, 0) - diagonalPrismPrincipal p (0, 1) := by
  rw [fundamentalCubeChain_four_prisms]
  simp only [map_add, map_sub]
  rw [induced_intervalTriangleChain_of_fst p ![(0, 0), (0, 0), (0, 1)]
      (Or.inl (by intro j; fin_cases j <;> rfl)),
    induced_intervalTriangleChain_of_snd p ![(0, 0), (0, 0), (1, 0)]
      (Or.inl (by intro j; fin_cases j <;> rfl)), sub_zero, add_zero]
  exact induced_diagonalPrism_sub p

/-- Literal six-tetrahedron formula for the chain of the original native based cube. -/
theorem cubeChain_six_tetrahedra (p : GenLoop (Fin 3) X x) :
    cubeChain p =
      simplexChain X 3 (p.val.comp (cubeTetrahedron 1)) -
        simplexChain X 3 (p.val.comp (cubeTetrahedron (Equiv.swap 0 1))) +
        simplexChain X 3 (p.val.comp
          (cubeTetrahedron ((Equiv.swap 1 2).trans (Equiv.swap 0 1)))) -
        simplexChain X 3 (p.val.comp (cubeTetrahedron (Equiv.swap 1 2))) +
        simplexChain X 3 (p.val.comp
          (cubeTetrahedron ((Equiv.swap 0 1).trans (Equiv.swap 1 2)))) -
        simplexChain X 3 (p.val.comp (cubeTetrahedron (Equiv.swap 0 2))) := by
  rw [cubeChain_eq_induced, induced_fundamentalCubeChain_eq_principal]
  simp only [diagonalPrismPrincipal, prismSimplexChain, inducedChain_simplex,
    prismSimplex_lower_zero, prismSimplex_lower_one, prismSimplex_lower_two,
    prismSimplex_upper_zero, prismSimplex_upper_one, prismSimplex_upper_two]
  abel

/-- The same exact chain identity indexed by the actual six coordinate permutations. -/
theorem cubeChain_eq_sum_tetrahedra (p : GenLoop (Fin 3) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 3),
      cubeOrientation e • simplexChain X 3 (p.val.comp (cubeTetrahedron e)) := by
  rw [cubeChain_six_tetrahedra, sum_oriented_cubePermutations]
  abel

end Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision
