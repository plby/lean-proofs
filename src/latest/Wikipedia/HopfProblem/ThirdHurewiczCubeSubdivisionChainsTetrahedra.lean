import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChainsPrism
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometryPermutations

/-!
# The six nondegenerate prism terms are the six native cube tetrahedra

The interval coordinate is coordinate zero. The two square triangles
produce coordinate orders `012, 102, 120` and `021, 201, 210`,
respectively. Their ordered affine simplices are identified literally.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris Geometry

theorem prismSimplex_lower_zero :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)] =
      cubeTetrahedron 1 := by
  change cubeAffineSimplex _ = cubeAffineSimplex (cubeVertex (Equiv.refl (Fin 3)))
  apply congrArg cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;> simp [cubeBitVertex, cubeVertex, stdVertices]

theorem prismSimplex_lower_one :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)] =
      cubeTetrahedron (Equiv.swap 0 1) := by
  apply congrArg cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [cubeBitVertex, cubeVertex, stdVertices, Equiv.swap_apply_def]

theorem prismSimplex_lower_two :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)] =
      cubeTetrahedron ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) := by
  apply congrArg cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [cubeBitVertex, cubeVertex, stdVertices, Equiv.swap_apply_def]

theorem prismSimplex_upper_zero :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)] =
      cubeTetrahedron (Equiv.swap 1 2) := by
  apply congrArg cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [cubeBitVertex, cubeVertex, stdVertices, Equiv.swap_apply_def]

theorem prismSimplex_upper_one :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)] =
      cubeTetrahedron ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) := by
  apply congrArg cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [cubeBitVertex, cubeVertex, stdVertices, Equiv.swap_apply_def]

theorem prismSimplex_upper_two :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)] =
      cubeTetrahedron (Equiv.swap 0 2) := by
  apply congrArg cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [cubeBitVertex, cubeVertex, stdVertices, Equiv.swap_apply_def]

end Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision
