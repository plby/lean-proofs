import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometryAffine
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChainsFormal

/-!
# The literal twelve singular tetrahedra of an interval-triangle prism

This realizes the formal cone expansion in the original singular chain
complex of the native cube.  In particular, every repeated-vertex term
of the unnormalized cross product is retained.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology Geometry
open SecondHurewicz SecondHurewicz.SimplyConnected

attribute [local instance] integerLinearMapModule integerTensorModule

/-- An actual tetrahedron of a square-triangle prism, with its four ordered indices. -/
def prismSimplex (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3) :
    C(Simplex 3, Cube3) :=
  cubeAffineSimplex (fun j => cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2])

def prismSimplexChain (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3) :
    Chains Cube3 3 := simplexChain Cube3 3 (prismSimplex v w)

/-- Realize a formal prism on indexed vertices using the actual cross-product maps. -/
def prismRealization (v : Fin 3 → Fin 2 × Fin 2) :
    FormalChains (Fin 2 × Fin 3) 4 →ₗ[ℤ] Chains Cube3 3 :=
  (inducedChain (cubeTrianglePrism v) 3).comp
    ((productAffineChainMap 1 2 3).comp
      (formalMap (fun z : Fin 2 × Fin 3 => (stdVertices 1 z.1, stdVertices 2 z.2)) 4))

@[simp] theorem prismRealization_simplex (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) :
    prismRealization v (formalSimplex w) = prismSimplexChain v w := by
  simp only [prismRealization, LinearMap.comp_apply, formalMap_simplex,
    productAffineChainMap_simplex, inducedChain_simplex]
  change simplexChain Cube3 3 ((cubeTrianglePrism v).comp
    (productAffineSimplex (fun j => (stdVertices 1 (w j).1, stdVertices 2 (w j).2)))) = _
  rw [cubeTrianglePrism_affine]
  rfl

/-- The frozen interval cross product with a literal square triangle,
transported to the native three-dimensional cube. -/
def intervalTriangleChain (v : Fin 3 → Fin 2 × Fin 2) : Chains Cube3 3 :=
  inducedChain cubeCoordinates 3
    (crossProductEdge I (Fin 2 → I) 2 intervalChain
      (inducedChain squareCoordinates 2 (simplexChain (I × I) 2 (squareAffineTriangle v))))

theorem intervalTriangleChain_eq_prismRealization (v : Fin 3 → Fin 2 × Fin 2) :
    intervalTriangleChain v =
      prismRealization v (formalEdgeCrossProduct 2
        (formalSimplex (fun i : Fin 2 => i)) (formalSimplex (fun j : Fin 3 => j))) := by
  have h := formalMap_edgeCrossProduct (stdVertices 1) (stdVertices 2) 2
    (formalSimplex (fun i : Fin 2 => i)) (formalSimplex (fun j : Fin 3 => j))
  simp only [formalMap_simplex, Function.comp_def] at h
  rw [intervalTriangleChain, inducedChain_simplex, intervalChain, pathChain,
    crossProductEdge_simplex]
  change ((inducedChain cubeCoordinates 3).comp
    (inducedChain ((pathSimplex Path.id).prodMap
      (squareCoordinates.comp (squareAffineTriangle v))) 3))
      (productAffineChainMap 1 2 3
        (formalEdgeCrossProduct 2 (formalSimplex (stdVertices 1))
          (formalSimplex (stdVertices 2)))) = _
  rw [← inducedChain_comp, ← h]
  rfl

/-- The exact twelve-term expansion before any cancellation or normalization. -/
theorem intervalTriangleChain_twelve_tetrahedra (v : Fin 3 → Fin 2 × Fin 2) :
    intervalTriangleChain v =
      prismSimplexChain v ![(0, 0), (1, 0), (1, 1), (1, 2)] -
        prismSimplexChain v ![(0, 0), (0, 1), (1, 1), (1, 2)] +
        prismSimplexChain v ![(0, 0), (0, 1), (0, 2), (1, 2)] -
        prismSimplexChain v ![(0, 0), (0, 0), (0, 1), (0, 2)] +
        prismSimplexChain v ![(0, 0), (0, 1), (0, 1), (0, 2)] -
        prismSimplexChain v ![(0, 0), (0, 1), (0, 1), (1, 1)] +
        prismSimplexChain v ![(0, 0), (0, 0), (1, 0), (1, 2)] -
        prismSimplexChain v ![(0, 0), (0, 0), (0, 0), (0, 2)] -
        prismSimplexChain v ![(0, 0), (0, 0), (0, 2), (1, 2)] -
        prismSimplexChain v ![(0, 0), (0, 0), (1, 0), (1, 1)] +
        prismSimplexChain v ![(0, 0), (0, 0), (0, 0), (0, 1)] +
        prismSimplexChain v ![(0, 0), (0, 0), (0, 1), (1, 1)] := by
  rw [intervalTriangleChain_eq_prismRealization]
  have h := congrArg (prismRealization v)
    (formalEdgeCrossProduct_two_expansion (fun i : Fin 2 => i) (fun j : Fin 3 => j))
  simpa only [map_sub, map_add, prismRealization_simplex] using h

end Wikipedia.HopfProblem.ThirdHurewicz.CubeSubdivision
