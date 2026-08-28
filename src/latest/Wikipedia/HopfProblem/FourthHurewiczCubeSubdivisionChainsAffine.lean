import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsAffineGeometry
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsCurrying

/-!
# The exact affine realization of the original interval-tetrahedron cross product

The universal formal edge product is realized by the actual product of
standard simplices and then by the original cube map. The identification
holds before normalization and retains every repeated-vertex term.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- The formal prism realization is the actual affine product realization followed
by its genuine cube map, in every geometric degree. -/
theorem prismCubeRealization_eq_induced {n : ℕ} (p : C(CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) :
    prismCubeRealization p e m =
      (inducedChain (p.comp (prismCubeMap e)) m).comp
        ((productAffineChainMap 1 n m).comp
          (formalMap (Prod.map (stdVertices 1) (stdVertices n)) (m + 1))) := by
  apply formalChains_ext
  intro v
  simp only [prismCubeRealization_simplex, LinearMap.comp_apply,
    formalMap_simplex, productAffineChainMap_simplex, inducedChain_simplex]
  apply congrArg (simplexChain X m)
  change p.comp (prismCubeSimplex e v) =
    p.comp ((prismCubeMap e).comp
      (productAffineSimplex (fun j => (stdVertices 1 (v j).1, stdVertices n (v j).2))))
  rw [prismCubeMap_affine]

/-- Realizing the universal recursive edge product gives precisely the actual
cross-product affine chain, not a normalized replacement. -/
theorem prismCubeRealization_edgeCrossProduct {n : ℕ}
    (p : C(CubeN (n + 1), X)) (e : Equiv.Perm (Fin n)) :
    prismCubeRealization p e (n + 1)
        (formalEdgeCrossProduct n (formalSimplex (fun i : Fin 2 => i))
          (formalSimplex (fun j : Fin (n + 1) => j))) =
      inducedChain (p.comp (prismCubeMap e)) (n + 1)
        (productAffineChainMap 1 n (n + 1)
          (formalEdgeCrossProduct n (formalSimplex (stdVertices 1))
            (formalSimplex (stdVertices n)))) := by
  rw [prismCubeRealization_eq_induced]
  simp only [LinearMap.comp_apply]
  rw [formalMap_edgeCrossProduct]
  simp only [formalMap_simplex, Function.comp_def]

/-- The frozen tetrahedron is the dimension-three instance of the general cube simplex. -/
theorem cubeTetrahedron_eq_cubeSimplex (e : Equiv.Perm (Fin 3)) :
    ThirdHurewicz.Geometry.cubeTetrahedron e = cubeSimplex e := rfl

/-- The generic affine prism map agrees with the original four-cube coordinate map. -/
theorem prismCubeMap_three (e : Equiv.Perm (Fin 3)) :
    cubeCoordinates.comp ((pathSimplex Path.id).prodMap
      (ThirdHurewicz.Geometry.cubeTetrahedron e)) = prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact cubeCoordinates_zero _
  · change cubeCoordinates (pathSimplex Path.id z.1,
      ThirdHurewicz.Geometry.cubeTetrahedron e z.2) j.succ = _
    rw [cubeCoordinates_succ]
    rfl

variable {x : X}

/-- The exact affine realization of the original degree-three recursive edge product
is one of the six actual prisms in the native four-cube chain. -/
theorem intervalTetrahedronChain_eq_prismCubeRealization
    (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 3)) :
    intervalTetrahedronChain p e = prismCubeRealization p.val e 4
      (formalEdgeCrossProduct 3 (formalSimplex (fun i : Fin 2 => i))
        (formalSimplex (fun j : Fin 4 => j))) := by
  rw [intervalTetrahedronChain_eq_original, SecondHurewicz.intervalChain,
    pathChain, crossProductEdge_simplex, prismCubeRealization_edgeCrossProduct]
  change ((inducedChain (cubeMap p) 4).comp
    (inducedChain ((pathSimplex Path.id).prodMap
      (ThirdHurewicz.Geometry.cubeTetrahedron e)) 4)) _ = _
  rw [← inducedChain_comp]
  change inducedChain (p.val.comp (cubeCoordinates.comp
    ((pathSimplex Path.id).prodMap (ThirdHurewicz.Geometry.cubeTetrahedron e)))) 4 _ = _
  rw [prismCubeMap_three]

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
