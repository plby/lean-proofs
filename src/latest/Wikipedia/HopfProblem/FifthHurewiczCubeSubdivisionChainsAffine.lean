import Wikipedia.HopfProblem.FifthHurewiczCubeSubdivisionChainsCurrying
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsAffine

/-!
# Exact affine realization of the original interval-four-simplex prisms

The five-cube coordinate map identifies each actual recursive prism with
the generic affine realization. This equality retains every term of the
original edge cross product before the general correction cancellation.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision
  (prismCubeMap prismCubeRealization prismCubeRealization_edgeCrossProduct)

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- The generic affine prism map is the original five-cube coordinate map
on the interval times each actual four-simplex. -/
theorem prismCubeMap_four (e : Equiv.Perm (Fin 4)) :
    cubeCoordinates.comp ((pathSimplex Path.id).prodMap (cubeSimplex e)) =
      prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact cubeCoordinates_zero _
  · change cubeCoordinates (pathSimplex Path.id z.1, cubeSimplex e z.2) j.succ = _
    rw [cubeCoordinates_succ]
    rfl

variable {x : X}

/-- The genuine recursive interval-four-simplex chain equals its generic
affine realization, including all repeated-vertex terms. -/
theorem intervalFourSimplexChain_eq_prismCubeRealization
    (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 4)) :
    intervalFourSimplexChain p e = prismCubeRealization p.val e 5
      (formalEdgeCrossProduct 4 (formalSimplex (fun i : Fin 2 => i))
        (formalSimplex (fun j : Fin 5 => j))) := by
  rw [intervalFourSimplexChain_eq_original, SecondHurewicz.intervalChain,
    pathChain, crossProductEdge_simplex, prismCubeRealization_edgeCrossProduct]
  change ((inducedChain (cubeMap p) 5).comp
    (inducedChain ((pathSimplex Path.id).prodMap (cubeSimplex e)) 5)) _ = _
  rw [← inducedChain_comp]
  change inducedChain (p.val.comp (cubeCoordinates.comp
    ((pathSimplex Path.id).prodMap (cubeSimplex e)))) 5 _ = _
  rw [prismCubeMap_four]

end Wikipedia.HopfProblem.FifthHurewicz.CubeSubdivision
