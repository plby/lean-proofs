import Wikipedia.HopfProblem.SixthHurewiczCubeSubdivisionChainsCurrying
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsAffine

/-!
# Exact affine realization of the original interval-five-simplex prisms

The six-cube coordinate map identifies each actual recursive prism with
the generic affine realization. This equality retains every term of the
original edge cross product before the general correction cancellation.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision
  (prismCubeMap prismCubeRealization prismCubeRealization_edgeCrossProduct)

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- The generic affine prism map is the original six-cube coordinate map
on the interval times each actual five-simplex. -/
theorem prismCubeMap_five (e : Equiv.Perm (Fin 5)) :
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

/-- The genuine recursive interval-five-simplex chain equals its generic
affine realization, including all repeated-vertex terms. -/
theorem intervalFiveSimplexChain_eq_prismCubeRealization
    (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 5)) :
    intervalFiveSimplexChain p e = prismCubeRealization p.val e 6
      (formalEdgeCrossProduct 5 (formalSimplex (fun i : Fin 2 => i))
        (formalSimplex (fun j : Fin 6 => j))) := by
  rw [intervalFiveSimplexChain_eq_original, SecondHurewicz.intervalChain,
    pathChain, crossProductEdge_simplex, prismCubeRealization_edgeCrossProduct]
  change ((inducedChain (cubeMap p) 6).comp
    (inducedChain ((pathSimplex Path.id).prodMap (cubeSimplex e)) 6)) _ = _
  rw [← inducedChain_comp]
  change inducedChain (p.val.comp (cubeCoordinates.comp
    ((pathSimplex Path.id).prodMap (cubeSimplex e)))) 6 _ = _
  rw [prismCubeMap_five]

end Wikipedia.HopfProblem.SixthHurewicz.CubeSubdivision
