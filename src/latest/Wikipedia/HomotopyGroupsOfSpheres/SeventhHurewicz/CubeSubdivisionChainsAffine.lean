import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivisionChainsCurrying
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsAffine

/-!
# Exact affine realization of the original interval-six-simplex prisms

The seven-cube coordinate map identifies each actual recursive prism with
the generic affine realization. This equality retains every term of the
original edge cross product before the general correction cancellation.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivision

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision
  (prismCubeMap prismCubeRealization prismCubeRealization_edgeCrossProduct)

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- The generic affine prism map is the original seven-cube coordinate map
on the interval times each actual six-simplex. -/
theorem prismCubeMap_six (e : Equiv.Perm (Fin 6)) :
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

/-- The genuine recursive interval-six-simplex chain equals its generic
affine realization, including all repeated-vertex terms. -/
theorem intervalSixSimplexChain_eq_prismCubeRealization
    (p : GenLoop (Fin 7) X x) (e : Equiv.Perm (Fin 6)) :
    intervalSixSimplexChain p e = prismCubeRealization p.val e 7
      (formalEdgeCrossProduct 6 (formalSimplex (fun i : Fin 2 => i))
        (formalSimplex (fun j : Fin 7 => j))) := by
  rw [intervalSixSimplexChain_eq_original, SecondHurewicz.intervalChain,
    pathChain, crossProductEdge_simplex, prismCubeRealization_edgeCrossProduct]
  change ((inducedChain (cubeMap p) 7).comp
    (inducedChain ((pathSimplex Path.id).prodMap (cubeSimplex e)) 7)) _ = _
  rw [← inducedChain_comp]
  change inducedChain (p.val.comp (cubeCoordinates.comp
    ((pathSimplex Path.id).prodMap (cubeSimplex e)))) 7 _ = _
  rw [prismCubeMap_six]

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivision
