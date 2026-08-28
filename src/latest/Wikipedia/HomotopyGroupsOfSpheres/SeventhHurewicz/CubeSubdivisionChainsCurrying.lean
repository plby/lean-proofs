import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Cube
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivisionChainsCurryingGeometry
import Wikipedia.HopfProblem.SixthHurewiczCubeSubdivisionChains

/-!
# The original seven-cube chain as 720 genuine recursive prisms

The proved six-cube subdivision applies to the actual curried based
six-loop in the continuous interval-map space. Naturality and joint
evaluation give an equality of the original unnormalized seven-chains.
Every prism retains the frozen recursive degree-six edge cross product.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivision

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision (evalLeft)

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Evaluation commutes with the actual interval product after currying the original seven-cube. -/
theorem evalLeft_crossProductEdge_curryLoop (p : GenLoop (Fin 7) X x) (n : ℕ)
    (b : Chains (Fin 6 → I) n) :
    inducedChain (evalLeft X) (n + 1)
        (crossProductEdge I C(I, X) n SecondHurewicz.intervalChain
          (inducedChain (curryLoop p).val n b)) =
      inducedChain (cubeMap p) (n + 1)
        (crossProductEdge I (Fin 6 → I) n SecondHurewicz.intervalChain b) := by
  have h := crossProductEdge_natural (ContinuousMap.id I) (curryLoop p).val n
    SecondHurewicz.intervalChain b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evalLeft X) (n + 1)).comp
    (inducedChain ((ContinuousMap.id I).prodMap (curryLoop p).val) (n + 1))) _ = _
  rw [← inducedChain_comp, evalLeft_comp_curryLoop]

/-- The original native seven-cube chain is the evaluated product with the original
sixth Hurewicz chain of its actual curried based six-loop. -/
theorem cubeChain_eq_curriedCrossProduct (p : GenLoop (Fin 7) X x) :
    cubeChain p = inducedChain (evalLeft X) 7
      (crossProductEdge I C(I, X) 6 SecondHurewicz.intervalChain
        (SixthHurewicz.cubeChain (curryLoop p))) := by
  rw [SixthHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    cubeChain_eq_induced, fundamentalCubeChain]
  change (inducedChain p.val 7) ((inducedChain cubeCoordinates 7) productCubeChain) =
    (inducedChain (p.val.comp cubeCoordinates) 7) productCubeChain
  rw [inducedChain_comp]
  rfl

/-- One genuine interval-six-simplex prism obtained from the actual curried seven-cube. -/
def intervalSixSimplexChain (p : GenLoop (Fin 7) X x) (e : Equiv.Perm (Fin 6)) :
    Chains X 7 :=
  inducedChain (evalLeft X) 7
    (crossProductEdge I C(I, X) 6 SecondHurewicz.intervalChain
      (simplexChain C(I, X) 6 ((curryLoop p).val.comp (cubeSimplex e))))

/-- Each evaluated prism is the original seven-cube map applied to its genuine
interval-times-six-simplex singular cross product. -/
theorem intervalSixSimplexChain_eq_original (p : GenLoop (Fin 7) X x)
    (e : Equiv.Perm (Fin 6)) :
    intervalSixSimplexChain p e = inducedChain (cubeMap p) 7
      (crossProductEdge I (Fin 6 → I) 6 SecondHurewicz.intervalChain
        (simplexChain (Fin 6 → I) 6 (cubeSimplex e))) := by
  rw [intervalSixSimplexChain, ← inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

/-- The exact 720-prism expansion, indexed by the actual six-coordinate permutations. -/
theorem cubeChain_eq_sum_prisms (p : GenLoop (Fin 7) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 6),
      cubeOrientation e • intervalSixSimplexChain p e := by
  rw [cubeChain_eq_curriedCrossProduct,
    SixthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices]
  simp only [map_sum, map_zsmul, intervalSixSimplexChain]

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivision
