import Wikipedia.HopfProblem.FifthHurewiczCube
import Wikipedia.HopfProblem.FifthHurewiczCubeSubdivisionChainsCurryingGeometry
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChains

/-!
# The original five-cube chain as twenty-four genuine recursive prisms

The proved four-cube subdivision applies to the actual curried based
four-loop in the continuous interval-map space. Naturality and joint
evaluation give an equality of the original unnormalized five-chains.
Every prism retains the frozen recursive degree-four edge cross product.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision (evalLeft)

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Evaluation commutes with the actual interval product after currying the original five-cube. -/
theorem evalLeft_crossProductEdge_curryLoop (p : GenLoop (Fin 5) X x) (n : ℕ)
    (b : Chains (Fin 4 → I) n) :
    inducedChain (evalLeft X) (n + 1)
        (crossProductEdge I C(I, X) n SecondHurewicz.intervalChain
          (inducedChain (curryLoop p).val n b)) =
      inducedChain (cubeMap p) (n + 1)
        (crossProductEdge I (Fin 4 → I) n SecondHurewicz.intervalChain b) := by
  have h := crossProductEdge_natural (ContinuousMap.id I) (curryLoop p).val n
    SecondHurewicz.intervalChain b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evalLeft X) (n + 1)).comp
    (inducedChain ((ContinuousMap.id I).prodMap (curryLoop p).val) (n + 1))) _ = _
  rw [← inducedChain_comp, evalLeft_comp_curryLoop]

/-- The original native five-cube chain is the evaluated product with the original
fourth Hurewicz chain of its actual curried based four-loop. -/
theorem cubeChain_eq_curriedCrossProduct (p : GenLoop (Fin 5) X x) :
    cubeChain p = inducedChain (evalLeft X) 5
      (crossProductEdge I C(I, X) 4 SecondHurewicz.intervalChain
        (FourthHurewicz.cubeChain (curryLoop p))) := by
  rw [FourthHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    cubeChain_eq_induced, fundamentalCubeChain]
  change (inducedChain p.val 5) ((inducedChain cubeCoordinates 5) productCubeChain) =
    (inducedChain (p.val.comp cubeCoordinates) 5) productCubeChain
  rw [inducedChain_comp]
  rfl

/-- One genuine interval-four-simplex prism obtained from the actual curried five-cube. -/
def intervalFourSimplexChain (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 4)) :
    Chains X 5 :=
  inducedChain (evalLeft X) 5
    (crossProductEdge I C(I, X) 4 SecondHurewicz.intervalChain
      (simplexChain C(I, X) 4 ((curryLoop p).val.comp (cubeSimplex e))))

/-- Each evaluated prism is the original five-cube map applied to its genuine
interval-times-four-simplex singular cross product. -/
theorem intervalFourSimplexChain_eq_original (p : GenLoop (Fin 5) X x)
    (e : Equiv.Perm (Fin 4)) :
    intervalFourSimplexChain p e = inducedChain (cubeMap p) 5
      (crossProductEdge I (Fin 4 → I) 4 SecondHurewicz.intervalChain
        (simplexChain (Fin 4 → I) 4 (cubeSimplex e))) := by
  rw [intervalFourSimplexChain, ← inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

/-- The exact twenty-four-prism expansion, indexed by the actual four-coordinate permutations. -/
theorem cubeChain_eq_sum_prisms (p : GenLoop (Fin 5) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 4),
      cubeOrientation e • intervalFourSimplexChain p e := by
  rw [cubeChain_eq_curriedCrossProduct,
    FourthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices]
  simp only [map_sum, map_zsmul, intervalFourSimplexChain]

end Wikipedia.HopfProblem.FifthHurewicz.CubeSubdivision
