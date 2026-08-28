import Wikipedia.HopfProblem.SixthHurewiczCube
import Wikipedia.HopfProblem.SixthHurewiczCubeSubdivisionChainsCurryingGeometry
import Wikipedia.HopfProblem.FifthHurewiczCubeSubdivisionChains

/-!
# The original six-cube chain as 120 genuine recursive prisms

The proved five-cube subdivision applies to the actual curried based
five-loop in the continuous interval-map space. Naturality and joint
evaluation give an equality of the original unnormalized six-chains.
Every prism retains the frozen recursive degree-five edge cross product.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open HigherHurewicz.CubeTriangulation
open FourthHurewicz.CubeSubdivision (evalLeft)

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Evaluation commutes with the actual interval product after currying the original six-cube. -/
theorem evalLeft_crossProductEdge_curryLoop (p : GenLoop (Fin 6) X x) (n : ℕ)
    (b : Chains (Fin 5 → I) n) :
    inducedChain (evalLeft X) (n + 1)
        (crossProductEdge I C(I, X) n SecondHurewicz.intervalChain
          (inducedChain (curryLoop p).val n b)) =
      inducedChain (cubeMap p) (n + 1)
        (crossProductEdge I (Fin 5 → I) n SecondHurewicz.intervalChain b) := by
  have h := crossProductEdge_natural (ContinuousMap.id I) (curryLoop p).val n
    SecondHurewicz.intervalChain b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evalLeft X) (n + 1)).comp
    (inducedChain ((ContinuousMap.id I).prodMap (curryLoop p).val) (n + 1))) _ = _
  rw [← inducedChain_comp, evalLeft_comp_curryLoop]

/-- The original native six-cube chain is the evaluated product with the original
fifth Hurewicz chain of its actual curried based five-loop. -/
theorem cubeChain_eq_curriedCrossProduct (p : GenLoop (Fin 6) X x) :
    cubeChain p = inducedChain (evalLeft X) 6
      (crossProductEdge I C(I, X) 5 SecondHurewicz.intervalChain
        (FifthHurewicz.cubeChain (curryLoop p))) := by
  rw [FifthHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    cubeChain_eq_induced, fundamentalCubeChain]
  change (inducedChain p.val 6) ((inducedChain cubeCoordinates 6) productCubeChain) =
    (inducedChain (p.val.comp cubeCoordinates) 6) productCubeChain
  rw [inducedChain_comp]
  rfl

/-- One genuine interval-five-simplex prism obtained from the actual curried six-cube. -/
def intervalFiveSimplexChain (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 5)) :
    Chains X 6 :=
  inducedChain (evalLeft X) 6
    (crossProductEdge I C(I, X) 5 SecondHurewicz.intervalChain
      (simplexChain C(I, X) 5 ((curryLoop p).val.comp (cubeSimplex e))))

/-- Each evaluated prism is the original six-cube map applied to its genuine
interval-times-five-simplex singular cross product. -/
theorem intervalFiveSimplexChain_eq_original (p : GenLoop (Fin 6) X x)
    (e : Equiv.Perm (Fin 5)) :
    intervalFiveSimplexChain p e = inducedChain (cubeMap p) 6
      (crossProductEdge I (Fin 5 → I) 5 SecondHurewicz.intervalChain
        (simplexChain (Fin 5 → I) 5 (cubeSimplex e))) := by
  rw [intervalFiveSimplexChain, ← inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

/-- The exact 120-prism expansion, indexed by the actual five-coordinate permutations. -/
theorem cubeChain_eq_sum_prisms (p : GenLoop (Fin 6) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 5),
      cubeOrientation e • intervalFiveSimplexChain p e := by
  rw [cubeChain_eq_curriedCrossProduct,
    FifthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices]
  simp only [map_sum, map_zsmul, intervalFiveSimplexChain]

end Wikipedia.HopfProblem.SixthHurewicz.CubeSubdivision
