import Wikipedia.HopfProblem.FourthHurewiczCube
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsCurryingGeometry
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChains

/-!
# The original four-cube chain as six genuine interval-tetrahedron prisms

Currying the native four-cube in its first interval variable allows the
proved six-tetrahedron formula to be applied in the continuous-map
space. Cross-product naturality and evaluation then yield an equality
of the original, unnormalized singular four-chains. The prism terms
retain the frozen recursive edge cross product in degree three.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open ThirdHurewicz.Geometry

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Evaluation commutes with the actual interval product after currying the original cube. -/
theorem evalLeft_crossProductEdge_curryLoop (p : GenLoop (Fin 4) X x) (n : ℕ)
    (b : Chains (Fin 3 → I) n) :
    inducedChain (evalLeft X) (n + 1)
        (crossProductEdge I C(I, X) n SecondHurewicz.intervalChain
          (inducedChain (curryLoop p).val n b)) =
      inducedChain (cubeMap p) (n + 1)
        (crossProductEdge I (Fin 3 → I) n SecondHurewicz.intervalChain b) := by
  have h := crossProductEdge_natural (ContinuousMap.id I) (curryLoop p).val n
    SecondHurewicz.intervalChain b
  rw [inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change ((inducedChain (evalLeft X) (n + 1)).comp
    (inducedChain ((ContinuousMap.id I).prodMap (curryLoop p).val) (n + 1))) _ = _
  rw [← inducedChain_comp, evalLeft_comp_curryLoop]

/-- The original native four-cube chain is the evaluated product with the original
third Hurewicz chain of its actual curried based three-loop. -/
theorem cubeChain_eq_curriedCrossProduct (p : GenLoop (Fin 4) X x) :
    cubeChain p = inducedChain (evalLeft X) 4
      (crossProductEdge I C(I, X) 3 SecondHurewicz.intervalChain
        (ThirdHurewicz.cubeChain (curryLoop p))) := by
  rw [ThirdHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    cubeChain_eq_induced, fundamentalCubeChain]
  change (inducedChain p.val 4) ((inducedChain cubeCoordinates 4) productCubeChain) =
    (inducedChain (p.val.comp cubeCoordinates) 4) productCubeChain
  rw [inducedChain_comp]
  rfl

/-- One genuine interval-tetrahedron prism obtained from the curried native cube. -/
def intervalTetrahedronChain (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 3)) :
    Chains X 4 :=
  inducedChain (evalLeft X) 4
    (crossProductEdge I C(I, X) 3 SecondHurewicz.intervalChain
      (simplexChain C(I, X) 3 ((curryLoop p).val.comp (cubeTetrahedron e))))

/-- Each evaluated prism is the original four-cube map applied to its genuine
interval-times-tetrahedron singular cross product. -/
theorem intervalTetrahedronChain_eq_original (p : GenLoop (Fin 4) X x)
    (e : Equiv.Perm (Fin 3)) :
    intervalTetrahedronChain p e = inducedChain (cubeMap p) 4
      (crossProductEdge I (Fin 3 → I) 3 SecondHurewicz.intervalChain
        (simplexChain (Fin 3 → I) 3 (cubeTetrahedron e))) := by
  rw [intervalTetrahedronChain, ← inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

/-- The exact six-prism expansion, indexed by the original three-coordinate permutations. -/
theorem cubeChain_eq_sum_prisms (p : GenLoop (Fin 4) X x) :
    cubeChain p = ∑ e : Equiv.Perm (Fin 3),
      cubeOrientation e • intervalTetrahedronChain p e := by
  rw [cubeChain_eq_curriedCrossProduct,
    ThirdHurewicz.CubeSubdivision.cubeChain_eq_sum_tetrahedra]
  simp only [map_sum, map_zsmul, intervalTetrahedronChain]

/-- The same equality with all six genuine interval-tetrahedron prisms displayed. -/
theorem cubeChain_six_prisms (p : GenLoop (Fin 4) X x) :
    cubeChain p =
      intervalTetrahedronChain p 1 -
        intervalTetrahedronChain p (Equiv.swap 0 1) +
        intervalTetrahedronChain p ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) -
        intervalTetrahedronChain p (Equiv.swap 1 2) +
        intervalTetrahedronChain p ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) -
        intervalTetrahedronChain p (Equiv.swap 0 2) := by
  rw [cubeChain_eq_curriedCrossProduct,
    ThirdHurewicz.CubeSubdivision.cubeChain_six_tetrahedra]
  simp only [map_add, map_sub, intervalTetrahedronChain]

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
