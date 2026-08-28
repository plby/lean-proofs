import Wikipedia.HopfProblem.FourthHurewiczChainsBoundary

/-!
# Cubical suspension chains for the fourth Hurewicz map

Crossing an actual chain in the based three-loop space with the frozen
fundamental three-cube and evaluating raises its degree by three. The
boundary-face cancellation gives genuine four-cycles and explicit
five-chain primitives for path homotopy and concatenation.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- Evaluation of an actual one-chain crossed with the fundamental three-cube. -/
def suspensionOne (x : X) : Chains (BasedLoopSpace x) 1 →ₗ[ℤ] Chains X 4 :=
  (inducedChain (evaluation x) 4).comp
    (integerBilinearRightApply (crossProductEdge (BasedLoopSpace x) (Fin 3 → I) 3)
      ThirdHurewicz.fundamentalCubeChain)

@[simp] theorem suspensionOne_apply (x : X) (a : Chains (BasedLoopSpace x) 1) :
    suspensionOne x a = inducedChain (evaluation x) 4
      (crossProductEdge (BasedLoopSpace x) (Fin 3 → I) 3 a
        ThirdHurewicz.fundamentalCubeChain) := rfl

/-- The genuine degree-five chains for homotopy and concatenation primitives. -/
def suspensionTwo (x : X) : Chains (BasedLoopSpace x) 2 →ₗ[ℤ] Chains X 5 :=
  (inducedChain (evaluation x) 5).comp
    (integerBilinearRightApply (crossProductTriangle (BasedLoopSpace x) (Fin 3 → I) 3)
      ThirdHurewicz.fundamentalCubeChain)

@[simp] theorem suspensionTwo_apply (x : X) (a : Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a = inducedChain (evaluation x) 5
      (crossProductTriangle (BasedLoopSpace x) (Fin 3 → I) 3 a
        ThirdHurewicz.fundamentalCubeChain) := rfl

/-- Every actual one-cycle in the based three-loop space gives a four-cycle. -/
theorem boundaryFour_suspensionOne_of_cycle (x : X) (a : Chains (BasedLoopSpace x) 1)
    (ha : boundaryOne (BasedLoopSpace x) a = 0) :
    ((singularComplex X).d 4 3).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← inducedChain_boundary, crossProductEdge_boundary 2]
  change inducedChain (evaluation x) 3
    (crossProductZeroLeft (BasedLoopSpace x) (Fin 3 → I) 3
        (boundaryOne (BasedLoopSpace x) a) ThirdHurewicz.fundamentalCubeChain -
      crossProductEdge (BasedLoopSpace x) (Fin 3 → I) 2 a
        (((singularComplex (Fin 3 → I)).d 3 2).hom ThirdHurewicz.fundamentalCubeChain)) = 0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg,
    evaluated_edge_cubeBoundary_cancel, neg_zero]

/-- The actual five-chain boundary is the cubical suspension of the
original two-chain boundary, without additional correction terms. -/
theorem boundaryFive_suspensionTwo (x : X) (a : Chains (BasedLoopSpace x) 2) :
    ((singularComplex X).d 5 4).hom (suspensionTwo x a) =
      suspensionOne x (boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← inducedChain_boundary, crossProductTriangle_boundary 2]
  change inducedChain (evaluation x) 4
    (crossProductEdge (BasedLoopSpace x) (Fin 3 → I) 3
        (boundaryTwo (BasedLoopSpace x) a) ThirdHurewicz.fundamentalCubeChain +
      crossProductTriangle (BasedLoopSpace x) (Fin 3 → I) 2 a
        (((singularComplex (Fin 3 → I)).d 3 2).hom ThirdHurewicz.fundamentalCubeChain)) = _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

end Wikipedia.HopfProblem.FourthHurewicz
