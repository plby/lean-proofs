import Wikipedia.HopfProblem.FifthHurewiczChainsBoundary

/-!
# Cubical suspension chains for the fifth Hurewicz map

Crossing an actual chain in the based four-loop space with the frozen
fundamental four-cube and evaluating raises its degree by four. The
paired-face cancellation gives genuine five-cycles and explicit
six-chain primitives for homotopy and concatenation.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- Evaluation of an actual one-chain crossed with the fundamental four-cube. -/
def suspensionOne (x : X) : Chains (BasedLoopSpace x) 1 →ₗ[ℤ] Chains X 5 :=
  (inducedChain (evaluation x) 5).comp
    (integerBilinearRightApply (crossProductEdge (BasedLoopSpace x) (Fin 4 → I) 4)
      FourthHurewicz.fundamentalCubeChain)

@[simp] theorem suspensionOne_apply (x : X) (a : Chains (BasedLoopSpace x) 1) :
    suspensionOne x a = inducedChain (evaluation x) 5
      (crossProductEdge (BasedLoopSpace x) (Fin 4 → I) 4 a
        FourthHurewicz.fundamentalCubeChain) := rfl

/-- The genuine degree-six chains for homotopy and concatenation primitives. -/
def suspensionTwo (x : X) : Chains (BasedLoopSpace x) 2 →ₗ[ℤ] Chains X 6 :=
  (inducedChain (evaluation x) 6).comp
    (integerBilinearRightApply (crossProductTriangle (BasedLoopSpace x) (Fin 4 → I) 4)
      FourthHurewicz.fundamentalCubeChain)

@[simp] theorem suspensionTwo_apply (x : X) (a : Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a = inducedChain (evaluation x) 6
      (crossProductTriangle (BasedLoopSpace x) (Fin 4 → I) 4 a
        FourthHurewicz.fundamentalCubeChain) := rfl

/-- An actual one-cycle in the based four-loop space determines a five-cycle. -/
theorem boundaryFive_suspensionOne_of_cycle (x : X) (a : Chains (BasedLoopSpace x) 1)
    (ha : boundaryOne (BasedLoopSpace x) a = 0) :
    ((singularComplex X).d 5 4).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← inducedChain_boundary, crossProductEdge_boundary 3]
  change inducedChain (evaluation x) 4
    (crossProductZeroLeft (BasedLoopSpace x) (Fin 4 → I) 4
        (boundaryOne (BasedLoopSpace x) a) FourthHurewicz.fundamentalCubeChain -
      crossProductEdge (BasedLoopSpace x) (Fin 4 → I) 3 a
        (((singularComplex (Fin 4 → I)).d 4 3).hom FourthHurewicz.fundamentalCubeChain)) = 0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg,
    evaluated_edge_cubeBoundary_cancel, neg_zero]

/-- The actual six-chain boundary is precisely the cubical suspension of
the original two-chain boundary. -/
theorem boundarySix_suspensionTwo (x : X) (a : Chains (BasedLoopSpace x) 2) :
    ((singularComplex X).d 6 5).hom (suspensionTwo x a) =
      suspensionOne x (boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← inducedChain_boundary, crossProductTriangle_boundary 3]
  change inducedChain (evaluation x) 5
    (crossProductEdge (BasedLoopSpace x) (Fin 4 → I) 4
        (boundaryTwo (BasedLoopSpace x) a) FourthHurewicz.fundamentalCubeChain +
      crossProductTriangle (BasedLoopSpace x) (Fin 4 → I) 3 a
        (((singularComplex (Fin 4 → I)).d 4 3).hom FourthHurewicz.fundamentalCubeChain)) = _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

end Wikipedia.HopfProblem.FifthHurewicz
