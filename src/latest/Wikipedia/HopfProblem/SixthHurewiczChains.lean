import Wikipedia.HopfProblem.SixthHurewiczChainsBoundary

/-!
# Cubical suspension chains for the sixth Hurewicz map

Crossing an actual chain in the based five-loop space with the frozen
fundamental five-cube and evaluating raises its degree by five. The
paired-face cancellation gives genuine six-cycles and explicit
seven-chain primitives for homotopy and concatenation.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- Evaluation of an actual one-chain crossed with the fundamental five-cube. -/
def suspensionOne (x : X) : Chains (BasedLoopSpace x) 1 →ₗ[ℤ] Chains X 6 :=
  (inducedChain (evaluation x) 6).comp
    (integerBilinearRightApply (crossProductEdge (BasedLoopSpace x) (Fin 5 → I) 5)
      FifthHurewicz.fundamentalCubeChain)

@[simp] theorem suspensionOne_apply (x : X) (a : Chains (BasedLoopSpace x) 1) :
    suspensionOne x a = inducedChain (evaluation x) 6
      (crossProductEdge (BasedLoopSpace x) (Fin 5 → I) 5 a
        FifthHurewicz.fundamentalCubeChain) := rfl

/-- The genuine degree-seven chains for homotopy and concatenation primitives. -/
def suspensionTwo (x : X) : Chains (BasedLoopSpace x) 2 →ₗ[ℤ] Chains X 7 :=
  (inducedChain (evaluation x) 7).comp
    (integerBilinearRightApply (crossProductTriangle (BasedLoopSpace x) (Fin 5 → I) 5)
      FifthHurewicz.fundamentalCubeChain)

@[simp] theorem suspensionTwo_apply (x : X) (a : Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a = inducedChain (evaluation x) 7
      (crossProductTriangle (BasedLoopSpace x) (Fin 5 → I) 5 a
        FifthHurewicz.fundamentalCubeChain) := rfl

/-- An actual one-cycle in the based five-loop space determines a six-cycle. -/
theorem boundarySix_suspensionOne_of_cycle (x : X) (a : Chains (BasedLoopSpace x) 1)
    (ha : boundaryOne (BasedLoopSpace x) a = 0) :
    ((singularComplex X).d 6 5).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← inducedChain_boundary, crossProductEdge_boundary 4]
  change inducedChain (evaluation x) 5
    (crossProductZeroLeft (BasedLoopSpace x) (Fin 5 → I) 5
        (boundaryOne (BasedLoopSpace x) a) FifthHurewicz.fundamentalCubeChain -
      crossProductEdge (BasedLoopSpace x) (Fin 5 → I) 4 a
        (((singularComplex (Fin 5 → I)).d 5 4).hom FifthHurewicz.fundamentalCubeChain)) = 0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg,
    evaluated_edge_cubeBoundary_cancel, neg_zero]

/-- The actual seven-chain boundary is precisely the cubical suspension of
the original two-chain boundary. -/
theorem boundarySeven_suspensionTwo (x : X) (a : Chains (BasedLoopSpace x) 2) :
    ((singularComplex X).d 7 6).hom (suspensionTwo x a) =
      suspensionOne x (boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← inducedChain_boundary, crossProductTriangle_boundary 4]
  change inducedChain (evaluation x) 6
    (crossProductEdge (BasedLoopSpace x) (Fin 5 → I) 5
        (boundaryTwo (BasedLoopSpace x) a) FifthHurewicz.fundamentalCubeChain +
      crossProductTriangle (BasedLoopSpace x) (Fin 5 → I) 4 a
        (((singularComplex (Fin 5 → I)).d 5 4).hom FifthHurewicz.fundamentalCubeChain)) = _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

end Wikipedia.HopfProblem.SixthHurewicz
