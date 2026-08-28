import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.ChainsBoundary

/-!
# Cubical suspension chains for the seventh Hurewicz map

Crossing an actual chain in the based six-loop space with the frozen
fundamental six-cube and evaluating raises its degree by six. The
paired-face cancellation gives genuine seven-cycles and explicit
eight-chain primitives for homotopy and concatenation.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- Evaluation of an actual one-chain crossed with the fundamental six-cube. -/
def suspensionOne (x : X) : Chains (BasedLoopSpace x) 1 →ₗ[ℤ] Chains X 7 :=
  (inducedChain (evaluation x) 7).comp
    (integerBilinearRightApply (crossProductEdge (BasedLoopSpace x) (Fin 6 → I) 6)
      SixthHurewicz.fundamentalCubeChain)

@[simp] theorem suspensionOne_apply (x : X) (a : Chains (BasedLoopSpace x) 1) :
    suspensionOne x a = inducedChain (evaluation x) 7
      (crossProductEdge (BasedLoopSpace x) (Fin 6 → I) 6 a
        SixthHurewicz.fundamentalCubeChain) := rfl

/-- The genuine degree-eight chains for homotopy and concatenation primitives. -/
def suspensionTwo (x : X) : Chains (BasedLoopSpace x) 2 →ₗ[ℤ] Chains X 8 :=
  (inducedChain (evaluation x) 8).comp
    (integerBilinearRightApply (crossProductTriangle (BasedLoopSpace x) (Fin 6 → I) 6)
      SixthHurewicz.fundamentalCubeChain)

@[simp] theorem suspensionTwo_apply (x : X) (a : Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a = inducedChain (evaluation x) 8
      (crossProductTriangle (BasedLoopSpace x) (Fin 6 → I) 6 a
        SixthHurewicz.fundamentalCubeChain) := rfl

/-- An actual one-cycle in the based six-loop space determines a seven-cycle. -/
theorem boundarySeven_suspensionOne_of_cycle (x : X) (a : Chains (BasedLoopSpace x) 1)
    (ha : boundaryOne (BasedLoopSpace x) a = 0) :
    ((singularComplex X).d 7 6).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← inducedChain_boundary, crossProductEdge_boundary 5]
  change inducedChain (evaluation x) 6
    (crossProductZeroLeft (BasedLoopSpace x) (Fin 6 → I) 6
        (boundaryOne (BasedLoopSpace x) a) SixthHurewicz.fundamentalCubeChain -
      crossProductEdge (BasedLoopSpace x) (Fin 6 → I) 5 a
        (((singularComplex (Fin 6 → I)).d 6 5).hom SixthHurewicz.fundamentalCubeChain)) = 0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg,
    evaluated_edge_cubeBoundary_cancel, neg_zero]

/-- The actual eight-chain boundary is precisely the cubical suspension of
the original two-chain boundary. -/
theorem boundaryEight_suspensionTwo (x : X) (a : Chains (BasedLoopSpace x) 2) :
    ((singularComplex X).d 8 7).hom (suspensionTwo x a) =
      suspensionOne x (boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← inducedChain_boundary, crossProductTriangle_boundary 5]
  change inducedChain (evaluation x) 7
    (crossProductEdge (BasedLoopSpace x) (Fin 6 → I) 6
        (boundaryTwo (BasedLoopSpace x) a) SixthHurewicz.fundamentalCubeChain +
      crossProductTriangle (BasedLoopSpace x) (Fin 6 → I) 5 a
        (((singularComplex (Fin 6 → I)).d 6 5).hom SixthHurewicz.fundamentalCubeChain)) = _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
