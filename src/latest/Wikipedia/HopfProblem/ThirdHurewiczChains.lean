import Wikipedia.HopfProblem.ThirdHurewiczChainsBoundary

/-!
# Cubical suspension chains for the third Hurewicz map

Crossing a chain in the actual based two-loop space with the fixed
fundamental square, then evaluating, raises its degree by two. The
square-boundary faces cancel as actual singular chains. This produces
three-cycles and explicit four-chains for path homotopies and concatenation.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- Evaluation of an actual one-chain crossed with the fundamental square. -/
def suspensionOne (x : X) : Chains (BasedLoopSpace x) 1 →ₗ[ℤ] Chains X 3 :=
  (inducedChain (evaluation x) 3).comp
    (integerBilinearRightApply (crossProductEdge (BasedLoopSpace x) (Fin 2 → I) 2)
      SecondHurewicz.fundamentalSquareChain)

@[simp] theorem suspensionOne_apply (x : X) (a : Chains (BasedLoopSpace x) 1) :
    suspensionOne x a = inducedChain (evaluation x) 3
      (crossProductEdge (BasedLoopSpace x) (Fin 2 → I) 2 a
        SecondHurewicz.fundamentalSquareChain) := rfl

/-- The actual degree-four chain for homotopy and concatenation primitives. -/
def suspensionTwo (x : X) : Chains (BasedLoopSpace x) 2 →ₗ[ℤ] Chains X 4 :=
  (inducedChain (evaluation x) 4).comp
    (integerBilinearRightApply (crossProductTriangle (BasedLoopSpace x) (Fin 2 → I) 2)
      SecondHurewicz.fundamentalSquareChain)

@[simp] theorem suspensionTwo_apply (x : X) (a : Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a = inducedChain (evaluation x) 4
      (crossProductTriangle (BasedLoopSpace x) (Fin 2 → I) 2 a
        SecondHurewicz.fundamentalSquareChain) := rfl

/-- A genuine one-cycle in the based two-loop space gives a singular three-cycle. -/
theorem boundaryThree_suspensionOne_of_cycle (x : X) (a : Chains (BasedLoopSpace x) 1)
    (ha : boundaryOne (BasedLoopSpace x) a = 0) :
    ((singularComplex X).d 3 2).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← inducedChain_boundary, crossProductEdge_boundary 1]
  change inducedChain (evaluation x) 2
    (crossProductZeroLeft (BasedLoopSpace x) (Fin 2 → I) 2
        (boundaryOne (BasedLoopSpace x) a) SecondHurewicz.fundamentalSquareChain -
      crossProductEdge (BasedLoopSpace x) (Fin 2 → I) 1 a
        (boundaryTwo (Fin 2 → I) SecondHurewicz.fundamentalSquareChain)) = 0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg,
    evaluated_edge_squareBoundary_cancel, neg_zero]

/-- The actual four-chain boundary is exactly the cubical suspension of
the original two-chain boundary. -/
theorem boundaryFour_suspensionTwo (x : X) (a : Chains (BasedLoopSpace x) 2) :
    ((singularComplex X).d 4 3).hom (suspensionTwo x a) =
      suspensionOne x (boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← inducedChain_boundary, crossProductTriangle_boundary 1]
  change inducedChain (evaluation x) 3
    (crossProductEdge (BasedLoopSpace x) (Fin 2 → I) 2
        (boundaryTwo (BasedLoopSpace x) a) SecondHurewicz.fundamentalSquareChain +
      crossProductTriangle (BasedLoopSpace x) (Fin 2 → I) 1 a
        (boundaryTwo (Fin 2 → I) SecondHurewicz.fundamentalSquareChain)) = _
  rw [map_add, evaluated_triangle_squareBoundary_cancel, add_zero]
  rfl

end Wikipedia.HopfProblem.ThirdHurewicz
