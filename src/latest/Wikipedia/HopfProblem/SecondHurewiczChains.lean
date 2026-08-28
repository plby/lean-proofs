import Wikipedia.HopfProblem.SecondHurewiczEvaluation
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBoundary

/-!
# The square and prism chains for the second Hurewicz map

Crossing a chain in the native based-loop space with the actual interval
chain, then evaluating, raises its degree by one. The two endpoint maps
are literally the same constant map. Consequently one-cycles give
two-cycles, and two-boundaries give explicit three-boundaries.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X : Type} [TopologicalSpace X]

/-- The positively oriented singular chain of the actual unit interval. -/
def intervalChain : Chains I 1 := pathChain Path.id

theorem intervalChain_boundary :
    boundaryOne I intervalChain = pointChain (1 : I) - pointChain (0 : I) :=
  boundaryOne_pathChain Path.id

theorem evaluation_right_zero_chain (x : X) (n : ℕ) (a : Chains (BasedLoopSpace x) n) :
    inducedChain (evaluation x) n (inducedChain (crossInsertRight (0 : I)) n a) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change ((inducedChain (evaluation x) n).comp
    (inducedChain (crossInsertRight (0 : I)) n)) a = _
  rw [← inducedChain_comp, evaluation_comp_right_zero]

theorem evaluation_right_one_chain (x : X) (n : ℕ) (a : Chains (BasedLoopSpace x) n) :
    inducedChain (evaluation x) n (inducedChain (crossInsertRight (1 : I)) n a) =
      inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change ((inducedChain (evaluation x) n).comp
    (inducedChain (crossInsertRight (1 : I)) n)) a = _
  rw [← inducedChain_comp, evaluation_comp_right_one]

/-- The right endpoint correction vanishes already as a singular one-chain. -/
theorem evaluated_edge_endpoint_cancel (x : X) (a : Chains (BasedLoopSpace x) 1) :
    inducedChain (evaluation x) 1
        (crossProductEdge (BasedLoopSpace x) I 0 a (boundaryOne I intervalChain)) = 0 := by
  simp only [intervalChain_boundary, map_sub, crossProductEdge_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

/-- The corresponding endpoint correction also vanishes as a singular two-chain. -/
theorem evaluated_triangle_endpoint_cancel (x : X) (a : Chains (BasedLoopSpace x) 2) :
    inducedChain (evaluation x) 2
        (crossProductTriangle (BasedLoopSpace x) I 0 a (boundaryOne I intervalChain)) = 0 := by
  simp only [intervalChain_boundary, map_sub, crossProductTriangle_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

/-- Evaluation of an actual one-chain crossed with the interval. -/
def suspensionOne (x : X) : Chains (BasedLoopSpace x) 1 →ₗ[ℤ] Chains X 2 :=
  (inducedChain (evaluation x) 2).comp
    (integerBilinearRightApply (crossProductEdge (BasedLoopSpace x) I 1) intervalChain)

@[simp] theorem suspensionOne_apply (x : X) (a : Chains (BasedLoopSpace x) 1) :
    suspensionOne x a = inducedChain (evaluation x) 2
      (crossProductEdge (BasedLoopSpace x) I 1 a intervalChain) := rfl

/-- Evaluation of an actual two-chain crossed with the interval gives the
degree-three chain used for concatenation and homotopy. -/
def suspensionTwo (x : X) : Chains (BasedLoopSpace x) 2 →ₗ[ℤ] Chains X 3 :=
  (inducedChain (evaluation x) 3).comp
    (integerBilinearRightApply (crossProductTriangle (BasedLoopSpace x) I 1) intervalChain)

@[simp] theorem suspensionTwo_apply (x : X) (a : Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a = inducedChain (evaluation x) 3
      (crossProductTriangle (BasedLoopSpace x) I 1 a intervalChain) := rfl

/-- A one-cycle in the genuine loop space determines an actual two-cycle. -/
theorem boundaryTwo_suspensionOne_of_cycle (x : X) (a : Chains (BasedLoopSpace x) 1)
    (ha : boundaryOne (BasedLoopSpace x) a = 0) :
    boundaryTwo X (suspensionOne x a) = 0 := by
  change ((singularComplex X).d 2 1).hom (suspensionOne x a) = 0
  rw [suspensionOne_apply, ← inducedChain_boundary, crossProductEdge_boundary 0]
  change inducedChain (evaluation x) 1
    (crossProductZeroLeft (BasedLoopSpace x) I 1 (boundaryOne (BasedLoopSpace x) a)
        intervalChain -
      crossProductEdge (BasedLoopSpace x) I 0 a (boundaryOne I intervalChain)) = 0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg,
    evaluated_edge_endpoint_cancel, neg_zero]

/-- The prism boundary is exactly the suspension of the original boundary;
the two endpoint faces cancel under actual evaluation. -/
theorem boundaryThree_suspensionTwo (x : X) (a : Chains (BasedLoopSpace x) 2) :
    ((singularComplex X).d 3 2).hom (suspensionTwo x a) =
      suspensionOne x (boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← inducedChain_boundary, crossProductTriangle_boundary 0]
  change inducedChain (evaluation x) 2
    (crossProductEdge (BasedLoopSpace x) I 1 (boundaryTwo (BasedLoopSpace x) a)
        intervalChain +
      crossProductTriangle (BasedLoopSpace x) I 0 a (boundaryOne I intervalChain)) = _
  rw [map_add, evaluated_triangle_endpoint_cancel, add_zero]
  rfl

end Wikipedia.HopfProblem.SecondHurewicz
