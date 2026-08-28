import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductTriangle
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProductUnit
import Wikipedia.HopfProblem.FirstHurewiczPathChains

/-!
# Right endpoint factors in the second Hurewicz prism

The right degree-zero factor of the actual triangle cross product is
literal point insertion. This lets the two endpoint terms cancel when
evaluating a family of based loops.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SecondHurewicz

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

theorem crossProductTriangle_zero_eq_zeroRight :
    crossProductTriangle X Y 0 = crossProductZeroRight X Y 2 := by
  apply chainBilinearMap_ext X Y 2 0
  intro σ τ
  rw [crossProductTriangle_simplex, formalTriangleCrossProduct_zero_simplex_right,
    formalMap_simplex, productAffineChainMap_simplex, inducedChain_simplex,
    crossProductZeroRight_simplex]
  apply congrArg (simplexChain (X × Y) 2)
  change (σ.prodMap τ).comp
      (productAffineSimplex (fun i => (stdVertices 2 i, stdVertices 0 0))) =
    (crossInsertRight (zeroSimplexValue τ)).comp σ
  rw [productAffineSimplex_point_right, affineSimplex_stdVertices, ContinuousMap.comp_id]
  rfl

theorem crossProductTriangle_point_right (a : Chains X 2) (y : Y) :
    crossProductTriangle X Y 0 a (pointChain y) =
      inducedChain (crossInsertRight y) 2 a := by
  rw [crossProductTriangle_zero_eq_zeroRight, pointChain,
    crossProductZeroRight_simplex_right]
  rfl

theorem crossProductEdge_point_right (a : Chains X 1) (y : Y) :
    crossProductEdge X Y 0 a (pointChain y) =
      inducedChain (crossInsertRight y) 1 a := by
  rw [pointChain, crossProductEdge_zero_simplex_right]
  rfl

end Wikipedia.HopfProblem.SecondHurewicz
