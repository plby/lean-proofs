import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass

/-!
# The actual right-point unit of the degree-one cross product

The formal edge product with a zero-simplex is literal point insertion.
Realizing the standard affine simplex proves the same exact equality for
actual singular chains. Passing through the actual cycle-class maps gives
the corresponding unit formula on integral singular homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

/-- The constructed edge product in right degree zero is the literal
degree-zero right product, on all actual singular chains. -/
theorem crossProductEdge_zero_eq_zeroRight :
    crossProductEdge X Y 0 = crossProductZeroRight X Y 1 := by
  apply chainBilinearMap_ext X Y 1 0
  intro σ τ
  rw [crossProductEdge_simplex, formalEdgeCrossProduct_zero_simplex_right,
    formalMap_simplex, productAffineChainMap_simplex, inducedChain_simplex,
    crossProductZeroRight_simplex]
  apply congrArg (simplexChain (X × Y) 1)
  change (σ.prodMap τ).comp
      (productAffineSimplex (fun i => (stdVertices 1 i, stdVertices 0 0))) =
    (crossInsertRight (zeroSimplexValue τ)).comp σ
  rw [productAffineSimplex_point_right, affineSimplex_stdVertices, ContinuousMap.comp_id]
  rfl

/-- Multiplication by any actual zero-simplex inserts its value in the right factor. -/
theorem crossProductEdge_zero_simplex_right (a : Chains X 1)
    (τ : SingularSimplex Y 0) :
    crossProductEdge X Y 0 a (simplexChain Y 0 τ) =
      inducedChain (crossInsertRight (zeroSimplexValue τ)) 1 a := by
  rw [crossProductEdge_zero_eq_zeroRight, crossProductZeroRight_simplex_right]

/-- The actual point cycle is an exact right unit by the point-insertion chain map. -/
@[simp] theorem crossProductEdge_pointCycle_right (a : Chains X 1) (y : Y) :
    crossProductEdge X Y 0 a (pointCycle y).1 =
      inducedChain (crossInsertRight y) 1 a := by
  rw [pointCycle_val, crossProductEdge_zero_simplex_right]
  rfl

/-- The right-point unit agrees with the actual induced map already on singular cycles. -/
@[simp] theorem crossProductCycles_pointCycle_right (a : Cycle (singularComplex X) 1)
    (y : Y) :
    crossProductCycles X Y 0 a (pointCycle y) =
      mapCycles (singularChainMap (crossInsertRight y)) 1 a := by
  apply Subtype.ext
  rw [crossProductCycles_val, mapCycles_val]
  exact crossProductEdge_pointCycle_right X Y a.1 y

/-- The actual point class is a right unit via the actual inclusion of the first factor. -/
@[simp] theorem crossProductHomology_pointClass_right (a : SingularHomology X 1) (y : Y) :
    crossProductHomology X Y 0 a (pointClass y) =
      singularHomologyMap (crossInsertRight y) 1 a := by
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) 1 a
  change crossProductHomology X Y 0 (cycleClass (singularComplex X) 1 c)
      (cycleClass (singularComplex Y) 0 (pointCycle y)) = _
  rw [crossProductHomology_cycleClass, crossProductCycles_pointCycle_right]
  exact (homologyMap_cycleClass (singularChainMap (crossInsertRight y)) 1 c).symm

/-- Linear-map form of the actual right-point unit on degree-one homology. -/
theorem crossProductHomology_pointClass_right_linearMap (y : Y) :
    integerBilinearRightApply (crossProductHomology X Y 0) (pointClass y) =
      singularHomologyMap (crossInsertRight y) 1 := by
  apply LinearMap.ext
  intro a
  exact crossProductHomology_pointClass_right X Y a y

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
