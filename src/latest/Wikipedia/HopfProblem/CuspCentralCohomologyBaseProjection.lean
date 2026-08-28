import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusHomology
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelMap
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingProductTorus

/-!
# The actual base projection in the original period marking

The source coordinates are ordered `(β₀, β₁, α₀, α₁)`.  The genuine
central base projection composed with the genuine marked specialization
is the literal projection to the first two circle coordinates.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap Matrix

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspCentralHomology CuspCentralHomology.SpecializationModel
open SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior LocalSystemMatrices
open FirstHurewicz PeriodTorusHigherHomologyPontryagin

/-- The two original base periods, in their original order. -/
def markedBaseProjection : C(ProductTorus 4, ProductTorus 2) where
  toFun x := ![x 0, x 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> exact continuous_apply _

@[simp] theorem markedBaseProjection_apply (x : ProductTorus 4) :
    markedBaseProjection x = ![x 0, x 1] := rfl

/-- The actual first-coordinate two-subtorus. -/
def markedBaseInclusion : C(ProductTorus 2, ProductTorus 4) where
  toFun x := ![x 0, x 1, 0, 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact continuous_const
    · exact continuous_const

@[simp] theorem markedBaseInclusion_apply (x : ProductTorus 2) :
    markedBaseInclusion x = ![x 0, x 1, 0, 0] := rfl

/-- The literal integral matrix of the first-coordinate inclusion. -/
def markedBaseInclusionMatrix : Matrix (Fin 4) (Fin 2) ℤ :=
  !![1, 0; 0, 1; 0, 0; 0, 0]

theorem markedBaseInclusion_eq_matrix :
    markedBaseInclusion = torusMatrixMap markedBaseInclusionMatrix := by
  apply ContinuousMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [markedBaseInclusion_apply, torusMatrixMap_apply,
      markedBaseInclusionMatrix, Fin.sum_univ_two]

/-- Projecting and reinserting forgets exactly the two phase coordinates. -/
def markedBaseIdempotentMatrix : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem markedBaseInclusion_comp_projection :
    markedBaseInclusion.comp markedBaseProjection =
      torusMatrixMap markedBaseIdempotentMatrix := by
  apply ContinuousMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [markedBaseInclusion_apply, markedBaseProjection_apply,
      torusMatrixMap_apply, markedBaseIdempotentMatrix, Fin.sum_univ_four]

/-- The ordered minor `β₀ ∧ β₁` is retained by the actual projection matrix. -/
theorem markedBaseIdempotentMatrix_square_first (v : Fin 6 → ℤ) :
    (exteriorSquare markedBaseIdempotentMatrix *ᵥ v) 0 = v 0 := by
  have hrow : exteriorSquare markedBaseIdempotentMatrix 0 = Pi.single 0 1 := by decide
  change (∑ j, exteriorSquare markedBaseIdempotentMatrix 0 j * v j) = v 0
  rw [hrow]
  simp [Pi.single_apply]

/-- Every integral two-torus class is its marked multiple of the
already normalized actual top class. -/
theorem baseTorusH2_eq_smul_topClass (a : SingularHomology (ProductTorus 2) 2) :
    a = baseTorusH2Marking a • productTorusTopClass 2 := by
  apply baseTorusH2Marking.injective
  simp

private theorem matrix_two_topClass (A : Matrix (Fin 4) (Fin 2) ℤ) :
    singularHomologyMap (torusMatrixMap A) 2 (productTorusTopClass 2) =
      coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 (fun j => A *ᵥ Pi.single j 1)) := by
  rw [productTorusTopClass_two,
    product_natural _ (torusMatrixMap_add A),
    coordinateTorusWedgeTwo_apply_ιMulti_periodLoops (Elliptic.examplePeriod .four)]
  rw [singularHomologyMap_one, torusMatrixMap_coordinatePeriodHomology,
    torusMatrixMap_coordinatePeriodHomology]

private theorem markedBaseInclusionMatrix_columns :
    (fun j : Fin 2 => markedBaseInclusionMatrix *ᵥ Pi.single j 1) =
      latticeBasis ∘ pairIndices 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [markedBaseInclusionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      latticeBasis, pairIndices, Pi.basisFun_apply, Pi.single_apply]

/-- The actual top class maps to the positively ordered product of the
two original base-period loops. -/
theorem markedBaseInclusion_topClass :
    singularHomologyMap markedBaseInclusion 2 (productTorusTopClass 2) =
      coordinateTorusWedgeTwo (squareBasis 0) := by
  rw [markedBaseInclusion_eq_matrix, matrix_two_topClass,
    markedBaseInclusionMatrix_columns, squareBasis_apply]

theorem markedBaseInclusion_topClass_coordinates :
    coordinateTorusH2Coordinates
      (singularHomologyMap markedBaseInclusion 2 (productTorusTopClass 2)) =
        Pi.single 0 1 := by
  rw [markedBaseInclusion_topClass]
  change squareCoordinates (coordinateTorusH2ExteriorEquiv
    (coordinateTorusWedgeTwo (squareBasis 0))) = _
  rw [coordinateTorusH2ExteriorEquiv_wedge]
  ext i
  simp [squareCoordinates_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The comparison holds for every actual integral two-torus class. -/
theorem markedBaseInclusion_homology_coordinates
    (a : SingularHomology (ProductTorus 2) 2) :
    coordinateTorusH2Coordinates (singularHomologyMap markedBaseInclusion 2 a) =
      baseTorusH2Marking a • Pi.single 0 1 := by
  conv_lhs => rw [baseTorusH2_eq_smul_topClass a]
  rw [map_zsmul, map_zsmul, markedBaseInclusion_topClass_coordinates]

theorem markedBaseInclusion_homology_coordinate_zero
    (a : SingularHomology (ProductTorus 2) 2) :
    coordinateTorusH2Coordinates (singularHomologyMap markedBaseInclusion 2 a) 0 =
      baseTorusH2Marking a := by
  rw [markedBaseInclusion_homology_coordinates]
  simp

/-- The actual base projection evaluates precisely the first ordered
exterior coordinate, with its integral top-class normalization. -/
theorem baseTorusH2Marking_markedBaseProjection
    (a : SingularHomology (ProductTorus 4) 2) :
    baseTorusH2Marking (singularHomologyMap markedBaseProjection 2 a) =
      coordinateTorusH2Coordinates a 0 := by
  have h := congrArg
    (fun f : C(ProductTorus 4, ProductTorus 4) => singularHomologyMap f 2 a)
    markedBaseInclusion_comp_projection
  rw [singularHomologyMap_comp] at h
  have hc := congrArg (fun z => coordinateTorusH2Coordinates z 0) h
  change coordinateTorusH2Coordinates
    (singularHomologyMap markedBaseInclusion 2
      (singularHomologyMap markedBaseProjection 2 a)) 0 = _ at hc
  rw [markedBaseInclusion_homology_coordinate_zero, coordinateTorusH2Coordinates_matrix,
    markedBaseIdempotentMatrix_square_first] at hc
  exact hc

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- This is an equality of actual continuous maps, before applying
homology or cohomology. -/
theorem baseTorusProjectionMap_comp_markedCollapse :
    (baseTorusProjectionMap C r hr hC).comp (markedCollapse C r hr) =
      markedBaseProjection := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨p, rfl⟩ := sourceProductCoordinateHomeomorph.surjective x
  rw [markedCollapse_eq_product]
  change baseTorusProjection C r hr
    (productCollapse C r hr
      (sourceProductCoordinateHomeomorph.symm (sourceProductCoordinateHomeomorph p))) = _
  rw [Homeomorph.symm_apply_apply, baseTorusProjection_productCollapse,
    sourceProductCoordinateHomeomorph_apply]
  funext i
  fin_cases i <;> rfl

/-- Applying the genuine geometric base functional after actual marked
specialization returns the original `β₀ ∧ β₁` coefficient. -/
theorem baseTorusH2Functional_markedCollapse
    (a : SingularHomology (ProductTorus 4) 2) :
    baseTorusH2Functional C r hr hC
      (singularHomologyMap (markedCollapse C r hr) 2 a) =
        coordinateTorusH2Coordinates a 0 := by
  change baseTorusH2Marking
    (((singularHomologyMap (baseTorusProjectionMap C r hr hC) 2).comp
      (singularHomologyMap (markedCollapse C r hr) 2)) a) = _
  rw [← singularHomologyMap_comp, baseTorusProjectionMap_comp_markedCollapse]
  exact baseTorusH2Marking_markedBaseProjection a

end Wikipedia.HopfProblem.CuspCentralCohomology
