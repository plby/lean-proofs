import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelOneCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelOneSurjective
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsExact
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyCoordinatesHomology

/-!
# Exact integral degree-one specialization in the original marking

The actual marked collapse is surjective on first singular homology by
the geometric base section.  Its genuine monodromy homotopy annihilates
the monodromy-difference image.  The integral quotient and the actual
target are both free of rank two, so there are no further relations.
Everything is proved at the original positive radius from holomorphic
period data; no fibre marking or property of the desired map is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology
open SpecializationCoinvariants

/-- The original source-coordinate homeomorphism followed by the fixed positive-loop marking. -/
def sourceH1Coordinates (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SingularHomology (SourceModel C₀) 1 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (sourceCoordinateTorusHomologyEquiv C₀ 1).trans coordinateTorusH1Coordinates

/-- The same original source shear acts by the literal cusp matrix in degree one. -/
theorem sourceH1Coordinates_shear (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (a : SingularHomology (SourceModel C₀) 1) :
    sourceH1Coordinates C₀ (singularHomologyMap (sourceShear C₀) 1 a) =
      M₀ *ᵥ sourceH1Coordinates C₀ a := by
  change coordinateTorusH1Coordinates
    (sourceCoordinateTorusHomologyEquiv C₀ 1 (singularHomologyMap (sourceShear C₀) 1 a)) = _
  rw [sourceCoordinateTorusHomologyEquiv_shear, coordinateTorusH1Coordinates_matrix]
  rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC in
/-- The actual integral kernel is precisely the image of the actual cusp
monodromy minus identity, on the one original marked four-torus. -/
theorem markedCollapse_homology_one_kernel :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 1) =
      LinearMap.range (torusDifference 1) := by
  let := centralSingularH1_free C r hr hC
  let := centralSingularH1_finite C r hr hC
  exact kernel_eq_of_quotient_equiv (LinearMap.range (torusDifference 1))
    torusOneCoinvariantEquiv (singularHomologyMap (markedCollapse C r hr) 1)
    (markedCollapse_homology_one_surjective C r hr hC)
    (markedCollapse_homology_range_variation C r hr 1)
    (centralSingularH1_finrank C r hr hC)

include hC in
/-- The kernel statement as an equality of actual singular-homology classes. -/
theorem markedCollapse_homology_one_eq_zero_iff
    (a : SingularHomology (ProductTorus 4) 1) :
    singularHomologyMap (markedCollapse C r hr) 1 a = 0 ↔
      ∃ b : SingularHomology (ProductTorus 4) 1,
        singularHomologyMap (torusMatrixMap M₀) 1 b - b = a := by
  change a ∈ LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 1) ↔ _
  rw [markedCollapse_homology_one_kernel C r hr hC]
  rfl

include hC in
/-- Exact integer coordinates use the fixed positive coordinate loops,
with no change of source marking depending on the specialization. -/
theorem markedCollapse_homology_one_eq_zero_iff_coordinates
    (a : SingularHomology (ProductTorus 4) 1) :
    singularHomologyMap (markedCollapse C r hr) 1 a = 0 ↔
      ∃ v : Fin 4 → ℤ, M₀ *ᵥ v - v = coordinateTorusH1Coordinates a := by
  change a ∈ LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 1) ↔ _
  rw [markedCollapse_homology_one_kernel C r hr hC]
  simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using torusDifference_one_mem_range_iff a

include hC in
theorem markedCollapse_homology_one_eq_zero_iff_first_coordinates
    (a : SingularHomology (ProductTorus 4) 1) :
    singularHomologyMap (markedCollapse C r hr) 1 a = 0 ↔
      coordinateTorusH1Coordinates a 0 = 0 ∧ coordinateTorusH1Coordinates a 1 = 0 := by
  change a ∈ LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 1) ↔ _
  rw [markedCollapse_homology_one_kernel C r hr hC]
  exact torusDifference_one_range_iff a

/-- The quotient isomorphism is induced by the actual specialization map. -/
def markedCollapseH1CoinvariantEquiv :
    TorusCoinvariants 1 ≃ₗ[ℤ] SingularHomology (QuotientCentralFibre C r) 1 := by
  let := centralSingularH1_free C r hr hC
  let := centralSingularH1_finite C r hr hC
  exact quotientLiftEquiv (LinearMap.range (torusDifference 1)) torusOneCoinvariantEquiv
    (singularHomologyMap (markedCollapse C r hr) 1)
    (markedCollapse_homology_one_surjective C r hr hC)
    (markedCollapse_homology_range_variation C r hr 1)
    (centralSingularH1_finrank C r hr hC)

/-- On the canonical quotient class its forward map is exactly the actual induced map. -/
@[simp] theorem markedCollapseH1CoinvariantEquiv_mk
    (a : SingularHomology (ProductTorus 4) 1) :
    markedCollapseH1CoinvariantEquiv C r hr hC (Submodule.Quotient.mk a) =
      singularHomologyMap (markedCollapse C r hr) 1 a := rfl

/-- Target coordinates are induced by the actual quotient isomorphism;
the positive coordinate-loop marking on the source remains fixed. -/
def markedCollapseH1Coordinates :
    SingularHomology (QuotientCentralFibre C r) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (markedCollapseH1CoinvariantEquiv C r hr hC).symm.trans torusOneCoinvariantEquiv

/-- The two surviving coordinates of the actual map, in the original source order. -/
@[simp] theorem markedCollapseH1Coordinates_collapse
    (a : SingularHomology (ProductTorus 4) 1) :
    markedCollapseH1Coordinates C r hr hC
      (singularHomologyMap (markedCollapse C r hr) 1 a) =
      oneProjection (coordinateTorusH1Coordinates a) := by
  change torusOneCoinvariantEquiv
    ((markedCollapseH1CoinvariantEquiv C r hr hC).symm
      (markedCollapseH1CoinvariantEquiv C r hr hC (Submodule.Quotient.mk a))) = _
  rw [LinearEquiv.symm_apply_apply, torusOneCoinvariantEquiv_mk]

include hC in
/-- Surjectivity and exact integral kernel for the same actual marked map. -/
theorem markedCollapse_singularH1 :
    Function.Surjective (singularHomologyMap (markedCollapse C r hr) 1) ∧
      LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 1) =
        LinearMap.range (singularHomologyMap (torusMatrixMap M₀) 1 - LinearMap.id) :=
  ⟨markedCollapse_homology_one_surjective C r hr hC,
    markedCollapse_homology_one_kernel C r hr hC⟩

include hC in
/-- The degree-one name consistent with the other marked specialization degrees. -/
theorem markedCollapse_homologyOne_surjective :
    Function.Surjective (singularHomologyMap (markedCollapse C r hr) 1) :=
  markedCollapse_homology_one_surjective C r hr hC

include hC in
theorem markedCollapse_homologyOne_kernel :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 1) =
      LinearMap.range (torusDifference 1) :=
  markedCollapse_homology_one_kernel C r hr hC

include hC in
theorem markedCollapse_homologyOne_eq_zero_iff
    (a : SingularHomology (ProductTorus 4) 1) :
    singularHomologyMap (markedCollapse C r hr) 1 a = 0 ↔
      ∃ v : Fin 4 → ℤ, M₀ *ᵥ v - v = coordinateTorusH1Coordinates a :=
  markedCollapse_homology_one_eq_zero_iff_coordinates C r hr hC a

theorem markedCollapseH1Coordinates_homology
    (a : SingularHomology (ProductTorus 4) 1) :
    markedCollapseH1Coordinates C r hr hC
      (singularHomologyMap (markedCollapse C r hr) 1 a) =
      oneProjection (coordinateTorusH1Coordinates a) :=
  markedCollapseH1Coordinates_collapse C r hr hC a

include hC in
/-- The same exact integral formula holds on the original free source quotient. -/
theorem sourceCollapse_homologyOne_eq_zero_iff
    (a : SingularHomology (SourceModel (C 0)) 1) :
    singularHomologyMap (sourceCollapse C r hr) 1 a = 0 ↔
      ∃ v : Fin 4 → ℤ, M₀ *ᵥ v - v = sourceH1Coordinates (C 0) a := by
  rw [← markedCollapse_homology_source C r hr 1 a]
  exact markedCollapse_homologyOne_eq_zero_iff C r hr hC
    (homeomorphHomologyEquiv (sourceCoordinateTorusHomeomorph (C 0)) 1 a)

include hC in
/-- Before taking coordinates, the exact source kernel is the actual shear-difference image. -/
theorem sourceCollapse_homologyOne_kernel :
    LinearMap.ker (singularHomologyMap (sourceCollapse C r hr) 1) =
      LinearMap.range (singularHomologyMap (sourceShear (C 0)) 1 - LinearMap.id) := by
  ext a
  change singularHomologyMap (sourceCollapse C r hr) 1 a = 0 ↔ _
  rw [sourceCollapse_homologyOne_eq_zero_iff C r hr hC]
  have ht (b : SingularHomology (SourceModel (C 0)) 1) :
      sourceH1Coordinates (C 0)
        (singularHomologyMap (sourceShear (C 0)) 1 b - b) =
          oneDifference (sourceH1Coordinates (C 0) b) := by
    rw [map_sub, sourceH1Coordinates_shear]
    simp only [oneDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  have he := (mem_range_iff_of_intertwines (sourceH1Coordinates (C 0))
    (singularHomologyMap (sourceShear (C 0)) 1 - LinearMap.id) oneDifference ht a).symm
  simpa only [LinearMap.mem_range, oneDifference, Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec] using he

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
