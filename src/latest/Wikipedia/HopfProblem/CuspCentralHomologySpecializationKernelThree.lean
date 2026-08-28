import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelMap
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusThreeFour
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariants
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyCoordinatesHomology
import Wikipedia.HopfProblem.CuspCentralHomologyMiddle

/-!
# The actual degree-three specialization kernel

Actual Mayer–Vietoris naturality supplies the geometric surjectivity, and
the genuine compensated rotation supplies monodromy invariance.  The
proved integral coinvariant quotient and the actual central-fibre rank
then give precisely the exterior-cube monodromy relations, at the original
ambient radius.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior SpecializationCoinvariants

/-- The original exterior-cube marking intertwines the actual torus difference. -/
theorem torusDifference_three_exterior (a : SingularHomology (ProductTorus 4) 3) :
    coordinateTorusH3ExteriorEquiv (torusDifference 3 a) =
      exteriorCubeDifference (coordinateTorusH3ExteriorEquiv a) := by
  change coordinateTorusH3ExteriorEquiv
    (singularHomologyMap (torusMatrixMap M₀) 3 a - a) =
      exteriorPower.map 3 M₀.mulVecLin (coordinateTorusH3ExteriorEquiv a) -
        coordinateTorusH3ExteriorEquiv a
  rw [map_sub, coordinateTorusH3ExteriorEquiv_matrix]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))

include hC

/-- The actual marked collapse surjects on integral third homology,
with smallness derived from the original holomorphic data. -/
theorem markedCollapse_homologyThree_surjective :
    Function.Surjective (singularHomologyMap (markedCollapse C ε hε) 3) :=
  markedCollapse_homology_surjective_of_product C ε hε 3
    (productCollapse_homologyThree_surjective_of_holomorphic C ε hε hC)

/-- Exact actual single-monodromy relations in third singular homology. -/
theorem markedCollapse_homologyThree_kernel :
    LinearMap.ker (singularHomologyMap (markedCollapse C ε hε) 3) =
      LinearMap.range (torusDifference 3) := by
  let := centralSingularH3_free C ε hε hC
  let := centralSingularH3_finite C ε hε hC
  exact torusThree_kernel_eq_of_invariant _
    (markedCollapse_homologyThree_surjective C ε hε hC)
    (markedCollapse_homology_invariant C ε hε 3)
    (centralSingularH3_finrank C ε hε hC)

/-- Pointwise integral form in the original exterior-cube marking. -/
theorem markedCollapse_homologyThree_eq_zero_iff
    (a : SingularHomology (ProductTorus 4) 3) :
    singularHomologyMap (markedCollapse C ε hε) 3 a = 0 ↔
      ∃ v : latticeExterior 3,
        exteriorPower.map 3 M₀.mulVecLin v - v = coordinateTorusH3ExteriorEquiv a := by
  change a ∈ LinearMap.ker (singularHomologyMap (markedCollapse C ε hε) 3) ↔
    coordinateTorusH3ExteriorEquiv a ∈ LinearMap.range exteriorCubeDifference
  rw [markedCollapse_homologyThree_kernel C ε hε hC]
  exact mem_range_iff_of_intertwines coordinateTorusH3ExteriorEquiv
    (torusDifference 3) exteriorCubeDifference torusDifference_three_exterior a

/-- The same exact integral relations hold on the original free-source quotient. -/
theorem sourceCollapse_homologyThree_eq_zero_iff
    (a : SingularHomology (SourceModel (C 0)) 3) :
    singularHomologyMap (sourceCollapse C ε hε) 3 a = 0 ↔
      ∃ v : latticeExterior 3,
        exteriorPower.map 3 M₀.mulVecLin v - v = sourceH3ExteriorEquiv (C 0) a := by
  rw [← markedCollapse_homology_source C ε hε 3 a]
  exact markedCollapse_homologyThree_eq_zero_iff C ε hε hC
    (homeomorphHomologyEquiv (sourceCoordinateTorusHomeomorph (C 0)) 3 a)

/-- Actual source monodromy differences, before applying exterior coordinates. -/
theorem sourceCollapse_homologyThree_kernel :
    LinearMap.ker (singularHomologyMap (sourceCollapse C ε hε) 3) =
      LinearMap.range (singularHomologyMap (sourceShear (C 0)) 3 - LinearMap.id) := by
  ext a
  change singularHomologyMap (sourceCollapse C ε hε) 3 a = 0 ↔ _
  rw [sourceCollapse_homologyThree_eq_zero_iff C ε hε hC]
  change sourceH3ExteriorEquiv (C 0) a ∈ LinearMap.range exteriorCubeDifference ↔ _
  symm
  apply mem_range_iff_of_intertwines (sourceH3ExteriorEquiv (C 0))
  intro b
  change sourceH3ExteriorEquiv (C 0)
    (singularHomologyMap (sourceShear (C 0)) 3 b - b) =
      exteriorPower.map 3 M₀.mulVecLin (sourceH3ExteriorEquiv (C 0) b) -
        sourceH3ExteriorEquiv (C 0) b
  rw [map_sub, sourceH3ExteriorEquiv_shear]

/-- The quotient map induced by the actual third-homology collapse is an isomorphism. -/
def markedCollapseH3CoinvariantEquiv :
    TorusCoinvariants 3 ≃ₗ[ℤ] SingularHomology (QuotientCentralFibre C ε) 3 := by
  letI := centralSingularH3_free C ε hε hC
  letI := centralSingularH3_finite C ε hε hC
  exact torusThreeDescendedEquiv _
    (markedCollapse_homologyThree_surjective C ε hε hC)
    (markedCollapse_homology_range_variation C ε hε 3)
    (centralSingularH3_finrank C ε hε hC)

@[simp] theorem markedCollapseH3CoinvariantEquiv_mk
    (a : SingularHomology (ProductTorus 4) 3) :
    markedCollapseH3CoinvariantEquiv C ε hε hC (Submodule.Quotient.mk a) =
      singularHomologyMap (markedCollapse C ε hε) 3 a := rfl

/-- Integral target coordinates induced by the proved actual specialization quotient. -/
def markedCollapseH3Coordinates :
    SingularHomology (QuotientCentralFibre C ε) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (markedCollapseH3CoinvariantEquiv C ε hε hC).symm.trans torusThreeCoinvariantEquiv

/-- The actual specialization has the explicit integral cube-coinvariant projection. -/
theorem markedCollapseH3Coordinates_homology (a : SingularHomology (ProductTorus 4) 3) :
    markedCollapseH3Coordinates C ε hε hC
      (singularHomologyMap (markedCollapse C ε hε) 3 a) =
        cubeProjection (coordinateTorusH3Coordinates a) := by
  change torusThreeCoinvariantEquiv
    ((markedCollapseH3CoinvariantEquiv C ε hε hC).symm
      (singularHomologyMap (markedCollapse C ε hε) 3 a)) = _
  rw [← markedCollapseH3CoinvariantEquiv_mk C ε hε hC a,
    LinearEquiv.symm_apply_apply, torusThreeCoinvariantEquiv_mk]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
