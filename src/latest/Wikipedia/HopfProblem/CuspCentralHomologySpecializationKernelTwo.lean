import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelMap
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusTwo
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariants
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyCoordinatesHomology
import Wikipedia.HopfProblem.CuspCentralHomologyMiddle

/-!
# The actual degree-two specialization kernel

The original marked collapse is surjective by the geometric boundary and
base-section construction, and invariant by the genuine monodromy homotopy.
The proved free integral coinvariant quotient and the actual rank of the
central fibre then identify its kernel exactly.  No desired homology map,
surjectivity, or matrix action is assumed.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior SpecializationCoinvariants

/-- The original exterior-square marking intertwines the actual torus difference. -/
theorem torusDifference_two_exterior (a : SingularHomology (ProductTorus 4) 2) :
    coordinateTorusH2ExteriorEquiv (torusDifference 2 a) =
      exteriorSquareDifference (coordinateTorusH2ExteriorEquiv a) := by
  change coordinateTorusH2ExteriorEquiv
    (singularHomologyMap (torusMatrixMap M₀) 2 a - a) =
      exteriorPower.map 2 M₀.mulVecLin (coordinateTorusH2ExteriorEquiv a) -
        coordinateTorusH2ExteriorEquiv a
  rw [map_sub, coordinateTorusH2ExteriorEquiv_matrix]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))

include hC

/-- The actual marked collapse surjects on integral second homology at
the original radius; smallness is derived in the geometric proof. -/
theorem markedCollapse_homologyTwo_surjective :
    Function.Surjective (singularHomologyMap (markedCollapse C ε hε) 2) :=
  markedCollapse_homology_surjective_of_product C ε hε 2
    (productCollapse_homologyTwo_surjective_of_holomorphic C ε hε hC)

/-- The actual specialization kernel is exactly the actual single-monodromy image. -/
theorem markedCollapse_homologyTwo_kernel :
    LinearMap.ker (singularHomologyMap (markedCollapse C ε hε) 2) =
      LinearMap.range (torusDifference 2) := by
  let := centralSingularH2_free C ε hε hC
  let := centralSingularH2_finite C ε hε hC
  exact torusTwo_kernel_eq_of_invariant _
    (markedCollapse_homologyTwo_surjective C ε hε hC)
    (markedCollapse_homology_invariant C ε hε 2)
    (centralSingularH2_finrank C ε hε hC)

/-- Pointwise integral form in the original exterior-square marking. -/
theorem markedCollapse_homologyTwo_eq_zero_iff
    (a : SingularHomology (ProductTorus 4) 2) :
    singularHomologyMap (markedCollapse C ε hε) 2 a = 0 ↔
      ∃ v : latticeExterior 2,
        exteriorPower.map 2 M₀.mulVecLin v - v = coordinateTorusH2ExteriorEquiv a := by
  change a ∈ LinearMap.ker (singularHomologyMap (markedCollapse C ε hε) 2) ↔
    coordinateTorusH2ExteriorEquiv a ∈ LinearMap.range exteriorSquareDifference
  rw [markedCollapse_homologyTwo_kernel C ε hε hC]
  exact mem_range_iff_of_intertwines coordinateTorusH2ExteriorEquiv
    (torusDifference 2) exteriorSquareDifference torusDifference_two_exterior a

/-- The same exact integral relations hold on the original free-source quotient. -/
theorem sourceCollapse_homologyTwo_eq_zero_iff
    (a : SingularHomology (SourceModel (C 0)) 2) :
    singularHomologyMap (sourceCollapse C ε hε) 2 a = 0 ↔
      ∃ v : latticeExterior 2,
        exteriorPower.map 2 M₀.mulVecLin v - v = sourceH2ExteriorEquiv (C 0) a := by
  rw [← markedCollapse_homology_source C ε hε 2 a]
  exact markedCollapse_homologyTwo_eq_zero_iff C ε hε hC
    (homeomorphHomologyEquiv (sourceCoordinateTorusHomeomorph (C 0)) 2 a)

/-- Actual source monodromy differences, before applying exterior coordinates. -/
theorem sourceCollapse_homologyTwo_kernel :
    LinearMap.ker (singularHomologyMap (sourceCollapse C ε hε) 2) =
      LinearMap.range (singularHomologyMap (sourceShear (C 0)) 2 - LinearMap.id) := by
  ext a
  change singularHomologyMap (sourceCollapse C ε hε) 2 a = 0 ↔ _
  rw [sourceCollapse_homologyTwo_eq_zero_iff C ε hε hC]
  change sourceH2ExteriorEquiv (C 0) a ∈ LinearMap.range exteriorSquareDifference ↔ _
  symm
  apply mem_range_iff_of_intertwines (sourceH2ExteriorEquiv (C 0))
  intro b
  change sourceH2ExteriorEquiv (C 0)
    (singularHomologyMap (sourceShear (C 0)) 2 b - b) =
      exteriorPower.map 2 M₀.mulVecLin (sourceH2ExteriorEquiv (C 0) b) -
        sourceH2ExteriorEquiv (C 0) b
  rw [map_sub, sourceH2ExteriorEquiv_shear]

/-- The literal quotient map induced by the actual degree-two collapse is an isomorphism. -/
def markedCollapseH2CoinvariantEquiv :
    TorusCoinvariants 2 ≃ₗ[ℤ] SingularHomology (QuotientCentralFibre C ε) 2 := by
  letI := centralSingularH2_free C ε hε hC
  letI := centralSingularH2_finite C ε hε hC
  exact torusTwoDescendedEquiv _
    (markedCollapse_homologyTwo_surjective C ε hε hC)
    (markedCollapse_homology_range_variation C ε hε 2)
    (centralSingularH2_finrank C ε hε hC)

@[simp] theorem markedCollapseH2CoinvariantEquiv_mk
    (a : SingularHomology (ProductTorus 4) 2) :
    markedCollapseH2CoinvariantEquiv C ε hε hC (Submodule.Quotient.mk a) =
      singularHomologyMap (markedCollapse C ε hε) 2 a := rfl

/-- Integral target coordinates induced by the proved actual specialization quotient. -/
def markedCollapseH2Coordinates :
    SingularHomology (QuotientCentralFibre C ε) 2 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (markedCollapseH2CoinvariantEquiv C ε hε hC).symm.trans torusTwoCoinvariantEquiv

/-- The actual specialization has the explicit integral coinvariant projection. -/
theorem markedCollapseH2Coordinates_homology (a : SingularHomology (ProductTorus 4) 2) :
    markedCollapseH2Coordinates C ε hε hC
      (singularHomologyMap (markedCollapse C ε hε) 2 a) =
        squareProjection (coordinateTorusH2Coordinates a) := by
  change torusTwoCoinvariantEquiv
    ((markedCollapseH2CoinvariantEquiv C ε hε hC).symm
      (singularHomologyMap (markedCollapse C ε hε) 2 a)) = _
  rw [← markedCollapseH2CoinvariantEquiv_mk C ε hε hC a,
    LinearEquiv.symm_apply_apply, torusTwoCoinvariantEquiv_mk]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
