import Wikipedia.HopfProblem.CuspCentralCohomologyDoubleCurvesBasic
import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorusCycle
import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesFixed
import Wikipedia.HopfProblem.CuspCentralCohomologyMarked

/-!
# The two pure coefficients of the actual double-curve pullbacks

The native cohomology pullback of each named double-curve dual has zero
coefficients at the pure base and pure phase minors.  The base statement
uses the actual marked collapse on the first coordinate two-torus and the
geometric dual pairing.  The phase statement follows from the proved
monodromy invariance of the actual native pullback.

These statements concern the original ordered-minor marking.  No mixed
coefficient or desired specialization matrix is assumed here.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction CuspCentralHomology
open CuspCentralHomology.SpecializationModel
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

/-- The pure base coefficient of any actual pullback is its pairing with
the actual base-torus fundamental class. -/
theorem markedCollapse_pullback_coordinate_zero
    (a : SingularCohomology (QuotientCentralFibre C r) 2) :
    coordinateTorusH2CohomologyCoordinates
        (singularCohomologyPullback (markedCollapse C r hr) 2 a) 0 =
      singularEvaluation (QuotientCentralFibre C r) 2 a (baseTorusH2Class C r hr) := by
  change coordinateTorusCohomologyCoordinates 2 coordinateTorusH2Coordinates _ 0 = _
  rw [coordinateTorusCohomologyCoordinates_apply_coordinate,
    singularEvaluation_naturality, markedCollapse_baseCoordinateH2Class]

/-- Every native pullback has zero pure phase coefficient, by actual
monodromy invariance in the original positive-loop marking. -/
theorem markedCollapse_pullback_coordinate_five
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (a : SingularCohomology (QuotientCentralFibre C r) 2) :
    coordinateTorusH2CohomologyCoordinates
      (singularCohomologyPullback (markedCollapse C r hr) 2 a) 5 = 0 := by
  exact ((coordinateTorusH2_pullback_fixed_iff _).mp
    ((markedPullback_mem_range_iff_fixed C r hr hC 2 _).mp ⟨a, rfl⟩)).2

variable (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- Each actual pulled-back curve dual vanishes on the original pure
base two-cycle, whose image is the literal base-torus class. -/
theorem doubleCurveDualClass_pullback_evaluate_pureBase (j : Fin 3) :
    singularEvaluation (ProductTorus 4) 2
      (singularCohomologyPullback (markedCollapse C r hr) 2
        (doubleCurveDualClass C r hr hr1 hC hR j))
      (coordinateTorusH2Coordinates.symm (Pi.single 0 1)) = 0 := by
  rw [singularEvaluation_naturality, markedCollapse_baseCoordinateH2Class,
    doubleCurveDualClass_evaluate_base]

/-- The `γu` coefficient of each actual pulled-back curve dual is zero. -/
theorem doubleCurveDualClass_pullback_coordinate_zero (j : Fin 3) :
    coordinateTorusH2CohomologyCoordinates
      (singularCohomologyPullback (markedCollapse C r hr) 2
        (doubleCurveDualClass C r hr hr1 hC hR j)) 0 = 0 := by
  rw [markedCollapse_pullback_coordinate_zero, doubleCurveDualClass_evaluate_base]

/-- The `wδ` coefficient of each actual pulled-back curve dual is zero. -/
theorem doubleCurveDualClass_pullback_coordinate_five (j : Fin 3) :
    coordinateTorusH2CohomologyCoordinates
      (singularCohomologyPullback (markedCollapse C r hr) 2
        (doubleCurveDualClass C r hr hr1 hC hR j)) 5 = 0 :=
  markedCollapse_pullback_coordinate_five C r hr hC _

/-- The same pure phase vanishing as evaluation on the actual sixth
ordered-minor homology generator. -/
theorem doubleCurveDualClass_pullback_evaluate_pureFibre (j : Fin 3) :
    singularEvaluation (ProductTorus 4) 2
      (singularCohomologyPullback (markedCollapse C r hr) 2
        (doubleCurveDualClass C r hr hr1 hC hR j))
      (coordinateTorusH2Coordinates.symm (Pi.single 5 1)) = 0 := by
  rw [← coordinateTorusCohomologyCoordinates_apply_coordinate]
  exact doubleCurveDualClass_pullback_coordinate_five C r hr hr1 hC hR j

/-- Both pure coefficients vanish for each literal named double-curve dual. -/
theorem doubleCurveDualClass_pullback_pure_coordinates (j : Fin 3) :
    coordinateTorusH2CohomologyCoordinates
        (singularCohomologyPullback (markedCollapse C r hr) 2
          (doubleCurveDualClass C r hr hr1 hC hR j)) 0 = 0 ∧
      coordinateTorusH2CohomologyCoordinates
        (singularCohomologyPullback (markedCollapse C r hr) 2
          (doubleCurveDualClass C r hr hr1 hC hR j)) 5 = 0 :=
  ⟨doubleCurveDualClass_pullback_coordinate_zero C r hr hr1 hC hR j,
    doubleCurveDualClass_pullback_coordinate_five C r hr hr1 hC hR j⟩

end Wikipedia.HopfProblem.CuspCentralCohomology
