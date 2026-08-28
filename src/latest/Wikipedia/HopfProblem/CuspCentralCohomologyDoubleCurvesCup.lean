import Wikipedia.HopfProblem.CuspCentralCohomologyDoubleCurvesSpecialization
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupPairs

/-!
# The geometric double-curve formulas as native cup products

The six original degree-two coordinate-dual classes have been identified
with the genuine Alexander--Whitney cup products of the original positive
period-loop dual classes.  Consequently the already proved geometric
specialization formula is the literal native cup polynomial
`b² γ∪δ - a² u∪w + ab (γ∪w - u∪δ)`.

The actual curve indexing, the explicit source-order permutation, and
the previously computed cylinder-orientation signs are unchanged.  No
complex-orientation identification or new geometric compatibility is
assumed here.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction CuspCentralHomology
open CuspCentralHomology.SpecializationModel
open SingularCohomologyFree SingularCohomologyCup PeriodTorusHigherHomology
open PeriodTorusCohomologyCup

/-- The displayed quadratic expression in literal native cup products
of the original degree-one period-dual classes. -/
def slopeCupClass (a b : ℤ) : SingularCohomology (ProductTorus 4) 2 :=
  (b ^ 2) • cupProduct (ProductTorus 4) 1 1
      (coordinateTorusH1DualClass 0) (coordinateTorusH1DualClass 3) -
    (a ^ 2) • cupProduct (ProductTorus 4) 1 1
      (coordinateTorusH1DualClass 1) (coordinateTorusH1DualClass 2) +
    (a * b) •
      (cupProduct (ProductTorus 4) 1 1
          (coordinateTorusH1DualClass 0) (coordinateTorusH1DualClass 2) -
        cupProduct (ProductTorus 4) 1 1
          (coordinateTorusH1DualClass 1) (coordinateTorusH1DualClass 3))

/-- The equality follows from the actual cup-pair calculation on the
original marked period cycles, not from a definition of the cup product. -/
theorem slopeClass_eq_slopeCupClass (a b : ℤ) :
    slopeClass a b = slopeCupClass a b := by
  have h03 : cupProduct (ProductTorus 4) 1 1
      (coordinateTorusH1DualClass 0) (coordinateTorusH1DualClass 3) =
      coordinateTorusH2DualClass 2 := coordinateDualCup_coefficientPair 2
  have h12 : cupProduct (ProductTorus 4) 1 1
      (coordinateTorusH1DualClass 1) (coordinateTorusH1DualClass 2) =
      coordinateTorusH2DualClass 3 := coordinateDualCup_coefficientPair 3
  have h02 : cupProduct (ProductTorus 4) 1 1
      (coordinateTorusH1DualClass 0) (coordinateTorusH1DualClass 2) =
      coordinateTorusH2DualClass 1 := coordinateDualCup_coefficientPair 1
  have h13 : cupProduct (ProductTorus 4) 1 1
      (coordinateTorusH1DualClass 1) (coordinateTorusH1DualClass 3) =
      coordinateTorusH2DualClass 4 := coordinateDualCup_coefficientPair 4
  rw [slopeCupClass, h03, h12, h02, h13]
  exact slopeClass_eq_linearCombination a b

/-- The genuine cup polynomial has the established six ordered-minor coefficients. -/
theorem slopeCupClass_coordinates (a b : ℤ) :
    coordinateTorusH2CohomologyCoordinates (slopeCupClass a b) =
      slopeCoefficients a b := by
  rw [← slopeClass_eq_slopeCupClass, slopeClass_coordinates]

/-- Reindexing the actual curve rays preserves the literal cup
polynomial with the proved source-order normal convention. -/
theorem slopeCupClass_actualRay_paperOrder (j : Fin 3) :
    slopeCupClass (-ToricComponent.hexagonRay (thetaEdgeIndex (paperCurveOrder j)) 1)
        (ToricComponent.hexagonRay (thetaEdgeIndex (paperCurveOrder j)) 0) =
      slopeCupClass (-paperCurveNormal j 1) (paperCurveNormal j 0) := by
  simp only [← slopeClass_eq_slopeCupClass, slopeClass_actualRay_paperOrder]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- The pullback of each actual named curve dual is its signed native
cup polynomial under the actual marked collapse. -/
theorem doubleCurveDualClass_pullback_eq_slopeCupClass (j : Fin 3) :
    singularCohomologyPullback (markedCollapse C r hr) 2
        (doubleCurveDualClass C r hr hr1 hC hR j) =
      (-thetaEdgeOrientationSign j) •
        slopeCupClass (-ToricComponent.hexagonRay (thetaEdgeIndex j) 1)
          (ToricComponent.hexagonRay (thetaEdgeIndex j) 0) := by
  rw [doubleCurveDualClass_pullback_eq_slopeClass C r hr hr1 hC hR j,
    slopeClass_eq_slopeCupClass]

/-- The same actual pullbacks in the displayed source order, with the
already established orientation signs explicit. -/
theorem doubleCurveDualClass_pullback_cup_paperOrder (j : Fin 3) :
    singularCohomologyPullback (markedCollapse C r hr) 2
        (doubleCurveDualClass C r hr hr1 hC hR (paperCurveOrder j)) =
      (![(-1 : ℤ), -1, 1] : Fin 3 → ℤ) j •
        slopeCupClass (-paperCurveNormal j 1) (paperCurveNormal j 0) := by
  rw [doubleCurveDualClass_pullback_eq_slopeCupClass C r hr hr1 hC hR,
    paperCurveOrder_orientationSign, slopeCupClass_actualRay_paperOrder]

section Transport

variable {X : Type} [TopologicalSpace X] (E : ProductTorus 4 ≃ₜ X)
    (f : C(X, QuotientCentralFibre C r))
    (h : (markedCollapse C r hr).Homotopic (f.comp (E : C(ProductTorus 4, X))))

include h in
/-- Transport by the actual fibre marking does not change the native
cup formula or the actual geometric curve orientation. -/
theorem doubleCurveDualClass_specialization_cup (j : Fin 3) :
    homeomorphCohomologyEquiv E 2
        (singularCohomologyPullback f 2 (doubleCurveDualClass C r hr hr1 hC hR j)) =
      (-thetaEdgeOrientationSign j) •
        slopeCupClass (-ToricComponent.hexagonRay (thetaEdgeIndex j) 1)
          (ToricComponent.hexagonRay (thetaEdgeIndex j) 0) := by
  rw [doubleCurveDualClass_specialization_pullback C r hr hr1 hC hR E f h j,
    slopeClass_eq_slopeCupClass]

include h in
/-- The literal native cup formula in the source's displayed order,
with its actual permutation and cylinder signs retained. -/
theorem doubleCurveDualClass_specialization_cup_paperOrder (j : Fin 3) :
    homeomorphCohomologyEquiv E 2
        (singularCohomologyPullback f 2
          (doubleCurveDualClass C r hr hr1 hC hR (paperCurveOrder j))) =
      (![(-1 : ℤ), -1, 1] : Fin 3 → ℤ) j •
        slopeCupClass (-paperCurveNormal j 1) (paperCurveNormal j 0) := by
  rw [doubleCurveDualClass_specialization_paperOrder C r hr hr1 hC hR E f h j,
    slopeClass_eq_slopeCupClass]

end Transport

end Wikipedia.HopfProblem.CuspCentralCohomology
