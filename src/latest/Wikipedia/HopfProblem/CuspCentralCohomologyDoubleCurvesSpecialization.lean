import Wikipedia.HopfProblem.CuspCentralCohomologyDoubleCurvesMixed
import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorusSpecialization
import Wikipedia.HopfProblem.CuspCentralCohomology
import Wikipedia.HopfProblem.CuspCentralCohomologySlopeSourceOrder
import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryExistence

/-!
# Specialization of the actual geometric degree-two basis

The target classes are dual to the literal named double-curve
fundamental classes and the actual base-torus class.  The source classes
use the native evaluation-dual period marking.  The geometric mixed
calculation and the actual complex-fibre comparison give all four
specialization formulas in one and the same marking.  That same marking
identifies the endpoint of a constructed continuous circle transport
with the original monodromy matrix.

The normals below are the normals of the actual indexed toric rays.
No unproved identification with a different ordering of the three
curves, or with their complex-orientation convention, is made.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction CuspControlledRetraction CuspCentralHomology
open SingularCohomologyFree PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

section Transport

variable {X : Type} [TopologicalSpace X] (E : ProductTorus 4 ≃ₜ X)
    (f : C(X, QuotientCentralFibre C r))
    (h : (markedCollapse C r hr).Homotopic (f.comp (E : C(ProductTorus 4, X))))

include h in
/-- Exact native pullback of the independently normalized named curve
dual, transported by the actual fibre homeomorphism. -/
theorem doubleCurveDualClass_specialization_pullback (j : Fin 3) :
    homeomorphCohomologyEquiv E 2
        (singularCohomologyPullback f 2 (doubleCurveDualClass C r hr hr1 hC hR j)) =
      (-thetaEdgeOrientationSign j) •
        slopeClass (-ToricComponent.hexagonRay (thetaEdgeIndex j) 1)
          (ToricComponent.hexagonRay (thetaEdgeIndex j) 0) := by
  rw [markedSpecialization_pullback C r hr E f h 2,
    doubleCurveDualClass_pullback_eq_slopeClass C r hr hr1 hC hR j]

include h in
/-- The coordinate polynomial has the sign fixed by the actual
oriented suspension-cylinder fundamental class. -/
theorem doubleCurveDualClass_specialization_coordinates (j : Fin 3) :
    coordinateTorusH2CohomologyCoordinates
        (homeomorphCohomologyEquiv E 2
          (singularCohomologyPullback f 2 (doubleCurveDualClass C r hr hr1 hC hR j))) =
      (-thetaEdgeOrientationSign j) •
        slopeCoefficients (-ToricComponent.hexagonRay (thetaEdgeIndex j) 1)
          (ToricComponent.hexagonRay (thetaEdgeIndex j) 0) := by
  rw [doubleCurveDualClass_specialization_pullback C r hr hr1 hC hR E f h j,
    map_zsmul, slopeClass_coordinates]

include h in
/-- The same genuine classes in the source's displayed ray order
`w,δ-w,-δ`, with its index permutation and orientation signs explicit. -/
theorem doubleCurveDualClass_specialization_paperOrder (j : Fin 3) :
    homeomorphCohomologyEquiv E 2
        (singularCohomologyPullback f 2
          (doubleCurveDualClass C r hr hr1 hC hR (paperCurveOrder j))) =
      (![(-1 : ℤ), -1, 1] : Fin 3 → ℤ) j •
        slopeClass (-paperCurveNormal j 1) (paperCurveNormal j 0) := by
  rw [doubleCurveDualClass_specialization_pullback C r hr hr1 hC hR E f h,
    paperCurveOrder_orientationSign, slopeClass_actualRay_paperOrder]

end Transport

/-- All native cohomology image statements and all four geometric
degree-two specialization formulas hold in one constructed marking of
each sufficiently small actual complex fibre. -/
theorem exists_actual_geometric_specialization :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀), η₀ < r ∧ η₀ < 1 ∧
      ∀ (t : ℂ) (ht : t ≠ 0), ‖t‖ ≤ η₀ →
        ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t,
          HasMarkedCircleTransport C r t E ∧
          ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
            ∃ hc : Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη),
              let f : C(ActualQuotientFibre C r t, QuotientCentralFibre C r) :=
                ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩
              (∀ n : ℕ, Function.Injective (singularCohomologyPullback f n) ∧
                LinearMap.range (singularCohomologyPullback f n) =
                  singularCohomologyFixed (markedFibreMonodromy E) n) ∧
              homeomorphCohomologyEquiv E 2
                  (singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC)) =
                coordinateTorusH2DualClass 0 ∧
              ∀ j : Fin 3,
                homeomorphCohomologyEquiv E 2
                    (singularCohomologyPullback f 2 (doubleCurveDualClass C r hr hr1 hC hR j)) =
                  (-thetaEdgeOrientationSign j) •
                    slopeClass (-ToricComponent.hexagonRay (thetaEdgeIndex j) 1)
                      (ToricComponent.hexagonRay (thetaEdgeIndex j) 0) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hmodels⟩ :=
    exists_original_marked_circle_specialization_models C r hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro t ht ht₀
  obtain ⟨E, hcircle, hE⟩ := hmodels t ht ht₀
  refine ⟨E, hcircle, ?_⟩
  intro η hη htη hηr
  obtain ⟨hc, hh, _⟩ := hE η hη htη hηr
  let f : C(ActualQuotientFibre C r t, QuotientCentralFibre C r) :=
    ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro n
    exact ⟨markedSpecialization_pullback_injective C r hr hC E f hh n,
      markedSpecialization_pullback_range C r hr hC E f hh n⟩
  · exact baseTorusDualClass_specialization_pullback C r hr hC E f hh
  · exact doubleCurveDualClass_specialization_pullback C r hr hr1 hC hR E f hh

end Wikipedia.HopfProblem.CuspCentralCohomology
