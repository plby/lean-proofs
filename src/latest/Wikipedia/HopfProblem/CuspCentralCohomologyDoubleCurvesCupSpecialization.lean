import Wikipedia.HopfProblem.CuspCentralCohomologyDoubleCurvesCup

/-!
# Geometric specialization in native cup-product form

The already constructed actual fibre marking simultaneously realizes
physical circle transport, integral invariant cohomology in every
degree, and specialization of the geometric base and double-curve
classes.  This file expresses those same degree-two images as genuine
cup products of the original positive-loop dual classes.

The radius, actual fibre homeomorphism, and prescribed collapse are
reused from the geometric specialization theorem.  No new marking,
comparison homotopy, or geometric coefficient assumption is introduced.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction CuspControlledRetraction CuspCentralHomology
open SingularCohomologyFree SingularCohomologyCup PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel PeriodTorusCohomologyCup

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- One and the same actual complex-fibre marking gives physical
monodromy, all-degree integral invariant cohomology, and the literal
native cup formulas for the geometric degree-two basis. -/
theorem exists_actual_geometric_cup_specialization :
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
                cupProduct (ProductTorus 4) 1 1
                  (coordinateTorusH1DualClass 0) (coordinateTorusH1DualClass 1) ∧
              (∀ j : Fin 3,
                homeomorphCohomologyEquiv E 2
                    (singularCohomologyPullback f 2 (doubleCurveDualClass C r hr hr1 hC hR j)) =
                  (-thetaEdgeOrientationSign j) •
                    slopeCupClass (-ToricComponent.hexagonRay (thetaEdgeIndex j) 1)
                      (ToricComponent.hexagonRay (thetaEdgeIndex j) 0)) ∧
              ∀ j : Fin 3,
                homeomorphCohomologyEquiv E 2
                    (singularCohomologyPullback f 2
                      (doubleCurveDualClass C r hr hr1 hC hR (paperCurveOrder j))) =
                  (![(-1 : ℤ), -1, 1] : Fin 3 → ℤ) j •
                    slopeCupClass (-paperCurveNormal j 1) (paperCurveNormal j 0) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hmodels⟩ :=
    exists_actual_geometric_specialization C r hr hr1 hC hR
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro t ht ht₀
  obtain ⟨E, hcircle, hE⟩ := hmodels t ht ht₀
  refine ⟨E, hcircle, ?_⟩
  intro η hη htη hηr
  obtain ⟨hc, hall, hbase, hcurves⟩ := hE η hη htη hηr
  refine ⟨hc, hall, ?_, ?_, ?_⟩
  · simpa only [coordinateDualCup_gamma_u] using hbase
  · intro j
    rw [← slopeClass_eq_slopeCupClass]
    exact hcurves j
  · intro j
    rw [← slopeClass_eq_slopeCupClass]
    simpa only [paperCurveOrder_orientationSign, slopeClass_actualRay_paperOrder]
      using hcurves (paperCurveOrder j)

end Wikipedia.HopfProblem.CuspCentralCohomology
