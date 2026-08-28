import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorusPullback
import Wikipedia.HopfProblem.CuspCentralCohomologyTransport
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMarkedExistence

/-!
# Specialization of the actual base-torus dual class

The base-torus class is defined on the actual central fibre by its
actual base projection.  Its normalization by the actual geometric
homology basis is proved in the imported files.  The actual complex-fibre
comparison homotopy therefore gives the displayed specialization
`sp²(TB∨) = γu`, with one genuine marking for every degree and every
containing closed-tube radius.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction CuspControlledRetraction
open SingularCohomologyFree PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

section Transport

variable {X : Type} [TopologicalSpace X] (E : ProductTorus 4 ≃ₜ X)
    (f : C(X, QuotientCentralFibre C r))
    (h : (markedCollapse C r hr).Homotopic (f.comp (E : C(ProductTorus 4, X))))

include h in
/-- The equality is between actual native singular cohomology classes. -/
theorem baseTorusDualClass_specialization_pullback :
    homeomorphCohomologyEquiv E 2
        (singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC)) =
      coordinateTorusH2DualClass 0 := by
  rw [markedSpecialization_pullback C r hr E f h 2,
    baseTorusDualClass_markedPullback C r hr hC]

include h in
theorem baseTorusDualClass_specialization_coordinates :
    coordinateTorusH2CohomologyCoordinates
        (homeomorphCohomologyEquiv E 2
          (singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC))) =
      ![1, 0, 0, 0, 0, 0] := by
  rw [markedSpecialization_pullback C r hr E f h 2]
  exact baseTorusDualClass_markedPullback_coordinateVector C r hr hC

end Transport

include hC in
/-- For every sufficiently small actual complex fibre, the genuine
base-torus dual specializes to the first period two-class. -/
theorem exists_actual_baseTorus_specialization :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀), η₀ < r ∧ η₀ < 1 ∧
      ∀ (t : ℂ) (ht : t ≠ 0), ‖t‖ ≤ η₀ →
        ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t,
          ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
            ∃ hc : Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη),
              let f : C(ActualQuotientFibre C r t, QuotientCentralFibre C r) :=
                ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩
              homeomorphCohomologyEquiv E 2
                  (singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC)) =
                coordinateTorusH2DualClass 0 ∧
              coordinateTorusH2CohomologyCoordinates
                  (homeomorphCohomologyEquiv E 2
                    (singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC))) =
                ![1, 0, 0, 0, 0, 0] := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hmodels⟩ :=
    exists_original_marked_specialization_models C r hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro t ht ht₀
  obtain ⟨E, hE⟩ := hmodels t ht ht₀
  refine ⟨E, ?_⟩
  intro η hη htη hηr
  obtain ⟨hc, hh, _⟩ := hE η hη htη hηr
  let f : C(ActualQuotientFibre C r t, QuotientCentralFibre C r) :=
    ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩
  exact ⟨hc, baseTorusDualClass_specialization_pullback C r hr hC E f hh,
    baseTorusDualClass_specialization_coordinates C r hr hC E f hh⟩

end Wikipedia.HopfProblem.CuspCentralCohomology
