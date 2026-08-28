import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorusCup
import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryExistence

/-!
# Actual complex-fibre specialization of the native base-torus cup

The original holomorphic data provide one actual fibre marking for
physical circle transport, every integral cohomology degree, and the two
central degree-one classes and their genuine cup.  The marking is chosen
before the containing closed-tube radius.  No comparison homotopy,
circle transport, or cup-product identification is assumed here.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction CuspControlledRetraction SingularCohomologyFree
open SingularCohomologyCup PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC in
/-- The geometric base-torus dual specializes to the actual native `γ∪u` in the same marking
that realizes physical monodromy and all-degree integral invariant cohomology. -/
theorem exists_actual_baseTorus_nativeCup_specialization :
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
              homeomorphCohomologyEquiv E 1
                  (singularCohomologyPullback f 1 (centralGammaClass C r hr hC)) =
                coordinateTorusH1DualClass 0 ∧
              homeomorphCohomologyEquiv E 1
                  (singularCohomologyPullback f 1 (centralUClass C r hr hC)) =
                coordinateTorusH1DualClass 1 ∧
              homeomorphCohomologyEquiv E 2
                  (singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC)) =
                cupProduct (ProductTorus 4) 1 1
                  (coordinateTorusH1DualClass 0) (coordinateTorusH1DualClass 1) := by
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
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨markedSpecialization_pullback_injective C r hr hC E f hh n,
      markedSpecialization_pullback_range C r hr hC E f hh n⟩
  · exact centralGammaClass_specialization_pullback C r hr hC E f hh
  · exact centralUClass_specialization_pullback C r hr hC E f hh
  · exact baseTorusDualClass_specialization_eq_nativeCup C r hr hC E f hh

end Wikipedia.HopfProblem.CuspCentralCohomology
