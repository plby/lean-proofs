import Wikipedia.HopfProblem.CuspCentralCohomologySpecializationCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMarkedExistence

/-!
# Native integral cohomological specialization for actual cusp fibres

For every sufficiently small nonzero complex level, the independently
prescribed collapse from its literal fibre to the literal central fibre
is continuous.  Its pullback on the actual integral singular cochain
cohomology is injective and has exactly the actual monodromy-fixed image
in every degree.  A single genuine fibre homeomorphism supplies all
markings and all three displayed low-degree integral coefficient forms.

All geometric models, projectivity, homological kernels, and evaluation
comparisons have been proved.  The theorem assumes only the original
holomorphic period data.  It makes no assertion of a global logarithm or
of a deformation retraction at an arbitrary fixed tube radius.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction CuspControlledRetraction
open SingularCohomologyFree PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC in
/-- The integral cohomological part of cusp specialization, for actual
complex fibres at the original ambient radius. -/
theorem exists_actual_specialization_cohomology :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀), η₀ < r ∧ η₀ < 1 ∧
      ∀ (t : ℂ) (ht : t ≠ 0), ‖t‖ ≤ η₀ →
        ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t,
          ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
            ∃ hc : Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη),
              let f : C(ActualQuotientFibre C r t, QuotientCentralFibre C r) :=
                ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩
              (∀ n : ℕ, Function.Injective (singularCohomologyPullback f n) ∧
                LinearMap.range (singularCohomologyPullback f n) =
                  singularCohomologyFixed (markedFibreMonodromy E) n) ∧
              (∀ (n : ℕ) (a : SingularCohomology (QuotientCentralFibre C r) n),
                homeomorphCohomologyEquiv E n (singularCohomologyPullback f n a) =
                  singularCohomologyPullback (markedCollapse C r hr) n a) ∧
              (∀ a : SingularCohomology (ActualQuotientFibre C r t) 1,
                a ∈ LinearMap.range (singularCohomologyPullback f 1) ↔
                  ∃ b c : ℤ, coordinateTorusH1CohomologyCoordinates
                    (homeomorphCohomologyEquiv E 1 a) = ![b, c, 0, 0]) ∧
              (∀ a : SingularCohomology (ActualQuotientFibre C r t) 2,
                a ∈ LinearMap.range (singularCohomologyPullback f 2) ↔
                  ∃ b c d e : ℤ, coordinateTorusH2CohomologyCoordinates
                    (homeomorphCohomologyEquiv E 2 a) = ![b, c, d, e, -c, 0]) ∧
              (∀ a : SingularCohomology (ActualQuotientFibre C r t) 3,
                a ∈ LinearMap.range (singularCohomologyPullback f 3) ↔
                  ∃ b c : ℤ, coordinateTorusH3CohomologyCoordinates
                    (homeomorphCohomologyEquiv E 3 a) = ![b, c, 0, 0]) := by
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
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨markedSpecialization_pullback_injective C r hr hC E f hh n,
      markedSpecialization_pullback_range C r hr hC E f hh n⟩
  · exact markedSpecialization_pullback C r hr E f hh
  · exact markedSpecializationH1_mem_range_iff C r hr hC E f hh
  · exact markedSpecializationH2_mem_range_iff C r hr hC E f hh
  · exact markedSpecializationH3_mem_range_iff C r hr hC E f hh

end Wikipedia.HopfProblem.CuspCentralCohomology
