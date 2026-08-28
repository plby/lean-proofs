import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMarkedExistence
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationTransportMarked

/-!
# Integral specialization for the actual nonzero cusp fibres

From the original holomorphic period data alone, a common small radius
is derived.  Every nonzero complex fibre in that closed disc has one
actual four-torus marking, valid in every integral homology degree and
for every containing closed-tube radius in the disc.  The independently
prescribed collapse is continuous and induces a surjection whose kernel
is precisely the integral image of the monodromy difference.

The degree-two and degree-three formulas use the actual exterior-period
markings, not rationalized homology or a supplied representation.  The
marked collapse and its comparison homotopy are constructed in the
imported geometric files.  No global logarithm, global product
trivialization, or deformation retraction at an arbitrary fixed radius
is asserted here.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspControlledRetraction
open SingularMayerVietoris PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior
open SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC in
/-- The actual integral specialization theorem, simultaneously for all
small nonzero complex levels and all homology degrees.  Its geometric
and homological conclusions are derived, not supplied as hypotheses. -/
theorem exists_actual_specialization_homology :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀), η₀ < r ∧ η₀ < 1 ∧
      ∀ (t : ℂ) (ht : t ≠ 0), ‖t‖ ≤ η₀ →
        ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t,
          ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
            ∃ hc : Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη),
              let f : C(ActualQuotientFibre C r t, QuotientCentralFibre C r) :=
                ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩
              (markedCollapse C r hr).Homotopic
                  (f.comp (E : C(ProductTorus 4, ActualQuotientFibre C r t))) ∧
                (∀ n : ℕ, Function.Surjective (singularHomologyMap f n) ∧
                  ∀ a : SingularHomology (ActualQuotientFibre C r t) n,
                    singularHomologyMap f n a = 0 ↔
                      ∃ b : SingularHomology (ProductTorus 4) n,
                        singularHomologyMap (torusMatrixMap M₀) n b - b =
                          (homeomorphHomologyEquiv E n).symm a) ∧
                (∀ a : SingularHomology (ActualQuotientFibre C r t) 2,
                  singularHomologyMap f 2 a = 0 ↔
                    ∃ v : latticeExterior 2, exteriorPower.map 2 M₀.mulVecLin v - v =
                      coordinateTorusH2ExteriorEquiv
                        ((homeomorphHomologyEquiv E 2).symm a)) ∧
                (∀ a : SingularHomology (ActualQuotientFibre C r t) 3,
                  singularHomologyMap f 3 a = 0 ↔
                    ∃ v : latticeExterior 3, exteriorPower.map 3 M₀.mulVecLin v - v =
                      coordinateTorusH3ExteriorEquiv
                        ((homeomorphHomologyEquiv E 3).symm a)) := by
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
  refine ⟨hc, hh, ?_, ?_, ?_⟩
  · intro n
    exact ⟨markedSpecialization_homology_surjective C r hr hC E f hh n,
      markedSpecialization_homology_eq_zero_iff C r hr hC E f hh n⟩
  · exact markedSpecialization_homologyTwo_eq_zero_iff C r hr hC E f hh
  · exact markedSpecialization_homologyThree_eq_zero_iff C r hr hC E f hh

end Wikipedia.HopfProblem.CuspCentralHomology
