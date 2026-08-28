import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMarkedModels

/-!
# A common small radius for actual marked specialization

Only the original holomorphic period data are given.  The common
small-drift radius is derived, and every nonzero complex level of a
smaller closed disc has an actual four-torus homeomorphism to its literal
original-radius fibre.  One such homeomorphism works for every containing
closed-tube radius in that disc, and for every integral homology degree.

The homeomorphisms here are fibrewise.  No globally continuous logarithm
or global product trivialization of the punctured family is asserted.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction
open SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC in
/-- Actual, original-radius, arbitrary-complex-level specialization
models, constructed unconditionally from the holomorphic period data. -/
theorem exists_original_marked_specialization_models :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀), η₀ < r ∧ η₀ < 1 ∧
      ∀ (t : ℂ) (ht : t ≠ 0), ‖t‖ ≤ η₀ →
        ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t,
          ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
            ∃ hc : Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη),
              (markedCollapse C r hr).Homotopic
                ((⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ :
                  C(ActualQuotientFibre C r t, QuotientCentralFibre C r)).comp
                    (E : C(ProductTorus 4, ActualQuotientFibre C r t))) ∧
              ∀ (n : ℕ) (a : SingularHomology (ProductTorus 4) n),
                singularHomologyMap
                    (⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ :
                      C(ActualQuotientFibre C r t, QuotientCentralFibre C r)) n
                    (homeomorphHomologyEquiv E n a) =
                  singularHomologyMap (markedCollapse C r hr) n a := by
  obtain ⟨δ, hδ, hδr, hδ1, hRC, hRF⟩ :=
    exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  let η₀ : ℝ := δ / 2
  have hη₀ : 0 < η₀ := half_pos hδ
  have hη₀δ : η₀ < δ := half_lt_self hδ
  refine ⟨η₀, hη₀, hη₀δ.trans hδr, hη₀δ.trans hδ1, ?_⟩
  intro t ht ht₀
  have htδ : ‖t‖ < δ := ht₀.trans_lt hη₀δ
  obtain ⟨E, hE⟩ := exists_original_marked_model_of_smallRadius
    C r δ hr hδ hδr.le hC hδ1 hRC hRF t ht htδ
  refine ⟨E, ?_⟩
  intro η hη htη hηr
  have hηδ : η < δ := hη.trans_lt hη₀δ
  let f := smallRadiusActualFibreCollapseMap C r δ hr hδ hδr.le hC hδ1 hRC hRF
    η hηδ t ht htη
  refine ⟨f.continuous, ?_, ?_⟩
  · exact (hE η hηδ htη).1
  · exact (hE η hηδ htη).2

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
