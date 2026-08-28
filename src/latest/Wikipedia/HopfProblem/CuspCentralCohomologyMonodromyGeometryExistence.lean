import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryModels

/-!
# One original-radius marking for transport and specialization

The explicit complex-level model supplies one four-period marking for
both the actual circle transport and the independently prescribed
specialization map.  The original-radius homeomorphism preserves these
two properties together.  The final existence theorem derives every
small-drift bound from the original holomorphic data.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction
open SingularMayerVietoris PeriodTorusHigherHomology

section SmallRadius

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hδ1 : δ < 1) (hRC : SmallDrift C δ) (hRF : SmallDrift (frozen C) δ)

/-- At a specified radius and angle, the explicit varying model gives
one original-radius marking for physical transport and specialization. -/
theorem exists_original_marked_circle_model_at_rotatedLevel
    (ρ : ℝ) (hρ : 0 < ρ) (hρδ : ρ < δ) (a : ℝ) :
    ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r (rotatedLevel ρ a),
      HasMarkedCircleTransport C r (rotatedLevel ρ a) E ∧
      ∀ (η : ℝ) (hηδ : η < δ) (htη : ‖rotatedLevel ρ a‖ ≤ η),
        (markedCollapse C r hr).Homotopic
          ((smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
            η hηδ (rotatedLevel ρ a) (rotatedLevel_ne_zero ρ a hρ) htη).comp
              (E : C(ProductTorus 4, ActualQuotientFibre C r (rotatedLevel ρ a)))) ∧
        ∀ (n : ℕ) (b : SingularHomology (ProductTorus 4) n),
          singularHomologyMap
              (smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
                η hηδ (rotatedLevel ρ a) (rotatedLevel_ne_zero ρ a hρ) htη) n
              (homeomorphHomologyEquiv E n b) =
            singularHomologyMap (markedCollapse C r hr) n b := by
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr)
  let e := varyingComplexProductFibreHomeomorph C δ hδ ρ hρ hδ1 hρδ hCδ hRC hRF a
  have he : IsPrescribedProductModel C δ hδ (rotatedLevel ρ a)
      (rotatedLevel_ne_zero ρ a hρ) e :=
    varyingComplexProductFibreHomeomorph_isPrescribedProductModel
      C δ hδ hδ1 hCδ hRC hRF ρ hρ hρδ a
  have htδ : ‖rotatedLevel ρ a‖ < δ := rotatedLevel_norm_lt ρ a hρ.le δ hρδ
  refine ⟨radiusMarkedHomeomorph C r δ (rotatedLevel ρ a) hδr hC htδ e, ?_, ?_⟩
  · exact radiusMarkedHomeomorph_hasMarkedCircleTransport
      C ρ hρ δ hδ hδ1 hρδ hCδ hRC hRF a r hδr hC
  · intro η hηδ htη
    exact ⟨radiusMarkedHomeomorph_homotopic C r δ hr hδ hδr hC hδ1 hRC hRF
        (rotatedLevel ρ a) (rotatedLevel_ne_zero ρ a hρ) htδ e he η hηδ htη,
      radiusMarkedHomeomorph_homology C r δ hr hδ hδr hC hδ1 hRC hRF
        (rotatedLevel ρ a) (rotatedLevel_ne_zero ρ a hρ) htδ e he η hηδ htη⟩

/-- Every nonzero complex level in the admissible small disc has the
same original-radius marking for physical transport and specialization.
The chosen marking is independent of the containing closed-tube radius. -/
theorem exists_original_marked_circle_model_of_smallRadius
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ) :
    ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t,
      HasMarkedCircleTransport C r t E ∧
      ∀ (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η),
        (markedCollapse C r hr).Homotopic
          ((smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
            η hηδ t ht htη).comp (E : C(ProductTorus 4, ActualQuotientFibre C r t))) ∧
        ∀ (n : ℕ) (a : SingularHomology (ProductTorus 4) n),
          singularHomologyMap
              (smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
                η hηδ t ht htη) n (homeomorphHomologyEquiv E n a) =
            singularHomologyMap (markedCollapse C r hr) n a := by
  let P (u : ℂ) (hu : u ≠ 0) : Prop :=
    ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r u,
      HasMarkedCircleTransport C r u E ∧
      ∀ (η : ℝ) (hηδ : η < δ) (huη : ‖u‖ ≤ η),
        (markedCollapse C r hr).Homotopic
          ((smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
            η hηδ u hu huη).comp (E : C(ProductTorus 4, ActualQuotientFibre C r u))) ∧
        ∀ (n : ℕ) (a : SingularHomology (ProductTorus 4) n),
          singularHomologyMap
              (smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
                η hηδ u hu huη) n (homeomorphHomologyEquiv E n a) =
            singularHomologyMap (markedCollapse C r hr) n a
  change P t ht
  have hρ : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hm : P (rotatedLevel ‖t‖ (argumentTurns t))
      (rotatedLevel_ne_zero ‖t‖ (argumentTurns t) hρ) :=
    exists_original_marked_circle_model_at_rotatedLevel C r δ hr hδ hδr hC hδ1 hRC hRF
      ‖t‖ hρ htδ (argumentTurns t)
  have transfer (u : ℂ) (hu : u ≠ 0) (hut : u = t) (huModel : P u hu) : P t ht := by
    subst u
    exact huModel
  exact transfer _ _ (rotatedLevel_norm_argumentTurns t) hm

end SmallRadius

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC in
/-- The original holomorphic data alone provide a common small disc
and, at every nonzero level, one actual four-period marking realizing
both physical circle monodromy and the independently prescribed collapse. -/
theorem exists_original_marked_circle_specialization_models :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀), η₀ < r ∧ η₀ < 1 ∧
      ∀ (t : ℂ) (ht : t ≠ 0), ‖t‖ ≤ η₀ →
        ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t,
          HasMarkedCircleTransport C r t E ∧
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
  obtain ⟨E, hCircle, hE⟩ := exists_original_marked_circle_model_of_smallRadius
    C r δ hr hδ hδr.le hC hδ1 hRC hRF t ht htδ
  refine ⟨E, hCircle, ?_⟩
  intro η hη htη hηr
  have hηδ : η < δ := hη.trans_lt hη₀δ
  let f := smallRadiusActualFibreCollapseMap C r δ hr hδ hδr.le hC hδ1 hRC hRF
    η hηδ t ht htη
  refine ⟨f.continuous, ?_, ?_⟩
  · exact (hE η hηδ htη).1
  · exact (hE η hηδ htη).2

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
