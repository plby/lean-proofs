import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplex
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusContinuity
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelMap

/-!
# Original-radius fibre models in the original four-period marking

The actual complex-level product homeomorphism is followed by the genuine
representative-preserving radius homeomorphism.  The original source
period order then gives one homeomorphism from the four-torus to the
literal fibre at the original radius.  The independently prescribed
collapse, not a transported replacement, is homotopic to the marked
central collapse under this homeomorphism.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The original four-period marking on an actual radius-transported fibre. -/
def radiusMarkedHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ)
    (e : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C δ t) :
    ProductTorus 4 ≃ₜ ActualQuotientFibre C r t :=
  sourceProductCoordinateHomeomorph.symm.trans
    (e.trans (fibreRadiusHomeomorph C r δ t hδr hC htδ))

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hδ1 : δ < 1) (hRC : SmallDrift C δ) (hRF : SmallDrift (frozen C) δ)
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ)
    (e : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C δ t)
    (he : IsPrescribedProductModel C δ hδ t ht e)

include he in
/-- Exact radius naturality transports the genuine complex-level
homotopy to the independently prescribed map at the original radius. -/
theorem radiusMarkedHomeomorph_homotopic (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η) :
    (markedCollapse C r hr).Homotopic
      ((smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
        η hηδ t ht htη).comp
          (radiusMarkedHomeomorph C r δ t hδr hC htδ e :
            C(ProductTorus 4, ActualQuotientFibre C r t))) := by
  obtain ⟨hc, hh, _⟩ := he η htη hηδ
  let f : C(ActualQuotientFibre C δ t, QuotientCentralFibre C δ) :=
    ⟨prescribedActualFibreCollapse C δ hδ hηδ t ht htη, hc⟩
  let g := smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
    η hηδ t ht htη
  let eW : C(QuotientCentralFibre C δ, QuotientCentralFibre C r) :=
    (centralRadiusHomeomorph C r δ hδr hC hδ :
      C(QuotientCentralFibre C δ, QuotientCentralFibre C r))
  let eF := fibreRadiusHomeomorph C r δ t hδr hC htδ
  let eP : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C r t := e.trans eF
  have hleft : eW.comp (productCollapse C δ hδ) = productCollapse C r hr :=
    centralRadiusHomeomorph_comp_productCollapse C r δ hδr hC hδ
  have hright : eW.comp (f.comp
      (e : C(CompactFibreTorus × ProductTorus 2, ActualQuotientFibre C δ t))) =
      g.comp (eP : C(CompactFibreTorus × ProductTorus 2, ActualQuotientFibre C r t)) := by
    apply ContinuousMap.ext
    intro x
    exact (prescribedActualFibreCollapse_radius C r δ hr hδ hδr hC hδ1 hRC hRF
      η hηδ t ht htη (e x)).symm
  have hp : (productCollapse C r hr).Homotopic
      (g.comp (eP : C(CompactFibreTorus × ProductTorus 2, ActualQuotientFibre C r t))) := by
    have h := (ContinuousMap.Homotopic.refl eW).comp hh
    change (eW.comp (productCollapse C δ hδ)).Homotopic
      (eW.comp (f.comp
        (e : C(CompactFibreTorus × ProductTorus 2, ActualQuotientFibre C δ t)))) at h
    rwa [hleft, hright] at h
  have h := hp.comp (ContinuousMap.Homotopic.refl
    (sourceProductCoordinateHomeomorph.symm :
      C(ProductTorus 4, CompactFibreTorus × ProductTorus 2)))
  have hmarked : (productCollapse C r hr).comp
      (sourceProductCoordinateHomeomorph.symm :
        C(ProductTorus 4, CompactFibreTorus × ProductTorus 2)) = markedCollapse C r hr :=
    (markedCollapse_eq_product C r hr).symm
  have hend : (g.comp
      (eP : C(CompactFibreTorus × ProductTorus 2, ActualQuotientFibre C r t))).comp
        (sourceProductCoordinateHomeomorph.symm :
          C(ProductTorus 4, CompactFibreTorus × ProductTorus 2)) =
      g.comp (radiusMarkedHomeomorph C r δ t hδr hC htδ e :
        C(ProductTorus 4, ActualQuotientFibre C r t)) := by
    apply ContinuousMap.ext
    intro x
    rfl
  rwa [hmarked, hend] at h

include he in
/-- The single actual fibre homeomorphism gives the actual comparison
in every integral homology degree. -/
theorem radiusMarkedHomeomorph_homology (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η)
    (n : ℕ) (a : SingularHomology (ProductTorus 4) n) :
    singularHomologyMap
        (smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
          η hηδ t ht htη) n
        (homeomorphHomologyEquiv (radiusMarkedHomeomorph C r δ t hδr hC htδ e) n a) =
      singularHomologyMap (markedCollapse C r hr) n a := by
  have h := homotopic_homologyMap
    (radiusMarkedHomeomorph_homotopic C r δ hr hδ hδr hC hδ1 hRC hRF
      t ht htδ e he η hηδ htη) n
  rw [singularHomologyMap_comp] at h
  exact (LinearMap.congr_fun h a).symm

include htδ in
/-- A genuine marked model for every nonzero complex level of the
smaller admissible disc, with the literal larger-radius fibre as target.
The homeomorphism is independent of the containing closed-tube radius. -/
theorem exists_original_marked_model_of_smallRadius :
    ∃ E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t,
      ∀ (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η),
        (markedCollapse C r hr).Homotopic
          ((smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
            η hηδ t ht htη).comp (E : C(ProductTorus 4, ActualQuotientFibre C r t))) ∧
        ∀ (n : ℕ) (a : SingularHomology (ProductTorus 4) n),
          singularHomologyMap
              (smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
                η hηδ t ht htη) n (homeomorphHomologyEquiv E n a) =
            singularHomologyMap (markedCollapse C r hr) n a := by
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr)
  obtain ⟨e, he⟩ :=
    exists_product_model_at_nonzero_level C δ hδ hδ1 hCδ hRC hRF t ht htδ
  refine ⟨radiusMarkedHomeomorph C r δ t hδr hC htδ e, ?_⟩
  intro η hηδ htη
  exact ⟨radiusMarkedHomeomorph_homotopic C r δ hr hδ hδr hC hδ1 hRC hRF
      t ht htδ e he η hηδ htη,
    radiusMarkedHomeomorph_homology C r δ hr hδ hδr hC hδ1 hRC hRF
      t ht htδ e he η hηδ htη⟩

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
