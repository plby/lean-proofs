import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryCircle
import Wikipedia.HopfProblem.CuspCentralHomologyFibreRadius

/-!
# Actual circle transport is preserved by ambient radius extension

The fibrewise radius homeomorphisms are restrictions of one fixed
representative-preserving map of the ambient quotients.  Consequently
they preserve joint continuity along the circle and conjugate the
endpoint by precisely the same radius comparison as the marking.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open CuspControlledRetraction CuspQuotient PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)
    (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ)

/-- On every level, radius extension is the same fixed ambient map. -/
theorem fibreRadiusHomeomorph_coe (x : ActualQuotientFibre C δ t) :
    (fibreRadiusHomeomorph C r δ t hδr hC htδ x : QuotientSpace C r) =
      (openQuotientRadiusHomeomorph C hδr hC (x : QuotientSpace C δ) :
        QuotientSpace C r) := by
  exact congrArg Subtype.val (ContinuousMap.congr_fun
    (fibreRadiusHomeomorph_inclusion C r δ t hδr hC htδ) x)

/-- Increasing the ambient cusp radius retains a given physical circle
transport and its actual four-period marking. -/
theorem HasMarkedCircleTransport.radius
    {E : ProductTorus 4 ≃ₜ ActualQuotientFibre C δ t}
    (h : HasMarkedCircleTransport C δ t E) :
    HasMarkedCircleTransport C r t
      (E.trans (fibreRadiusHomeomorph C r δ t hδr hC htδ)) := by
  obtain ⟨F, hF, hF0, hF1⟩ := h
  let R := fibreRadiusHomeomorph C r δ t hδr hC htδ
  let Rs : (s : ℝ) → ActualQuotientFibre C δ (circleLevel t s) ≃ₜ
      ActualQuotientFibre C r (circleLevel t s) :=
    fun s => fibreRadiusHomeomorph C r δ (circleLevel t s) hδr hC
      (by simpa only [circleLevel_norm] using htδ)
  have hR (x : ActualQuotientFibre C δ t) :
      (R x : QuotientSpace C r) =
        (openQuotientRadiusHomeomorph C hδr hC (x : QuotientSpace C δ) :
          QuotientSpace C r) :=
    fibreRadiusHomeomorph_coe C r δ t hδr hC htδ x
  have hRs (s : ℝ) (x : ActualQuotientFibre C δ (circleLevel t s)) :
      (Rs s x : QuotientSpace C r) =
        (openQuotientRadiusHomeomorph C hδr hC (x : QuotientSpace C δ) :
          QuotientSpace C r) :=
    fibreRadiusHomeomorph_coe C r δ (circleLevel t s) hδr hC
      (by simpa only [circleLevel_norm] using htδ) x
  refine ⟨fun s => R.symm.trans ((F s).trans (Rs s)), ?_, ?_, ?_⟩
  · have hsmall : Continuous (fun p : ℝ × ActualQuotientFibre C r t =>
        (F p.1 (R.symm p.2) : QuotientSpace C δ)) :=
      hF.comp (continuous_fst.prodMk (R.symm.continuous.comp continuous_snd))
    have hlarge := continuous_subtype_val.comp
      ((openQuotientRadiusHomeomorph C hδr hC).continuous.comp hsmall)
    apply hlarge.congr
    intro p
    exact (hRs p.1 (F p.1 (R.symm p.2))).symm
  · intro x
    change (Rs 0 (F 0 (R.symm x)) : QuotientSpace C r) = x
    rw [hRs, hF0]
    exact (hR (R.symm x)).symm.trans
      (congrArg Subtype.val (R.apply_symm_apply x))
  · intro x
    change (Rs 1 (F 1 (R.symm x)) : QuotientSpace C r) =
      (CuspCentralCohomology.markedFibreMonodromy (E.trans R) x : QuotientSpace C r)
    rw [hRs, hF1]
    exact (hR (CuspCentralCohomology.markedFibreMonodromy E (R.symm x))).symm

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
