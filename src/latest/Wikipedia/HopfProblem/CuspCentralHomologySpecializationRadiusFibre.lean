import Wikipedia.HopfProblem.CuspCentralHomologyFibreRadius
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProjection

/-!
# Radius comparison preserves the literal nonzero-fibre projection

The previously constructed radius homeomorphism changes only the ambient
quotient radius.  On every fixed-time toric representative it is exactly
the original quotient projection at the larger radius.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspControlledRetraction SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)
    (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ)

/-- The actual fibre radius homeomorphism keeps each toric representative. -/
@[simp] theorem fibreRadiusHomeomorph_fibreProjection (x : ToricFibre t) :
    fibreRadiusHomeomorph C r δ t hδr hC htδ (fibreProjection C δ t htδ x) =
      fibreProjection C r t (htδ.trans_le hδr) x := by
  apply Subtype.ext
  change (openQuotientRadiusHomeomorph C hδr hC (fibreProjection C δ t htδ x).1).1 =
    (fibreProjection C r t (htδ.trans_le hδr) x).1
  simp only [fibreProjection_coe, openQuotientRadiusHomeomorph_quotientMap, openQuotientMap]

@[simp] theorem fibreRadiusHomeomorph_symm_fibreProjection (x : ToricFibre t) :
    (fibreRadiusHomeomorph C r δ t hδr hC htδ).symm
      (fibreProjection C r t (htδ.trans_le hδr) x) = fibreProjection C δ t htδ x := by
  apply (fibreRadiusHomeomorph C r δ t hδr hC htδ).injective
  rw [Homeomorph.apply_symm_apply, fibreRadiusHomeomorph_fibreProjection]

/-- Naturality is an equality of the original continuous maps. -/
theorem fibreRadiusHomeomorph_comp_fibreProjection :
    (fibreRadiusHomeomorph C r δ t hδr hC htδ :
        C(ActualQuotientFibre C δ t, ActualQuotientFibre C r t)).comp
      ⟨fibreProjection C δ t htδ, fibreProjection_continuous C δ t htδ⟩ =
        ⟨fibreProjection C r t (htδ.trans_le hδr),
          fibreProjection_continuous C r t (htδ.trans_le hδr)⟩ := by
  apply ContinuousMap.ext
  intro x
  exact fibreRadiusHomeomorph_fibreProjection C r δ t hδr hC htδ x

end Wikipedia.HopfProblem.CuspCentralHomology
