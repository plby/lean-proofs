import Wikipedia.HopfProblem.CuspCentralHomologyRadius
import Wikipedia.HopfProblem.CuspControlledRetractionFibre

/-!
# Actual nonzero fibres do not depend on a larger ambient cusp radius

The maps below are restrictions of the genuine representative-preserving
homeomorphism between the smaller quotient and the corresponding open
subspace of the larger quotient.  They preserve the literal fibre
inclusions and all original subspace topologies.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open CuspQuotient CuspControlledRetraction

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)

/-- The literal inclusion of a level into an open sub-tube. -/
def fibreIntoOpen (htδ : ‖t‖ < δ) :
    C(ActualQuotientFibre C r t, OpenQuotient C r δ) where
  toFun q := ⟨q.1, by rw [q.2]; exact htδ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- Forgetting the intermediate open-subspace subtype changes no fibre
topology, provided the level is in that open disc. -/
def openLevelFibreHomeomorph (htδ : ‖t‖ < δ) :
    {q : OpenQuotient C r δ // projection C r q = t} ≃ₜ ActualQuotientFibre C r t where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨fibreIntoOpen C r δ t htδ q, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (fibreIntoOpen C r δ t htδ).continuous

/-- Actual fibres at the same level, constructed using two different
ambient radii, are homeomorphic by keeping representatives. -/
def fibreRadiusHomeomorph (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ) :
    ActualQuotientFibre C δ t ≃ₜ ActualQuotientFibre C r t :=
  ((openQuotientRadiusHomeomorph C hδr hC).subtype
    (p := fun q => projection C δ q = t)
    (q := fun q : OpenQuotient C r δ => projection C r q = t)
    (fun q => by rw [openQuotientRadiusHomeomorph_projection])).trans
      (openLevelFibreHomeomorph C r δ t htδ)

/-- The radius comparison commutes with the literal fibre inclusion. -/
theorem fibreRadiusHomeomorph_inclusion (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ) :
    (fibreIntoOpen C r δ t htδ).comp
        ((fibreRadiusHomeomorph C r δ t hδr hC htδ) :
          C(ActualQuotientFibre C δ t, ActualQuotientFibre C r t)) =
      ((openQuotientRadiusHomeomorph C hδr hC) :
        C(QuotientSpace C δ, OpenQuotient C r δ)).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(ActualQuotientFibre C δ t, QuotientSpace C δ)) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  rfl

theorem fibreRadiusHomeomorph_symm_inclusion (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ) :
    ((openQuotientRadiusHomeomorph C hδr hC).symm :
        C(OpenQuotient C r δ, QuotientSpace C δ)).comp
          (fibreIntoOpen C r δ t htδ) =
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(ActualQuotientFibre C δ t, QuotientSpace C δ)).comp
          ((fibreRadiusHomeomorph C r δ t hδr hC htδ).symm :
            C(ActualQuotientFibre C r t, ActualQuotientFibre C δ t)) := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨q, rfl⟩ := (fibreRadiusHomeomorph C r δ t hδr hC htδ).surjective q
  have he := ContinuousMap.congr_fun (fibreRadiusHomeomorph_inclusion C r δ t hδr hC htδ) q
  change (openQuotientRadiusHomeomorph C hδr hC).symm
    (fibreIntoOpen C r δ t htδ (fibreRadiusHomeomorph C r δ t hδr hC htδ q)) = _
  rw [show fibreIntoOpen C r δ t htδ (fibreRadiusHomeomorph C r δ t hδr hC htδ q) =
    openQuotientRadiusHomeomorph C hδr hC q.1 from he]
  rw [Homeomorph.symm_apply_apply]
  change q.1 = ((fibreRadiusHomeomorph C r δ t hδr hC htδ).symm
    (fibreRadiusHomeomorph C r δ t hδr hC htδ q)).1
  rw [Homeomorph.symm_apply_apply]

end Wikipedia.HopfProblem.CuspCentralHomology
