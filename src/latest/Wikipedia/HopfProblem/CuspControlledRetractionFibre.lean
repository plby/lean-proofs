import Wikipedia.HopfProblem.CuspControlledRetractionCusp
import Wikipedia.HopfProblem.CuspControlledRetractionLevelQuotient

/-!
# Exact controlled collapse on the literal nonzero cusp fibre

The prescribed fibre map is defined from the explicit straightened polar
honeycomb formula on toric representatives, using the actual fixed-level
quotient projection. It is not defined as a restriction of a chosen
retraction. The constructed controlled deformation proves that this
descent is continuous, independent of representatives, and exactly equal
to the endpoint restriction on the chosen fibre of the original quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositiveRetraction CuspCollapse

/-- The literal fibre of the original quotient projection. -/
abbrev ActualQuotientFibre (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (t : ℂ) :=
  {q : CuspQuotient.QuotientSpace C r // CuspQuotient.projection C r q = t}

/-- At a level within the closed tube, its fixed-level subtype is exactly
the original quotient fibre, with its original subspace topology. -/
def quotientLevelFibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η) :
    QuotientLevel C r η t ≃ₜ ActualQuotientFibre C r t where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨⟨q.1, by rw [q.2]; exact htη⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _

def levelToPunctured (η : ℝ) (t : ℂ) (ht : t ≠ 0) (x : ToricLevel η t) :
    PuncturedClosedTube η :=
  ⟨x.1, fun hx => ht (x.2.symm.trans hx)⟩

/-- The prescribed representative formula before quotienting the level. -/
def prescribedFibreUpstairs (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (η : ℝ) (t : ℂ) (ht : t ≠ 0) (x : ToricLevel η t) :
    QuotientCentralFibre C r :=
  centralProject C r hr (straightenedPrescribedCollapse C η (levelToPunctured η t ht x))

/-- Descent of the explicit formula, without using any chosen homotopy
or endpoint retraction in its definition. -/
def prescribedFibreCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ) (ht : t ≠ 0) :
    QuotientLevel C r η t → QuotientCentralFibre C r :=
  levelDescend C hηr t (prescribedFibreUpstairs C r hr η t ht)

/-- The same independently defined map on the literal fibre of the
original quotient projection. -/
def prescribedActualFibreCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ) (ht : t ≠ 0)
    (htη : ‖t‖ ≤ η) : ActualQuotientFibre C r t → QuotientCentralFibre C r :=
  prescribedFibreCollapse C r hr hηr t ht ∘ (quotientLevelFibreHomeomorph C r η t htη).symm

theorem prescribedFibreCollapse_eq_of_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {η : ℝ}
    (hηr : η < r) (t : ℂ) (ht : t ≠ 0)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (hEnd : ∀ x : PuncturedClosedTube η, ‖time (x.1 : Space)‖ = ‖t‖ →
      R (closedQuotientMap C hηr x.1) =
        centralProject C r hr (straightenedPrescribedCollapse C η x)) :
    (fun q : QuotientLevel C r η t => R q.1) = prescribedFibreCollapse C r hr hηr t ht := by
  let f := prescribedFibreUpstairs C r hr η t ht
  let g := fun q : QuotientLevel C r η t => R q.1
  have hg (x : ToricLevel η t) : g (levelProjection C hηr t x) = f x :=
    hEnd (levelToPunctured η t ht x) (congrArg norm x.2)
  have hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y := by
    intro x y hxy
    exact (hg x).symm.trans ((congrArg g hxy).trans (hg y))
  exact levelDescend_unique C hηr t f hcompat g hg

theorem prescribedFibreCollapse_levelProjection_of_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {η : ℝ}
    (hηr : η < r) (t : ℂ) (ht : t ≠ 0)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (hEnd : ∀ x : PuncturedClosedTube η, ‖time (x.1 : Space)‖ = ‖t‖ →
      R (closedQuotientMap C hηr x.1) =
        centralProject C r hr (straightenedPrescribedCollapse C η x))
    (x : ToricLevel η t) :
    prescribedFibreCollapse C r hr hηr t ht (levelProjection C hηr t x) =
      prescribedFibreUpstairs C r hr η t ht x := by
  rw [← prescribedFibreCollapse_eq_of_endpoint C r hr hηr t ht R hEnd]
  exact hEnd (levelToPunctured η t ht x) (congrArg norm x.2)

/-- The controlled endpoint theorem on the actual nonzero fibre, with
an actual relative homotopy of the original closed cusp neighborhood. -/
theorem exists_controlled_actual_fibre_retraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ → ∀ (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η),
        ∃ R : C(ClosedQuotient C r η, QuotientCentralFibre C r),
          R.comp (quotientCentralIntoClosed C r η hη.le) =
            ContinuousMap.id (QuotientCentralFibre C r) ∧
          ∃ H : (ContinuousMap.id (ClosedQuotient C r η)).HomotopyRel
              ((quotientCentralIntoClosed C r η hη.le).comp R)
              {q : ClosedQuotient C r η | CuspQuotient.projection C r q = 0},
            (∀ s q, ‖CuspQuotient.projection C r (H (s, q))‖ ≤
              ‖CuspQuotient.projection C r q‖) ∧
            ∀ hηr : η < r,
              Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη) ∧
              (∀ q : ActualQuotientFibre C r t,
                R ((quotientLevelFibreHomeomorph C r η t htη).symm q).1 =
                  prescribedActualFibreCollapse C r hr hηr t ht htη q) ∧
              (∀ x : ToricLevel η t,
                prescribedFibreCollapse C r hr hηr t ht (levelProjection C hηr t x) =
                  prescribedFibreUpstairs C r hr η t ht x) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hR⟩ :=
    exists_closed_quotient_controlled_strongDeformationRetraction C hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ t ht htη
  obtain ⟨R, hRinc, H, hmono, hEnd⟩ :=
    hR η hη hηη₀ ‖t‖ (norm_pos_iff.mpr ht) htη
  refine ⟨R, hRinc, H, hmono, ?_⟩
  intro hηr
  have he := prescribedFibreCollapse_eq_of_endpoint C r hr hηr t ht R (hEnd hηr)
  refine ⟨?_, ?_, ?_⟩
  · unfold prescribedActualFibreCollapse
    rw [← he]
    exact (R.continuous.comp continuous_subtype_val).comp
      (quotientLevelFibreHomeomorph C r η t htη).symm.continuous
  · intro q
    exact congrFun he ((quotientLevelFibreHomeomorph C r η t htη).symm q)
  · exact prescribedFibreCollapse_levelProjection_of_endpoint C r hr hηr t ht R (hEnd hηr)

end Wikipedia.HopfProblem.CuspControlledRetraction
