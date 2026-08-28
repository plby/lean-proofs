import Wikipedia.HopfProblem.CuspControlledRetractionFibre

/-!
# The prescribed collapse on a whole literal norm circle

The source is the original norm-level subspace of the cusp quotient.
The map is defined from the independently prescribed collapse on each
literal complex fibre, without choosing a retraction.  A single
controlled endpoint on the whole toric norm shell proves its joint
continuity and identifies it with one retraction on every angle at once.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishingCircle

open ToricSpace CuspQuotient CuspRetraction CuspControlledRetraction CuspCollapse

/-- The literal norm-level subspace of the original cusp quotient. -/
abbrev NormCircle (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r ρ : ℝ) :=
  {q : QuotientSpace C r // ‖projection C r q‖ = ρ}

/-- The same norm-level points, included in a containing closed tube. -/
def normCircleIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η ρ : ℝ)
    (hρη : ρ ≤ η) : C(NormCircle C r ρ, ClosedQuotient C r η) where
  toFun q := ⟨q.1, q.2.trans_le hρη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem normCircleIntoClosed_coe
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η ρ : ℝ) (hρη : ρ ≤ η)
    (q : NormCircle C r ρ) :
    (normCircleIntoClosed C r η ρ hρη q : QuotientSpace C r) = q := rfl

theorem normCircle_projection_ne_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r ρ : ℝ) (hρ : 0 < ρ)
    (q : NormCircle C r ρ) : projection C r q ≠ 0 := by
  apply norm_pos_iff.mp
  rw [q.2]
  exact hρ

/-- The independently prescribed map on the whole norm circle.  Each
point is regarded in its own literal complex-time fibre. -/
def prescribedCircleCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (η ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η) (hηr : η < r)
    (q : NormCircle C r ρ) : QuotientCentralFibre C r :=
  prescribedActualFibreCollapse C r hr hηr (projection C r q)
    (normCircle_projection_ne_zero C r ρ hρ q) (q.2.trans_le hρη) ⟨q.1, rfl⟩

/-- The whole-circle endpoint condition is imposed on every original
toric representative, before any complex time or angle is selected. -/
def HasPrescribedCircleEndpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (η ρ : ℝ)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r)) : Prop :=
  ∀ (hηr : η < r) (x : PuncturedClosedTube η), ‖time (x.1 : Space)‖ = ρ →
    R (closedQuotientMap C hηr x.1) =
      centralProject C r hr (straightenedPrescribedCollapse C η x)

/-- A toric point on the chosen shell gives its original quotient point
on the actual norm circle. -/
def toricNormCircleProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η ρ : ℝ) (hηr : η < r)
    (x : PuncturedClosedTube η) (hx : ‖time (x.1 : Space)‖ = ρ) : NormCircle C r ρ :=
  ⟨closedQuotientMap C hηr x.1, hx⟩

@[simp] theorem normCircleIntoClosed_toricNormCircleProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η ρ : ℝ) (hρη : ρ ≤ η) (hηr : η < r)
    (x : PuncturedClosedTube η) (hx : ‖time (x.1 : Space)‖ = ρ) :
    normCircleIntoClosed C r η ρ hρη (toricNormCircleProjection C r η ρ hηr x hx) =
      closedQuotientMap C hηr x.1 := rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (η ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η) (hηr : η < r)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (hEnd : HasPrescribedCircleEndpoint C r hr η ρ R)

include hEnd

/-- One endpoint condition identifies the same retraction with every
independently prescribed fibre map at the chosen norm. -/
theorem controlledRetraction_actualFibre_eq (t : ℂ) (ht : t ≠ 0) (hnorm : ‖t‖ = ρ)
    (q : ActualQuotientFibre C r t) :
    R ((quotientLevelFibreHomeomorph C r η t (hnorm.trans_le hρη)).symm q).1 =
      prescribedActualFibreCollapse C r hr hηr t ht (hnorm.trans_le hρη) q := by
  have he := prescribedFibreCollapse_eq_of_endpoint C r hr hηr t ht R
    (fun x hx => hEnd hηr x (hx.trans hnorm))
  exact congrFun he ((quotientLevelFibreHomeomorph C r η t (hnorm.trans_le hρη)).symm q)

/-- Joint equality on the original norm-level topology, not merely
separate homotopies or separate choices of a retraction on each fibre. -/
theorem controlledRetraction_normCircle_eq (q : NormCircle C r ρ) :
    R (normCircleIntoClosed C r η ρ hρη q) =
      prescribedCircleCollapse C r hr η ρ hρ hρη hηr q :=
  controlledRetraction_actualFibre_eq C r hr η ρ hρη hηr R hEnd
    (projection C r q) (normCircle_projection_ne_zero C r ρ hρ q) q.2 ⟨q.1, rfl⟩

/-- A single continuous retraction proves continuity of the prescribed
collapse jointly over all angles of the original norm circle. -/
theorem prescribedCircleCollapse_continuous_of_endpoint :
    Continuous (prescribedCircleCollapse C r hr η ρ hρ hρη hηr) := by
  have he : (fun q => R (normCircleIntoClosed C r η ρ hρη q)) =
      prescribedCircleCollapse C r hr η ρ hρ hρη hηr :=
    funext (controlledRetraction_normCircle_eq C r hr η ρ hρ hρη hηr R hEnd)
  rw [← he]
  exact R.continuous.comp (normCircleIntoClosed C r η ρ hρη).continuous

/-- Exact representative formula for the prescribed whole-circle map. -/
theorem prescribedCircleCollapse_toricNormCircleProjection_of_endpoint
    (x : PuncturedClosedTube η) (hx : ‖time (x.1 : Space)‖ = ρ) :
    prescribedCircleCollapse C r hr η ρ hρ hρη hηr
      (toricNormCircleProjection C r η ρ hηr x hx) =
        centralProject C r hr (straightenedPrescribedCollapse C η x) := by
  rw [← controlledRetraction_normCircle_eq C r hr η ρ hρ hρη hηr R hEnd,
    normCircleIntoClosed_toricNormCircleProjection]
  exact hEnd hηr x hx

/-- The same endpoint condition gives continuity on each literal level,
with the very same `R` for every complex time of norm `ρ`. -/
theorem prescribedActualFibreCollapse_continuous_of_circle_endpoint
    (t : ℂ) (ht : t ≠ 0) (hnorm : ‖t‖ = ρ) :
    Continuous (prescribedActualFibreCollapse C r hr hηr t ht (hnorm.trans_le hρη)) := by
  have he : (fun q : ActualQuotientFibre C r t =>
      R ((quotientLevelFibreHomeomorph C r η t (hnorm.trans_le hρη)).symm q).1) =
        prescribedActualFibreCollapse C r hr hηr t ht (hnorm.trans_le hρη) :=
    funext (controlledRetraction_actualFibre_eq C r hr η ρ hρη hηr R hEnd t ht hnorm)
  rw [← he]
  exact (R.continuous.comp continuous_subtype_val).comp
    (quotientLevelFibreHomeomorph C r η t (hnorm.trans_le hρη)).symm.continuous

end Wikipedia.HopfProblem.CuspBoundaryTopVanishingCircle
