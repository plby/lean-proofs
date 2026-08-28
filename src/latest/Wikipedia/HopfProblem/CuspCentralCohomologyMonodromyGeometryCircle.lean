import Wikipedia.HopfProblem.CuspCentralCohomologyTransport
import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryPhase

/-!
# Marked transport through the literal fibres over a base circle

The transport condition refers to the original quotient and its actual
level subspaces.  It requires joint continuity in the ambient quotient,
the identity at time zero, and the specified marked monodromy at one
positive turn.  The real parameter records a lift of the base circle.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open CuspControlledRetraction CuspQuotient PeriodTorusHigherHomology

/-- The positively oriented base circle, with its real lift of angle. -/
def circleLevel (t : ℂ) (s : ℝ) : ℂ :=
  (Circle.exp (2 * Real.pi * s) : ℂ) * t

@[simp] theorem circleLevel_norm (t : ℂ) (s : ℝ) :
    ‖circleLevel t s‖ = ‖t‖ := by
  rw [circleLevel, norm_mul, Circle.norm_coe, one_mul]

@[simp] theorem circleLevel_zero (t : ℂ) : circleLevel t 0 = t := by
  simp [circleLevel]

@[simp] theorem circleLevel_one (t : ℂ) : circleLevel t 1 = t := by
  simp [circleLevel]

theorem circleLevel_continuous (t : ℂ) : Continuous (circleLevel t) := by
  unfold circleLevel
  fun_prop

/-- Shifting the lifted argument gives the actual circle based at the
original nonzero level. -/
theorem rotatedLevel_add (ρ a s : ℝ) :
    rotatedLevel ρ (a + s) = circleLevel (rotatedLevel ρ a) s := by
  simp only [rotatedLevel, circleLevel, mul_add, Circle.exp_add, Circle.coe_mul]
  ring

/-- Equality of levels identifies the actual fibre subspaces without
changing any point of the ambient quotient. -/
def actualFibreLevelCongr (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    {t u : ℂ} (h : t = u) :
    ActualQuotientFibre C r t ≃ₜ ActualQuotientFibre C r u where
  toFun x := ⟨x.1, x.2.trans h⟩
  invFun x := ⟨x.1, x.2.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp] theorem actualFibreLevelCongr_coe
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) {t u : ℂ} (h : t = u)
    (x : ActualQuotientFibre C r t) :
    (actualFibreLevelCongr C r h x : QuotientSpace C r) = x := rfl

/-- A given marking realizes monodromy by a jointly continuous family
of genuine fibre homeomorphisms over the positively oriented base circle.
The endpoint equalities are in the original quotient, so no choice of
identification of equal level subtypes enters the condition. -/
def HasMarkedCircleTransport (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (t : ℂ)
    (E : ProductTorus 4 ≃ₜ ActualQuotientFibre C r t) : Prop :=
  ∃ F : (s : ℝ) → ActualQuotientFibre C r t ≃ₜ ActualQuotientFibre C r (circleLevel t s),
    Continuous (fun p : ℝ × ActualQuotientFibre C r t =>
      (F p.1 p.2 : QuotientSpace C r)) ∧
    (∀ x, (F 0 x : QuotientSpace C r) = x) ∧
    (∀ x, (F 1 x : QuotientSpace C r) =
      (CuspCentralCohomology.markedFibreMonodromy E x : QuotientSpace C r))

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
