import Wikipedia.HopfProblem.PeriodTorusLineBundleChernWinding

/-!
# Pointwise multiplication and logarithmic gauge invariance of winding

These operations multiply and invert the actual scalar values of punctured-plane
loops. Their winding laws follow from addition and negation of the genuine
logarithmic lifts. A continuous closed logarithmic factor changes no winding,
without requiring that logarithm to start at zero.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open Topology unitInterval

/-- Pointwise multiplication of the actual punctured-plane values of two based loops. -/
def pointwiseMulLoop (γ δ : BasedLoop) : BasedLoop where
  toFun t := ⟨(γ t : ℂ) * (δ t : ℂ), mul_ne_zero (γ t).property (δ t).property⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp [puncturedOne]
  target' := by apply Subtype.ext; simp [puncturedOne]

@[simp] theorem pointwiseMulLoop_coe (γ δ : BasedLoop) (t : I) :
    (pointwiseMulLoop γ δ t : ℂ) = (γ t : ℂ) * (δ t : ℂ) := rfl

/-- Pointwise inversion of the actual nonzero complex values of a based loop. -/
def pointwiseInvLoop (γ : BasedLoop) : BasedLoop where
  toFun t := ⟨(γ t : ℂ)⁻¹, inv_ne_zero (γ t).property⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp γ.continuous).inv₀ (fun t => (γ t).property)).subtype_mk _
  source' := by apply Subtype.ext; simp [puncturedOne]
  target' := by apply Subtype.ext; simp [puncturedOne]

@[simp] theorem pointwiseInvLoop_coe (γ : BasedLoop) (t : I) :
    (pointwiseInvLoop γ t : ℂ) = (γ t : ℂ)⁻¹ := rfl

/-- The actual normalized covering lift of a pointwise product is the sum of the lifts. -/
theorem normalizedLoopLog_pointwiseMulLoop (γ δ : BasedLoop) (t : I) :
    normalizedLoopLog (pointwiseMulLoop γ δ) t =
      normalizedLoopLog γ t + normalizedLoopLog δ t := by
  have h := logPath_eq_normalizedLoopLog (pointwiseMulLoop γ δ)
    (fun s => normalizedLoopLog γ s + normalizedLoopLog δ s)
    ((normalizedLoopLog γ).continuous.add (normalizedLoopLog δ).continuous)
    (by simp) (fun s => by rw [Complex.exp_add, normalizedLoopLog_exp,
      normalizedLoopLog_exp]; rfl)
  exact congrFun h.symm t

/-- Pointwise multiplication adds the integer winding numbers. -/
theorem windingNumber_pointwiseMulLoop (γ δ : BasedLoop) :
    windingNumber (pointwiseMulLoop γ δ) = windingNumber γ + windingNumber δ := by
  apply int_mul_two_pi_I_injective
  change (windingNumber (pointwiseMulLoop γ δ) : ℂ) * (2 * Real.pi * Complex.I) =
    ((windingNumber γ + windingNumber δ : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
  rw [← normalizedLoopLog_endpoint, normalizedLoopLog_pointwiseMulLoop,
    normalizedLoopLog_endpoint, normalizedLoopLog_endpoint]
  push_cast
  ring

/-- The actual normalized covering lift of a pointwise inverse is the negative lift. -/
theorem normalizedLoopLog_pointwiseInvLoop (γ : BasedLoop) (t : I) :
    normalizedLoopLog (pointwiseInvLoop γ) t = -normalizedLoopLog γ t := by
  have h := logPath_eq_normalizedLoopLog (pointwiseInvLoop γ)
    (fun s => -normalizedLoopLog γ s) (normalizedLoopLog γ).continuous.neg
    (by simp) (fun s => by rw [Complex.exp_neg, normalizedLoopLog_exp]; rfl)
  exact congrFun h.symm t

/-- Pointwise inversion negates the integer winding number. -/
@[simp] theorem windingNumber_pointwiseInvLoop (γ : BasedLoop) :
    windingNumber (pointwiseInvLoop γ) = -windingNumber γ := by
  apply int_mul_two_pi_I_injective
  change (windingNumber (pointwiseInvLoop γ) : ℂ) * (2 * Real.pi * Complex.I) =
    ((-windingNumber γ : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
  rw [← normalizedLoopLog_endpoint, normalizedLoopLog_pointwiseInvLoop,
    normalizedLoopLog_endpoint]
  simp

/-- Multiplication by the exponential of any continuous closed logarithm preserves winding. -/
theorem windingNumber_eq_of_closed_log_factor (γ δ : BasedLoop) (b : I → ℂ)
    (hb : Continuous b) (hb01 : b 0 = b 1)
    (hfactor : ∀ t, (δ t : ℂ) = (γ t : ℂ) * Complex.exp (b t)) :
    windingNumber δ = windingNumber γ := by
  apply (windingNumber_eq_iff_of_logPath_difference δ
    (fun t => normalizedLoopLog γ t + b t)
    ((normalizedLoopLog γ).continuous.add hb)
    (fun t => by rw [Complex.exp_add, normalizedLoopLog_exp]; exact (hfactor t).symm)
    (windingNumber γ)).mpr
  rw [normalizedLoopLog_zero, zero_add, ← hb01, add_sub_cancel_right]
  exact normalizedLoopLog_endpoint γ

/-- Ratio form of invariance under a continuous closed logarithmic change of frame. -/
theorem windingNumber_eq_of_closed_log_ratio (γ δ : BasedLoop) (b : I → ℂ)
    (hb : Continuous b) (hb01 : b 0 = b 1)
    (hlog : ∀ t, Complex.exp (b t) = (δ t : ℂ) / (γ t : ℂ)) :
    windingNumber δ = windingNumber γ := by
  apply windingNumber_eq_of_closed_log_factor γ δ b hb hb01
  intro t
  rw [hlog t]
  exact ((mul_comm (γ t : ℂ) ((δ t : ℂ) / (γ t : ℂ))).trans
    (div_mul_cancel₀ (δ t : ℂ) (γ t).property)).symm

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
