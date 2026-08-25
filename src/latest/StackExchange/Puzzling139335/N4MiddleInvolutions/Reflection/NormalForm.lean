import StackExchange.Puzzling139335.PlaneIsometries.Chasles

/-!
# Real unit-normal form of an ordinary reflection

The complex axis form of a reflection is converted to its real orthogonal
projection formula.  The normal is obtained by rotating the unit axis
direction through a right angle.
-/

namespace Puzzling139335.N4MiddleInvolutions.Reflection

noncomputable section

open PlaneIsometries ComplexConjugate

/-- The unit normal obtained from a unit complex axis direction. -/
def axisNormal (u : Circle) : Plane := !₂[-(u : ℂ).im, (u : ℂ).re]

/-- The normal coordinate of a point on the reflection axis. -/
def axisOffset (c : ℂ) (u : Circle) : ℝ :=
  axisNormal u 0 * c.re + axisNormal u 1 * c.im

@[simp] theorem axisNormal_zero (u : Circle) :
    axisNormal u 0 = -(u : ℂ).im := by
  simp [axisNormal]

@[simp] theorem axisNormal_one (u : Circle) :
    axisNormal u 1 = (u : ℂ).re := by
  simp [axisNormal]

theorem axisNormal_unit (u : Circle) :
    axisNormal u 0 ^ 2 + axisNormal u 1 ^ 2 = 1 := by
  simpa [axisNormal, pow_two, Complex.normSq_apply, add_comm] using Circle.normSq_coe u

/-- The ordinary complex-axis reflection is reflection in the affine line
whose unit normal is `axisNormal u` and whose normal coordinate is `axisOffset c u`. -/
theorem axis_normal_form (e : Plane ≃ᵃⁱ[ℝ] Plane) (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ))) :
    ∀ p, e p = p -
      (2 * ((axisNormal u 0 * p 0 + axisNormal u 1 * p 1) - axisOffset c u)) •
        axisNormal u := by
  have hu : (u : ℂ).re ^ 2 + (u : ℂ).im ^ 2 = 1 := by
    simpa [pow_two, Complex.normSq_apply] using Circle.normSq_coe u
  intro p
  have hp : complexEquiv (e p) =
      c + (u : ℂ) ^ 2 * conj (complexEquiv p - c) := by
    rw [hform p, ← complexReflection_axis_form]
    rfl
  have hre := congrArg Complex.re hp
  have him := congrArg Complex.im hp
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, pow_two, Complex.mul_im,
    complexEquiv_re, complexEquiv_im] at hre him
  apply plane_ext
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      axisOffset, axisNormal_zero, axisNormal_one]
    linear_combination hre + (p 0 - c.re) * hu
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      axisOffset, axisNormal_zero, axisNormal_one]
    linear_combination him + (p 1 - c.im) * hu

/-- Every ordinary reflection has a real unit-normal projection formula. -/
theorem exists_unit_normal_form (e : Plane ≃ᵃⁱ[ℝ] Plane) (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ))) :
    ∃ (ν : Plane) (k : ℝ), ν 0 ^ 2 + ν 1 ^ 2 = 1 ∧
      ∀ p, e p = p - (2 * ((ν 0 * p 0 + ν 1 * p 1) - k)) • ν := by
  exact ⟨axisNormal u, axisOffset c u, axisNormal_unit u, axis_normal_form e c u hform⟩

/-- An affine isometry in the ordinary complex-axis form is involutive. -/
theorem involutive_of_axis_form (e : Plane ≃ᵃⁱ[ℝ] Plane) (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ))) :
    Function.Involutive e := by
  have he : ∀ p, complexEquiv (e p) = complexReflection (u ^ 2) c (complexEquiv p) := by
    intro p
    rw [hform p, complexReflection_axis_form]
  intro p
  apply complexEquiv.injective
  rw [he, he]
  exact complexReflection_involutive (u ^ 2) c (complexEquiv p)

end

end Puzzling139335.N4MiddleInvolutions.Reflection
