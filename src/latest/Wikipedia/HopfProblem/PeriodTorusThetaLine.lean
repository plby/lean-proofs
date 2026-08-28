import Wikipedia.HopfProblem.PeriodTorusThetaBasic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The exponentially normalized restriction to a complex line

The real quadratic expansion of an actual Hermitian form shows that the
explicit exponential correction cancels the mixed term along a complex line.
Consequently any genuine global Gaussian bound gives the stated one-variable
bound, without any periodicity assumption in this file.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTheta

/-- The actual sesquilinear diagonal scales by the squared complex norm. -/
theorem hermitianForm_smul_diagonal_re (H : HermitianForm)
    (v : ComplexPlane₂) (t : ℂ) :
    (H (t • v) (t • v)).re = ‖t‖ ^ 2 * (H v v).re := by
  rw [map_smul H t v, LinearMap.smul_apply, map_smulₛₗ (H v) t v]
  change (t * (star t * H v v)).re = _
  rw [← mul_assoc, Complex.star_def, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq]

/-- The real quadratic expansion along an arbitrary complex line. -/
theorem hermitian_line_re (H : HermitianForm) (hH : IsHermitian H)
    (z v : ComplexPlane₂) (t : ℂ) :
    (H (z + t • v) (z + t • v)).re =
      (H z z).re + 2 * (t * H v z).re + ‖t‖ ^ 2 * (H v v).re := by
  rw [IsHermitian.diagonal_add_re H hH z (t • v),
    hermitianForm_smul_diagonal_re]
  have hcross : (H z (t • v)).re = (t * H v z).re := by
    rw [hH (t • v) z]
    simp [map_smul, LinearMap.smul_apply]
  rw [hcross]

/-- Restriction to a complex line with its mixed Hermitian term removed. -/
def normalizedLine (H : HermitianForm) (θ : ComplexPlane₂ → ℂ)
    (z v : ComplexPlane₂) (t : ℂ) : ℂ :=
  θ (z + t • v) * Complex.exp (-(Real.pi : ℂ) * t * H v z)

@[simp] theorem normalizedLine_zero (H : HermitianForm) (θ : ComplexPlane₂ → ℂ)
    (z v : ComplexPlane₂) : normalizedLine H θ z v 0 = θ z := by
  simp [normalizedLine]

/-- An entire function remains entire after the explicit line normalization. -/
theorem differentiable_normalizedLine (H : HermitianForm) (θ : ComplexPlane₂ → ℂ)
    (hθ : Differentiable ℂ θ) (z v : ComplexPlane₂) :
    Differentiable ℂ (normalizedLine H θ z v) := by
  unfold normalizedLine
  apply Differentiable.mul
  · exact hθ.comp ((differentiable_const z).add (differentiable_id.smul_const v))
  · exact (((differentiable_const (-(Real.pi : ℂ))).mul differentiable_id).mul_const
      (H v z)).cexp

theorem normalizedLine_norm (H : HermitianForm) (θ : ComplexPlane₂ → ℂ)
    (z v : ComplexPlane₂) (t : ℂ) :
    ‖normalizedLine H θ z v t‖ =
      ‖θ (z + t • v)‖ * Real.exp (-Real.pi * (t * H v z).re) := by
  rw [normalizedLine, norm_mul, Complex.norm_exp]
  congr 2
  simp [mul_assoc, Complex.mul_re]

/-- A true global Gaussian bound induces the normalized one-variable bound. -/
theorem normalizedLine_norm_bound (H : HermitianForm) (hH : IsHermitian H)
    (θ : ComplexPlane₂ → ℂ) (C : ℝ)
    (hbound : ∀ x, ‖θ x‖ ≤ C * Real.exp ((Real.pi / 2) * (H x x).re))
    (z v : ComplexPlane₂) (t : ℂ) :
    ‖normalizedLine H θ z v t‖ ≤
      (C * Real.exp ((Real.pi / 2) * (H z z).re)) *
        Real.exp (((Real.pi / 2) * (H v v).re) * ‖t‖ ^ 2) := by
  rw [normalizedLine_norm]
  calc
    ‖θ (z + t • v)‖ * Real.exp (-Real.pi * (t * H v z).re) ≤
        (C * Real.exp ((Real.pi / 2) * (H (z + t • v) (z + t • v)).re)) *
          Real.exp (-Real.pi * (t * H v z).re) :=
      mul_le_mul_of_nonneg_right (hbound _) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      rw [hermitian_line_re H hH z v t]
      ring

end Wikipedia.HopfProblem.PeriodTorusTheta
