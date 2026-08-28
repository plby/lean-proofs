import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The radial correction for the smooth orbit model

The polynomial Hopf invariant squares the Euclidean radius. Its radial
correction is the inverse of `x ↦ ‖x‖ • x`. This file proves that this
correction is a homeomorphism, including continuity at the origin. It
does not assert smoothness at the origin: that assertion would be false.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.OrbitPair.Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Square the radius, without changing the direction. -/
def square (x : E) : E := ‖x‖ • x

/-- Take the square root of the radius, with value zero at the origin. -/
def root (x : E) : E := (Real.sqrt ‖x‖)⁻¹ • x

@[simp] theorem square_zero : square (0 : E) = 0 := by simp [square]

@[simp] theorem root_zero : root (0 : E) = 0 := by simp [root]

theorem norm_square (x : E) : ‖square x‖ = ‖x‖ ^ 2 := by
  simp [square, norm_smul, sq]

theorem norm_root (x : E) : ‖root x‖ = Real.sqrt ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hs : Real.sqrt ‖x‖ ≠ 0 := Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hx)
  rw [root, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    _ = (Real.sqrt ‖x‖)⁻¹ * (Real.sqrt ‖x‖ * Real.sqrt ‖x‖) :=
      congrArg ((Real.sqrt ‖x‖)⁻¹ * ·) (Real.mul_self_sqrt (norm_nonneg x)).symm
    _ = _ := inv_mul_cancel_left₀ hs _

@[simp] theorem root_square (x : E) : root (square x) = x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [root, norm_square, Real.sqrt_sq (norm_nonneg x), square,
    inv_smul_smul₀ (norm_ne_zero_iff.mpr hx)]

@[simp] theorem square_root (x : E) : square (root x) = x := by
  by_cases hx : x = 0
  · simp [hx]
  have hs : Real.sqrt ‖x‖ ≠ 0 := Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hx)
  rw [square, norm_root, root, smul_inv_smul₀ hs]

theorem continuous_square : Continuous (square : E → E) :=
  continuous_norm.smul continuous_id

theorem continuous_root : Continuous (root : E → E) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, root_zero, tendsto_zero_iff_norm_tendsto_zero]
    simpa only [ContinuousAt, norm_root, norm_zero, Real.sqrt_zero] using
      (continuous_norm.sqrt.continuousAt :
        ContinuousAt (fun y : E => Real.sqrt ‖y‖) 0)
  · exact (continuous_norm.continuousAt.sqrt.inv₀
      (Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hx))).smul continuousAt_id

/-- The actual radial map and its explicit continuous inverse. -/
def squareHomeomorph : E ≃ₜ E where
  toFun := square
  invFun := root
  left_inv := root_square
  right_inv := square_root
  continuous_toFun := continuous_square
  continuous_invFun := continuous_root

@[simp] theorem squareHomeomorph_apply (x : E) : squareHomeomorph x = square x := rfl

@[simp] theorem squareHomeomorph_symm_apply (x : E) :
    squareHomeomorph.symm x = root x := rfl

end Wikipedia.HopfProblem.OrbitPair.Radial
