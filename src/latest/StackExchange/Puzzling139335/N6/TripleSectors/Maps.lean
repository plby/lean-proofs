import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact maps for a corner split into three equal sectors

The maps are affine isometries, with no assumptions on the region to which
they will be applied.  All square roots are kept exact.
-/

open Set

namespace Puzzling139335.N6.TripleSectors

noncomputable section

def point (x y : ℝ) : Plane := !₂[x, y]

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] theorem point_one (x y : ℝ) : point x y 1 = y := rfl

theorem point_ext {p q : Plane} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p = q := by
  ext i
  fin_cases i <;> assumption

theorem sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem one_lt_sqrt_three : 1 < Real.sqrt 3 := by
  nlinarith only [sqrt_three_pos, sqrt_three_sq]

theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith only [sqrt_three_pos, sqrt_three_sq]

/-- The rotation matrix with a unit pair of coefficients. -/
def rotationLinear (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    Plane ≃ₗᵢ[ℝ] Plane where
  toFun p := point (c * p 0 - s * p 1) (s * p 0 + c * p 1)
  invFun p := point (c * p 0 + s * p 1) (-s * p 0 + c * p 1)
  left_inv p := by
    apply point_ext
    · change c * (c * p 0 - s * p 1) + s * (s * p 0 + c * p 1) = p 0
      calc
        _ = (c ^ 2 + s ^ 2) * p 0 := by ring
        _ = _ := by rw [h]; ring
    · change -s * (c * p 0 - s * p 1) + c * (s * p 0 + c * p 1) = p 1
      calc
        _ = (c ^ 2 + s ^ 2) * p 1 := by ring
        _ = _ := by rw [h]; ring
  right_inv p := by
    apply point_ext
    · change c * (c * p 0 + s * p 1) - s * (-s * p 0 + c * p 1) = p 0
      calc
        _ = (c ^ 2 + s ^ 2) * p 0 := by ring
        _ = _ := by rw [h]; ring
    · change s * (c * p 0 + s * p 1) + c * (-s * p 0 + c * p 1) = p 1
      calc
        _ = (c ^ 2 + s ^ 2) * p 1 := by ring
        _ = _ := by rw [h]; ring
  map_add' p q := by apply point_ext <;> simp [point] <;> ring
  map_smul' r p := by apply point_ext <;> simp [point] <;> ring
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
    change (c * p 0 - s * p 1) ^ 2 + (s * p 0 + c * p 1) ^ 2 = _
    calc
      _ = (c ^ 2 + s ^ 2) * (p 0 ^ 2 + p 1 ^ 2) := by ring
      _ = _ := by rw [h]; ring

/-- Rotation by thirty degrees about the origin. -/
def rotateThirty : Plane ≃ᵃⁱ[ℝ] Plane :=
  (rotationLinear (Real.sqrt 3 / 2) (1 / 2)
    (by nlinarith only [sqrt_three_sq])).toAffineIsometryEquiv

/-- Rotation by sixty degrees about the origin. -/
def rotateSixty : Plane ≃ᵃⁱ[ℝ] Plane :=
  (rotationLinear (1 / 2) (Real.sqrt 3 / 2)
    (by nlinarith only [sqrt_three_sq])).toAffineIsometryEquiv

@[simp] theorem rotateThirty_zero (p : Plane) :
    rotateThirty p 0 = Real.sqrt 3 / 2 * p 0 - p 1 / 2 := by
  change Real.sqrt 3 / 2 * p 0 - 1 / 2 * p 1 = _
  ring

@[simp] theorem rotateThirty_one (p : Plane) :
    rotateThirty p 1 = p 0 / 2 + Real.sqrt 3 / 2 * p 1 := by
  change 1 / 2 * p 0 + Real.sqrt 3 / 2 * p 1 = _
  ring

@[simp] theorem rotateThirty_symm_zero (p : Plane) :
    rotateThirty.symm p 0 = Real.sqrt 3 / 2 * p 0 + p 1 / 2 := by
  change Real.sqrt 3 / 2 * p 0 + 1 / 2 * p 1 = _
  ring

@[simp] theorem rotateThirty_symm_one (p : Plane) :
    rotateThirty.symm p 1 = -p 0 / 2 + Real.sqrt 3 / 2 * p 1 := by
  change -(1 / 2) * p 0 + Real.sqrt 3 / 2 * p 1 = _
  ring

@[simp] theorem rotateSixty_zero (p : Plane) :
    rotateSixty p 0 = p 0 / 2 - Real.sqrt 3 / 2 * p 1 := by
  change 1 / 2 * p 0 - Real.sqrt 3 / 2 * p 1 = _
  ring

@[simp] theorem rotateSixty_one (p : Plane) :
    rotateSixty p 1 = Real.sqrt 3 / 2 * p 0 + p 1 / 2 := by
  change Real.sqrt 3 / 2 * p 0 + 1 / 2 * p 1 = _
  ring

/-- Reflection in the line making fifteen degrees with the positive axis. -/
def reflectFifteen : Plane ≃ᵃⁱ[ℝ] Plane :=
  rotateSixty.trans ReflectionSeparation.diagonal

/-- Reflection in the line making thirty degrees with the positive axis. -/
def reflectThirty : Plane ≃ᵃⁱ[ℝ] Plane :=
  rotateThirty.trans ReflectionSeparation.diagonal

/-- Reflection in the line making sixty degrees with the positive axis. -/
def reflectSixty : Plane ≃ᵃⁱ[ℝ] Plane :=
  rotateThirty.symm.trans ReflectionSeparation.diagonal

@[simp] theorem reflectFifteen_zero (p : Plane) :
    reflectFifteen p 0 = Real.sqrt 3 / 2 * p 0 + p 1 / 2 := by
  simp [reflectFifteen]

@[simp] theorem reflectFifteen_one (p : Plane) :
    reflectFifteen p 1 = p 0 / 2 - Real.sqrt 3 / 2 * p 1 := by
  simp [reflectFifteen]

@[simp] theorem reflectThirty_zero (p : Plane) :
    reflectThirty p 0 = p 0 / 2 + Real.sqrt 3 / 2 * p 1 := by
  simp [reflectThirty]

@[simp] theorem reflectThirty_one (p : Plane) :
    reflectThirty p 1 = Real.sqrt 3 / 2 * p 0 - p 1 / 2 := by
  simp [reflectThirty]

@[simp] theorem reflectSixty_zero (p : Plane) :
    reflectSixty p 0 = -p 0 / 2 + Real.sqrt 3 / 2 * p 1 := by
  simp [reflectSixty]

@[simp] theorem reflectSixty_one (p : Plane) :
    reflectSixty p 1 = Real.sqrt 3 / 2 * p 0 + p 1 / 2 := by
  simp [reflectSixty]

theorem reflectThirty_fixed {p : Plane} (hp : Real.sqrt 3 * p 1 = p 0) :
    reflectThirty p = p := by
  apply point_ext
  · simp only [reflectThirty_zero]
    linarith only [hp]
  · simp only [reflectThirty_one]
    rw [← hp]
    ring_nf
    rw [sqrt_three_sq]
    ring

theorem reflectSixty_fixed {p : Plane} (hp : p 1 = Real.sqrt 3 * p 0) :
    reflectSixty p = p := by
  apply point_ext
  · simp only [reflectSixty_zero]
    rw [hp]
    ring_nf
    rw [sqrt_three_sq]
    ring
  · simp only [reflectSixty_one]
    linarith only [hp]

theorem reflectSixty_rotateThirty (p : Plane) :
    reflectSixty (rotateThirty p) = ReflectionSeparation.diagonal p := by
  change ReflectionSeparation.diagonal (rotateThirty.symm (rotateThirty p)) = _
  rw [rotateThirty.symm_apply_apply]

theorem rotateThirty_reflectFifteen (p : Plane) :
    rotateThirty (reflectFifteen p) = reflectThirty p := by
  apply point_ext
  · simp only [rotateThirty_zero, reflectFifteen_zero, reflectFifteen_one,
      reflectThirty_zero]
    ring_nf
    rw [sqrt_three_sq]
    ring
  · simp only [rotateThirty_one, reflectFifteen_zero, reflectFifteen_one,
      reflectThirty_one]
    ring_nf
    rw [sqrt_three_sq]
    ring

end

end Puzzling139335.N6.TripleSectors
