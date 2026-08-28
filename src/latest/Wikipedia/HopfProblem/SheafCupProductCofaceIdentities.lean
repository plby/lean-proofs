import Wikipedia.HopfProblem.SheafCupProductCofaceBasic
import Mathlib.Tactic.Ring

/-!
# The low-degree Alexander–Whitney identities

The degree-one product is the literal product `δ² a * δ⁰ b`.
Its differential and the primitives for incoming coboundaries are
computed from ring arithmetic and the actual coface identities.
-/

universe u₀ u₁ u₂ u₃

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface.Data

variable {R0 : Type u₀} {R1 : Type u₁} {R2 : Type u₂} {R3 : Type u₃}
variable [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
variable (D : Coface.Data R0 R1 R2 R3)

def cupOne (a b : R1) : R2 := D.δ1 2 a * D.δ1 0 b

@[simp] theorem cupOne_zero_left (b : R1) : D.cupOne 0 b = 0 := by
  simp [cupOne]

@[simp] theorem cupOne_zero_right (a : R1) : D.cupOne a 0 = 0 := by
  simp [cupOne]

theorem cupOne_add_left (a b c : R1) :
    D.cupOne (a + b) c = D.cupOne a c + D.cupOne b c := by
  simp only [cupOne, map_add, add_mul]

theorem cupOne_add_right (a b c : R1) :
    D.cupOne a (b + c) = D.cupOne a b + D.cupOne a c := by
  simp only [cupOne, map_add, mul_add]

/-- The actual Leibniz identity in bidegree `(1,1)`. -/
theorem d2_cupOne (a b : R1) :
    D.d2 (D.cupOne a b) =
      D.δ2 3 (D.d1 a) * D.δ2 0 (D.δ1 0 b) -
        D.δ2 3 (D.δ1 2 a) * D.δ2 0 (D.d1 b) := by
  simp only [d2_apply, cupOne, map_mul, d1_apply, map_sub, map_add]
  simp only [D.coface12_02, D.coface12_12, D.coface12_22,
    D.coface12_00, D.coface12_01]
  ring

theorem cupOne_isCocycle {a b : R1} (ha : D.d1 a = 0) (hb : D.d1 b = 0) :
    D.d2 (D.cupOne a b) = 0 := by
  rw [D.d2_cupOne, ha, hb, map_zero, map_zero, zero_mul, mul_zero, sub_zero]

def leftPrimitive (r : R0) (b : R1) : R1 := D.δ0 1 r * b

def rightPrimitive (a : R1) (r : R0) : R1 := -(a * D.δ0 0 r)

theorem d1_leftPrimitive (r : R0) (b : R1) :
    D.d1 (D.leftPrimitive r b) =
      D.cupOne (D.d0 r) b + D.δ1 2 (D.δ0 1 r) * D.d1 b := by
  simp only [d1_apply, leftPrimitive, cupOne, d0_apply, map_sub, map_mul]
  simp only [D.coface01_01, D.coface01_11]
  ring

theorem d1_rightPrimitive (a : R1) (r : R0) :
    D.d1 (D.rightPrimitive a r) =
      D.cupOne a (D.d0 r) - D.d1 a * D.δ1 0 (D.δ0 0 r) := by
  simp only [d1_apply, rightPrimitive, cupOne, d0_apply, map_sub, map_mul, map_neg]
  simp only [D.coface01_00, D.coface01_01]
  ring

/-- An incoming coboundary in the first argument has this literal primitive. -/
theorem cupOne_d0_left (r : R0) {b : R1} (hb : D.d1 b = 0) :
    D.cupOne (D.d0 r) b = D.d1 (D.δ0 1 r * b) := by
  have h := D.d1_leftPrimitive r b
  rw [hb, mul_zero, add_zero] at h
  exact h.symm

/-- The sign in the second incoming coboundary is included in the primitive. -/
theorem cupOne_d0_right {a : R1} (ha : D.d1 a = 0) (r : R0) :
    D.cupOne a (D.d0 r) = D.d1 (-(a * D.δ0 0 r)) := by
  have h := D.d1_rightPrimitive a r
  rw [ha, zero_mul, sub_zero] at h
  exact h.symm

theorem cupOne_d0_right_signed {a : R1} (ha : D.d1 a = 0) (r : R0) :
    D.cupOne a (D.d0 r) = -D.d1 (a * D.δ0 0 r) := by
  rw [D.cupOne_d0_right ha r, map_neg]

end Wikipedia.HopfProblem.SheafCupProduct.Coface.Data
