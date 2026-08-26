import ErdosProblems.Erdos633b.DoubledPlacement

/-! Integral scales clear every denominator in the five-piece construction. -/

namespace Erdos633b.DoubledDimensions

open Sixty

def outerScale (a b c : ℕ) : ℕ := commonScale a b * b * (a + b) * c ^ 2
def smallScale (a b c : ℕ) : ℕ := 2 * commonScale a b * a * b * c ^ 3
def cornerScale (a b c : ℕ) : ℕ := a * c ^ 2 * (b - a)
def widthUnits (a b c : ℕ) : ℕ := commonScale a b * (a + b) * c ^ 3
def heightUnits (a b c : ℕ) : ℕ := commonScale a b * c ^ 3 * (b - a)
def trapezoidCount (a b c : ℕ) : ℕ := heightUnits a b c *
  (2 * widthUnits a b c + heightUnits a b c) * (a * b)

theorem outerScale_pos (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) : 0 < outerScale a b c := by
  unfold outerScale
  exact mul_pos (mul_pos (mul_pos (commonScale_pos a b) hb) (by omega)) (pow_pos hc 2)

theorem smallScale_pos (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < smallScale a b c := by
  unfold smallScale
  exact mul_pos (mul_pos (mul_pos (mul_pos (by decide) (commonScale_pos a b)) ha) hb) (pow_pos hc 3)

theorem cornerScale_pos (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c) :
    0 < cornerScale a b c := by
  unfold cornerScale
  exact mul_pos (mul_pos ha (pow_pos hc 2)) (Nat.sub_pos_of_lt hab)

theorem heightUnits_pos (a b c : ℕ) (hab : a < b) (hc : 0 < c) : 0 < heightUnits a b c := by
  unfold heightUnits
  exact mul_pos (mul_pos (commonScale_pos a b) (pow_pos hc 3)) (Nat.sub_pos_of_lt hab)

theorem widthUnits_ge_scale (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    GroupTwoDimensions.scale a b ≤ widthUnits a b c := by
  calc
    _ ≤ commonScale a b := by unfold commonScale; omega
    _ ≤ commonScale a b * (a + b) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ widthUnits a b c := Nat.le_mul_of_pos_right _ (pow_pos hc 3)

theorem shortBase_eq (a b c : ℕ) :
    DoubledCoordinates.shortBase a c (outerScale a b c) =
      (widthUnits a b c : ℝ) * ((a : ℝ) * b) := by
  dsimp only [DoubledCoordinates.shortBase, outerScale, widthUnits]
  push_cast
  ring

theorem lateralSide_eq (a b c : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    DoubledCoordinates.lateralSide a b c (outerScale a b c) =
      (heightUnits a b c : ℝ) * ((a : ℝ) * b) := by
  have hZ : (0 : ℝ) < (a : ℝ) + b := by exact_mod_cast (show 0 < a + b by omega)
  dsimp only [DoubledCoordinates.lateralSide, outerScale, heightUnits]
  push_cast [Nat.cast_sub hab]
  field_simp

theorem smallScale_eq (a b c : ℕ) (hb : 0 < b) :
    2 * (outerScale a b c : ℝ) * a * c / ((a : ℝ) + b) = smallScale a b c := by
  have hZ : (0 : ℝ) < (a : ℝ) + b := by exact_mod_cast (show 0 < a + b by omega)
  dsimp only [outerScale, smallScale]
  push_cast
  field_simp

theorem cornerScale_eq (a b c : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    (outerScale a b c : ℝ) * a * ((b : ℝ) - a) / ((a : ℝ) + b) =
      (cornerScale a b c : ℝ) * (commonScale a b * b : ℕ) := by
  have hZ : (0 : ℝ) < (a : ℝ) + b := by exact_mod_cast (show 0 < a + b by omega)
  dsimp only [outerScale, cornerScale]
  push_cast [Nat.cast_sub hab]
  field_simp

end Erdos633b.DoubledDimensions
