import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Images of vertically symmetric sets under a horizontal reflection

The composition of the two axial square reflections is the point reflection
about the square center.  On a vertically symmetric set their images agree.
-/

open Set

namespace Puzzling139335.N4Remainder

open ReflectionSeparation

theorem horizontal_vertical_apply (p : Plane) :
    horizontal (vertical p) = AffineIsometryEquiv.pointReflection ℝ squareCenter p := by
  ext i
  rw [AffineIsometryEquiv.pointReflection_apply]
  change horizontal (vertical p) i = squareCenter i - p i + squareCenter i
  fin_cases i
  · change horizontal (vertical p) 0 = (1 / 2 : ℝ) - p 0 + 1 / 2
    rw [horizontal_apply_zero, vertical_apply_zero]
    ring
  · change horizontal (vertical p) 1 = (1 / 2 : ℝ) - p 1 + 1 / 2
    rw [horizontal_apply_one, vertical_apply_one]
    ring

theorem horizontal_image_eq_pointReflection_image {P : Set Plane}
    (hP : vertical '' P = P) :
    horizontal '' P = (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' P := by
  calc
    horizontal '' P = horizontal '' (vertical '' P) := by rw [hP]
    _ = (fun p => horizontal (vertical p)) '' P := by rw [Set.image_image]
    _ = (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' P := by
      simp only [horizontal_vertical_apply]

end Puzzling139335.N4Remainder
