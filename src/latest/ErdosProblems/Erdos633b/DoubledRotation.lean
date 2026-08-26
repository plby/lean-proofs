import ErdosProblems.Erdos633b.DoubledScaledPoints
import ErdosProblems.Erdos633b.PlanarMotions

/-! The rigid placement of the fifth, trapezoidal piece. -/

namespace Erdos633b.DoubledCoordinates

open Sixty

theorem rotation_unit (d : ℝ) (he : d ^ 2 = 3) (a b c : ℝ) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ((b - a) / (2 * c)) ^ 2 + (-d * (a + b) / (2 * c)) ^ 2 = 1 := by
  field_simp
  simp only [he, hrel]
  ring

noncomputable def trapezoidTurn (d : ℝ) (he : d ^ 2 = 3) (a b c m : ℝ) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (rotation ((b - a) / (2 * c)) (-d * (a + b) / (2 * c))
    (rotation_unit d he a b c hc hrel)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.constVAdd ℝ Plane (pointF d a b c m))

theorem trapezoidTurn_point (d : ℝ) (he : d ^ 2 = 3) (a b c m : ℝ) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (s t : ℝ) :
    trapezoidTurn d he a b c m hc hrel (point d s t) =
      pointF d a b c m + point d ((b * s + (a + b) * t) / c)
        (-((a + b) * s + a * t) / c) := by
  change pointF d a b c m + rotationMap ((b - a) / (2 * c))
    (-d * (a + b) / (2 * c)) (point d s t) = _
  congr 1
  ext i
  fin_cases i <;> simp [rotationMap, point]
  · field_simp
    ring_nf
    rw [he]
    ring
  · field_simp
    ring

end Erdos633b.DoubledCoordinates
