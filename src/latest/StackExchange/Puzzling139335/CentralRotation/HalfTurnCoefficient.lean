import StackExchange.Puzzling139335.CentralRotation.RotationAlgebra

/-! # Recognizing the half-turn coefficient in a direct isometry -/

namespace Puzzling139335.CentralRotation.RotationAlgebra

open PlaneIsometries

/-- A direct multiplier other than minus one excludes every half-turn,
irrespective of the translation term or center. -/
theorem not_halfTurn_of_direct_coefficient_ne_neg_one
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle) (b : ℂ) (ha : a ≠ -1)
    (hg : ∀ x, complexEquiv (g x) = (a : ℂ) * complexEquiv x + b) :
    ∀ z, g ≠ AffineIsometryEquiv.pointReflection ℝ z := by
  intro z hgeq
  have hzero := hg (0 : Plane)
  have hone := hg (complexEquiv.symm 1)
  rw [hgeq, complex_pointReflection, map_zero complexEquiv] at hzero
  rw [hgeq, complex_pointReflection, complexEquiv.apply_symm_apply] at hone
  simp only [sub_zero, mul_zero, zero_add] at hzero
  simp only [mul_one] at hone
  have hcoef : (a : ℂ) = -1 := by linear_combination hzero - hone
  apply ha
  apply Subtype.ext
  simpa only [Circle.coe_neg, Circle.coe_one] using hcoef

end Puzzling139335.CentralRotation.RotationAlgebra
