import StackExchange.Puzzling139335.N5.StrictFrame.Placement.Form

/-!
# Inverse evaluations of the actual corner placement

Each formula is verified by evaluating the actual affine isometry on the
proposed inverse point, then using injectivity.
-/

namespace Puzzling139335.N5

/-- The direct row order pulls a point of the right side back along the
source direction `(s, -c)`. -/
theorem direct_inverse_right_point
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {C : Plane} {c s b : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hform : ∀ p, e p =
      !₂[1 - c * C 0 - s * C 1 + c * p 0 + s * p 1,
         1 + s * C 0 - c * C 1 - s * p 0 + c * p 1]) :
    e.symm (Schoenflies.Plane.mk 1 b) =
      !₂[C 0 + (1 - b) * s, C 1 - (1 - b) * c] := by
  apply e.injective
  rw [e.apply_symm_apply, hform]
  apply PlaneIsometries.plane_ext
  · change (1 : ℝ) = 1 - c * C 0 - s * C 1 +
      c * (C 0 + (1 - b) * s) + s * (C 1 - (1 - b) * c)
    ring
  · change b = 1 + s * C 0 - c * C 1 -
      s * (C 0 + (1 - b) * s) + c * (C 1 - (1 - b) * c)
    linear_combination (1 - b) * hunit

/-- The swapped row order pulls a point of the right side back along the
source direction `(-c, -s)`. -/
theorem swapped_inverse_right_point
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {C : Plane} {c s b : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hform : ∀ p, e p =
      !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
         1 - c * C 0 - s * C 1 + c * p 0 + s * p 1]) :
    e.symm (Schoenflies.Plane.mk 1 b) =
      !₂[C 0 - (1 - b) * c, C 1 - (1 - b) * s] := by
  apply e.injective
  rw [e.apply_symm_apply, hform]
  apply PlaneIsometries.plane_ext
  · change (1 : ℝ) = 1 + s * C 0 - c * C 1 -
      s * (C 0 - (1 - b) * c) + c * (C 1 - (1 - b) * s)
    ring
  · change b = 1 - c * C 0 - s * C 1 +
      c * (C 0 - (1 - b) * c) + s * (C 1 - (1 - b) * s)
    linear_combination (1 - b) * hunit

/-- Swapping the two output rows leaves the center unchanged, so both
actual placement forms have the same inverse image of the center. -/
theorem CornerPlacementForm.inverse_center
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {C : Plane} {c s : ℝ}
    (hf : CornerPlacementForm e C c s) (hunit : c ^ 2 + s ^ 2 = 1) :
    e.symm squareCenter =
      !₂[C 0 - (c - s) / 2, C 1 - (c + s) / 2] := by
  apply e.injective
  rw [e.apply_symm_apply]
  rcases hf with hform | hform
  · rw [hform]
    apply PlaneIsometries.plane_ext
    · change (1 / 2 : ℝ) = 1 - c * C 0 - s * C 1 +
        c * (C 0 - (c - s) / 2) + s * (C 1 - (c + s) / 2)
      linear_combination (1 / 2 : ℝ) * hunit
    · change (1 / 2 : ℝ) = 1 + s * C 0 - c * C 1 -
        s * (C 0 - (c - s) / 2) + c * (C 1 - (c + s) / 2)
      linear_combination (1 / 2 : ℝ) * hunit
  · rw [hform]
    apply PlaneIsometries.plane_ext
    · change (1 / 2 : ℝ) = 1 + s * C 0 - c * C 1 -
        s * (C 0 - (c - s) / 2) + c * (C 1 - (c + s) / 2)
      linear_combination (1 / 2 : ℝ) * hunit
    · change (1 / 2 : ℝ) = 1 - c * C 0 - s * C 1 +
        c * (C 0 - (c - s) / 2) + s * (C 1 - (c + s) / 2)
      linear_combination (1 / 2 : ℝ) * hunit

end Puzzling139335.N5
