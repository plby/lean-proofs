import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.PlaneIsometries

/-!
# Coordinate identities for the reversed axial form

These lemmas concern the actual affine isometry with coordinate formula
`g(x, y) = (1 - x, y + δ)`.  Its square is a vertical translation, and
reflection in the square's horizontal midline conjugates it to its inverse.
-/

namespace Puzzling139335.N4OuterPair.EqualNormals.AxialForms

open PlaneIsometries ReflectionSeparation

/-- The inverse reverses the sign of the vertical displacement. -/
theorem reversed_inverse_coordinates (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = p 1 + δ) :
    ∀ p, (g.symm p) 0 = 1 - p 0 ∧ (g.symm p) 1 = p 1 - δ := by
  intro p
  have hz := (hg (g.symm p)).1
  have hy := (hg (g.symm p)).2
  rw [g.apply_symm_apply] at hz hy
  exact ⟨by linarith, by linarith⟩

/-- The inverse in the same additive coordinate form, with parameter `-δ`. -/
theorem reversed_inverse_coordinates_neg (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = p 1 + δ) :
    ∀ p, (g.symm p) 0 = 1 - p 0 ∧ (g.symm p) 1 = p 1 + (-δ) := by
  simpa only [sub_eq_add_neg] using reversed_inverse_coordinates g δ hg

/-- Squaring the reversed axial form gives a vertical translation. -/
theorem reversed_square (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = p 1 + δ) :
    ∀ p, g (g p) = p + !₂[0, 2 * δ] := by
  intro p
  apply plane_ext
  · change (g (g p)) 0 = p 0 + 0
    rw [(hg (g p)).1, (hg p).1]
    ring
  · change (g (g p)) 1 = p 1 + 2 * δ
    rw [(hg (g p)).2, (hg p).2]
    ring

/-- The square's horizontal midline reflection conjugates the reversed axial
form to its inverse. -/
theorem horizontal_conjugates_reversed (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = p 1 + δ) :
    ∀ p, horizontal (g (horizontal p)) = g.symm p := by
  intro p
  obtain ⟨hz, hy⟩ := reversed_inverse_coordinates g δ hg p
  apply plane_ext
  · rw [horizontal_apply_zero, (hg (horizontal p)).1, horizontal_apply_zero, hz]
  · rw [horizontal_apply_one, (hg (horizontal p)).2, horizontal_apply_one, hy]
    ring

/-- With no vertical displacement the reversed axial form fixes the square's
actual center. -/
theorem reversed_center_fixed_of_zero (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = p 1 + δ) (hδ : δ = 0) :
    g squareCenter = squareCenter := by
  apply plane_ext
  · rw [(hg squareCenter).1, squareCenter_apply_zero]
    norm_num
  · rw [(hg squareCenter).2, hδ, add_zero]

/-- A nonzero vertical parameter gives a nonzero doubled translation vector. -/
theorem vertical_double_ne_zero (δ : ℝ) (hδ : δ ≠ 0) :
    (!₂[0, 2 * δ] : Plane) ≠ 0 := by
  intro h
  have hy := congrArg (fun p : Plane => p 1) h
  change 2 * δ = 0 at hy
  exact hδ (by linarith)

end Puzzling139335.N4OuterPair.EqualNormals.AxialForms
