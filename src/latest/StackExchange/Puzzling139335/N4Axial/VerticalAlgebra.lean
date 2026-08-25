import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.PlaneIsometries

/-! # Coordinate identities for a vertical translation -/

namespace Puzzling139335.N4Axial

open PlaneIsometries ReflectionSeparation

/-- The square of a vertical translation has twice its displacement. -/
theorem vertical_translation_square (g : Plane ≃ᵃⁱ[ℝ] Plane) (t : ℝ)
    (hg : ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = p 1 + t) :
    ∀ p, g (g p) = p + !₂[0, t + t] := by
  intro p
  apply plane_ext
  · change (g (g p)) 0 = p 0 + 0
    rw [(hg (g p)).1, (hg p).1, add_zero]
  · change (g (g p)) 1 = p 1 + (t + t)
    rw [(hg (g p)).2, (hg p).2]
    ring

/-- Horizontal reflection conjugates every vertical translation to its
inverse; the reflection axis is the square's actual midline. -/
theorem horizontal_conjugates_vertical_translation
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (t : ℝ)
    (hg : ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = p 1 + t) :
    ∀ p, horizontal (g (horizontal p)) = g.symm p := by
  intro p
  have hzero : (g.symm p) 0 = p 0 := by
    have hz := (hg (g.symm p)).1
    rw [g.apply_symm_apply] at hz
    exact hz.symm
  have hone : (g.symm p) 1 = p 1 - t := by
    have hy := (hg (g.symm p)).2
    rw [g.apply_symm_apply] at hy
    linarith
  apply plane_ext
  · rw [horizontal_apply_zero, (hg (horizontal p)).1, horizontal_apply_zero, hzero]
  · rw [horizontal_apply_one, (hg (horizontal p)).2, horizontal_apply_one, hone]
    ring

end Puzzling139335.N4Axial
