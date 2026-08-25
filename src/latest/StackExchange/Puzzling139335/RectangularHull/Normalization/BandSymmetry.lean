import StackExchange.Puzzling139335.RectangularHull.AnchoredBands
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Normalize a pair of opposite side bands

Square reflections take any chosen side band to the bottom band and its
opposite to the top band.  These identities hold for every real band width.
-/

open Set

namespace Puzzling139335.RectangularHull

open ReflectionSeparation

lemma horizontal_image_closedAxisBox (l r b t : ℝ) :
    horizontal '' closedAxisBox l r b t = closedAxisBox l r (1 - t) (1 - b) := by
  rw [Function.Involutive.image_eq_preimage_symm horizontal_involutive]
  ext p
  simp only [mem_preimage, closedAxisBox, mem_ofPred_eq, mem_Icc,
    horizontal_apply_zero, horizontal_apply_one]
  constructor <;> intro hp <;>
    exact ⟨hp.1, ⟨by linarith only [hp.2.2], by linarith only [hp.2.1]⟩⟩

lemma diagonal_image_closedAxisBox (l r b t : ℝ) :
    diagonal '' closedAxisBox l r b t = closedAxisBox b t l r := by
  rw [Function.Involutive.image_eq_preimage_symm diagonal_involutive]
  ext p
  simp only [mem_preimage, closedAxisBox, mem_ofPred_eq,
    diagonal_apply_zero, diagonal_apply_one, and_comm]

lemma antiDiagonal_image_closedAxisBox (l r b t : ℝ) :
    antiDiagonal '' closedAxisBox l r b t =
      closedAxisBox (1 - t) (1 - b) (1 - r) (1 - l) := by
  rw [Function.Involutive.image_eq_preimage_symm antiDiagonal_involutive]
  ext p
  simp only [mem_preimage, closedAxisBox, mem_ofPred_eq, mem_Icc,
    antiDiagonal_apply_zero, antiDiagonal_apply_one]
  constructor <;> rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ <;>
    exact ⟨⟨by linarith only [hy1], by linarith only [hy0]⟩,
      ⟨by linarith only [hx1], by linarith only [hx0]⟩⟩

/-- A square symmetry puts any pair of opposite side bands in bottom/top
position, with the chosen member at the bottom. -/
theorem exists_sideBand_normalizing_isometry (h : ℝ) (s : Fin 4) :
    ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, e '' unitSquare = unitSquare ∧
      e '' sideBand h s = sideBand h 0 ∧
      e '' sideBand h (s + 2) = sideBand h 2 := by
  fin_cases s
  · refine ⟨AffineIsometryEquiv.refl ℝ Plane, ?_, ?_, ?_⟩ <;> simp
  · refine ⟨antiDiagonal, antiDiagonal_image_unitSquare, ?_, ?_⟩
    · simp [antiDiagonal_image_closedAxisBox]
    · change antiDiagonal '' sideBand h 3 = sideBand h 2
      simp [antiDiagonal_image_closedAxisBox]
  · refine ⟨horizontal, horizontal_image_unitSquare, ?_, ?_⟩
    · simp [horizontal_image_closedAxisBox]
    · change horizontal '' sideBand h 0 = sideBand h 2
      simp [horizontal_image_closedAxisBox]
  · refine ⟨diagonal, diagonal_image_unitSquare, ?_, ?_⟩
    · simp [diagonal_image_closedAxisBox]
    · change diagonal '' sideBand h 1 = sideBand h 2
      simp [diagonal_image_closedAxisBox]

end Puzzling139335.RectangularHull
