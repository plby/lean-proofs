import StackExchange.Puzzling139335.N4Diagonal.Defs

/-!
# The two actual placement forms at each singleton corner

The center and corner images fix an affine isometry up to interchanging
the two inward coordinates. These alternatives are exactly the preserving
and reversing coordinate formulas of the diagonal-reflection argument.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

theorem ray_quarter (θ : ℝ) : ray (θ + Real.pi / 2) = perpRay θ := by
  ext i
  fin_cases i <;> simp [ray, perpRay, Real.cos_add, Real.sin_add]

theorem perpRay_quarter (θ : ℝ) : perpRay (θ + Real.pi / 2) = -ray θ := by
  ext i
  fin_cases i <;> simp [ray, perpRay, Real.cos_add, Real.sin_add]

theorem ray_half (θ : ℝ) : ray (θ + Real.pi) = -ray θ := by
  ext i
  fin_cases i <;> simp [ray, Real.cos_add, Real.sin_add]

theorem perpRay_half (θ : ℝ) : perpRay (θ + Real.pi) = -perpRay θ := by
  ext i
  fin_cases i <;> simp [perpRay, Real.cos_add, Real.sin_add]

theorem antiDiagonal_cornerFlip_swap (j : Fin 4) (hj : j = 1 ∨ j = 3) (x : Plane) :
    ReflectionSeparation.antiDiagonal (SquareSymmetry.cornerFlip j x) =
      SquareSymmetry.cornerFlip j !₂[x 1, x 0] := by
  rcases hj with rfl | rfl <;> ext i <;> fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

theorem first_frameCoordinates (p x : Plane) (θ : ℝ) :
    N4Midline.frameCoordinates p (θ + Real.pi / 2) x =
      !₂[inner ℝ (perpRay θ) (x - p), -inner ℝ (ray θ) (x - p)] := by
  ext i
  fin_cases i
  · change N4Midline.frameCoordinates p (θ + Real.pi / 2) x 0 =
      inner ℝ (perpRay θ) (x - p)
    rw [N4Midline.frameCoordinates_zero, ray_quarter]
  · change N4Midline.frameCoordinates p (θ + Real.pi / 2) x 1 =
      -inner ℝ (ray θ) (x - p)
    rw [N4Midline.frameCoordinates_one, perpRay_quarter, inner_neg_left]

theorem last_frameCoordinates (q x : Plane) (β : ℝ) :
    N4Midline.frameCoordinates q (β + Real.pi) x =
      !₂[-inner ℝ (ray β) (x - q), -inner ℝ (perpRay β) (x - q)] := by
  ext i
  fin_cases i
  · change N4Midline.frameCoordinates q (β + Real.pi) x 0 =
      -inner ℝ (ray β) (x - q)
    rw [N4Midline.frameCoordinates_zero, ray_half, inner_neg_left]
  · change N4Midline.frameCoordinates q (β + Real.pi) x 1 =
      -inner ℝ (perpRay β) (x - q)
    rw [N4Midline.frameCoordinates_one, perpRay_half, inner_neg_left]

namespace Model

theorem firstCorner_one_or_three (m : Model) : m.firstCorner = 1 ∨ m.firstCorner = 3 :=
  m.corner_order.imp And.left And.left

theorem lastCorner_one_or_three (m : Model) : m.lastCorner = 1 ∨ m.lastCorner = 3 := by
  rcases m.corner_order with h | h
  · exact Or.inr h.2
  · exact Or.inl h.2

theorem first_form (m : Model) :
    (∀ x, m.e x = firstPlus m.firstCorner m.p m.θ x) ∨
      (∀ x, m.e x = firstMinus m.firstCorner m.p m.θ x) := by
  have hcenter := m.e.apply_symm_apply squareCenter
  rw [m.first_center] at hcenter
  have hcenter' : m.e (m.p + (1 / 2 : ℝ) •
      (ray (m.θ + Real.pi / 2) + perpRay (m.θ + Real.pi / 2))) = squareCenter := by
    simpa only [ray_quarter, perpRay_quarter, sub_eq_add_neg] using hcenter
  rcases N4Midline.corner_frame_coordinates m.e m.p (m.θ + Real.pi / 2)
      m.firstCorner m.first_corner hcenter' with hform | hform
  · right
    intro x
    apply (SquareSymmetry.cornerFlip m.firstCorner).injective
    rw [hform, first_frameCoordinates, firstMinus, firstPlus,
      antiDiagonal_cornerFlip_swap m.firstCorner m.firstCorner_one_or_three,
      SquareSymmetry.cornerFlip_involutive]
    rfl
  · left
    intro x
    apply (SquareSymmetry.cornerFlip m.firstCorner).injective
    rw [hform, first_frameCoordinates, firstPlus, SquareSymmetry.cornerFlip_involutive]
    rfl

theorem last_form (m : Model) :
    (∀ x, m.f x = lastPlus m.lastCorner m.q m.β x) ∨
      (∀ x, m.f x = lastMinus m.lastCorner m.q m.β x) := by
  have hcenter := m.f.apply_symm_apply squareCenter
  rw [m.last_center] at hcenter
  have hcenter' : m.f (m.q + (1 / 2 : ℝ) •
      (ray (m.β + Real.pi) + perpRay (m.β + Real.pi))) = squareCenter := by
    simpa only [ray_half, perpRay_half, ← neg_add, smul_neg, sub_eq_add_neg] using hcenter
  rcases N4Midline.corner_frame_coordinates m.f m.q (m.β + Real.pi)
      m.lastCorner m.last_corner hcenter' with hform | hform
  · right
    intro x
    apply (SquareSymmetry.cornerFlip m.lastCorner).injective
    rw [hform, last_frameCoordinates, lastMinus, lastPlus,
      antiDiagonal_cornerFlip_swap m.lastCorner m.lastCorner_one_or_three,
      SquareSymmetry.cornerFlip_involutive]
    rfl
  · left
    intro x
    apply (SquareSymmetry.cornerFlip m.lastCorner).injective
    rw [hform, last_frameCoordinates, lastPlus, SquareSymmetry.cornerFlip_involutive]
    rfl

end Model

end Puzzling139335.N4Diagonal
