import StackExchange.Puzzling139335.N5.CornerFrame

/-!
# Exact coordinate formulas and their supporting inequalities

The predicate records only the two affine row orders. Support bounds are
consequences of square containment of the actual image points.
-/

open Set

namespace Puzzling139335.N5

/-- The two possible row orders of the corner frame. This records an
actual affine placement, with no inequality assumptions. -/
abbrev CornerPlacementForm (e : Plane ≃ᵃⁱ[ℝ] Plane) (C : Plane) (c s : ℝ) : Prop :=
  (∀ p, e p =
      !₂[1 - c * C 0 - s * C 1 + c * p 0 + s * p 1,
         1 + s * C 0 - c * C 1 - s * p 0 + c * p 1]) ∨
  (∀ p, e p =
      !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
         1 - c * C 0 - s * C 1 + c * p 0 + s * p 1])

/-- Both support inequalities follow by applying square containment to
the actual image of each source point. -/
theorem CornerPlacementForm.support {e : Plane ≃ᵃⁱ[ℝ] Plane}
    {C : Plane} {c s : ℝ} (hf : CornerPlacementForm e C c s)
    {P : Set Plane} (he : e '' P ⊆ unitSquare) {p : Plane} (hp : p ∈ P) :
    c * p 0 + s * p 1 ≤ c * C 0 + s * C 1 ∧
      -s * p 0 + c * p 1 ≤ -s * C 0 + c * C 1 := by
  have hfit := he (mem_image_of_mem e hp)
  rcases hf with hform | hform
  · rw [hform p] at hfit
    change
      (0 ≤ 1 - c * C 0 - s * C 1 + c * p 0 + s * p 1 ∧
        1 - c * C 0 - s * C 1 + c * p 0 + s * p 1 ≤ 1) ∧
      (0 ≤ 1 + s * C 0 - c * C 1 - s * p 0 + c * p 1 ∧
        1 + s * C 0 - c * C 1 - s * p 0 + c * p 1 ≤ 1) at hfit
    constructor <;> linarith only [hfit.1.2, hfit.2.2]
  · rw [hform p] at hfit
    change
      (0 ≤ 1 + s * C 0 - c * C 1 - s * p 0 + c * p 1 ∧
        1 + s * C 0 - c * C 1 - s * p 0 + c * p 1 ≤ 1) ∧
      (0 ≤ 1 - c * C 0 - s * C 1 + c * p 0 + s * p 1 ∧
        1 - c * C 0 - s * C 1 + c * p 0 + s * p 1 ≤ 1) at hfit
    constructor <;> linarith only [hfit.1.2, hfit.2.2]

/-- Positivity of the two image coordinates of the actual base origin
makes the first support value strictly less than one in either row order. -/
theorem CornerPlacementForm.frame_sum_lt_one_of_origin_image_pos
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {C : Plane} {c s : ℝ}
    (hf : CornerPlacementForm e C c s)
    (hpos : 0 < e (corner 0) 0 ∧ 0 < e (corner 0) 1) :
    c * C 0 + s * C 1 < 1 := by
  rcases hf with hform | hform
  · rw [hform (corner 0)] at hpos
    norm_num [corner, Fin.ext_iff] at hpos
    linarith only [hpos.1]
  · rw [hform (corner 0)] at hpos
    norm_num [corner, Fin.ext_iff] at hpos
    linarith only [hpos.2]

end Puzzling139335.N5
