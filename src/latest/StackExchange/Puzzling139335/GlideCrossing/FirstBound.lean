import Mathlib

/-!
# The first lower bound for the reversed-straddle glide

The proof uses a rational chord below the unit circle instead of differentiating
the trigonometric expression.  At the auxiliary endpoint `(C,S) = (1/2,6/7)`,
the circle tangent `4c + 3s ≤ 5` gives the uniform lower bound `1/140`.
Affine interpolation along the chord then gives strict positivity for `C > 0`.
-/

namespace Puzzling139335.GlideCrossing

/-- A rational chord below the relevant arc of the unit circle. -/
private theorem firstBound_chord (S C : ℝ) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hChalf : C ≤ 1 / 2) (hcircle : S ^ 2 + C ^ 2 = 1) :
    1 - (2 / 7) * C ≤ S := by
  have hCsq : C ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hChalf)]
  have hSlarge : 3 / 4 ≤ S := by nlinarith
  have hdiff : 0 ≤ (2 / 7) * (1 + S) - C := by linarith
  have hproduct : 0 ≤ (S - (1 - (2 / 7) * C)) * (1 + S) := by
    nlinarith [mul_nonneg hC hdiff]
  have hden : 0 < 1 + S := by linarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hproduct hden)

/-- A rational lower bound at the auxiliary endpoint `(C,S) = (1/2,6/7)`.
The only geometric input is the unit-circle relation for `(c,s)`. -/
private theorem firstEndpoint_lower (s c : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hcircle : c ^ 2 + s ^ 2 = 1) :
    (1 : ℝ) / 140 ≤
      (2 - s / 2) * (6 / 7) +
        (1 - c / 2 - min (1 / 2) (c / (1 + s))) / 2 - 3 / 2 := by
  let m : ℝ := min (1 / 2) (c / (1 + s))
  have htangent : 4 * c + 3 * s ≤ 5 := by
    nlinarith [sq_nonneg (5 * c - 4), sq_nonneg (5 * s - 3)]
  have hmhalf : m ≤ 1 / 2 := min_le_left _ _
  have hmdiv : m ≤ c / (1 + s) := min_le_right _ _
  have hden : 0 < 1 + s := by linarith
  have hmprod : m * (1 + s) ≤ c := (le_div_iff₀ hden).mp hmdiv
  have hbound : 35 * c + 60 * s + 70 * m ≤ 99 := by
    by_cases hs : s ≤ 3 / 5
    · nlinarith
    · have hpT : 0 ≤ (3 + s) * (5 - 4 * c - 3 * s) :=
        mul_nonneg (by linarith) (by linarith)
      have hpS : 0 ≤ (5 * s - 3) * (43 - 27 * s) :=
        mul_nonneg (by linarith) (by linarith)
      have hp : 0 ≤ (1 + s) * (99 - 60 * s - 35 * c - 70 * m) := by
        nlinarith
      have h := nonneg_of_mul_nonneg_right hp hden
      linarith
  change (1 : ℝ) / 140 ≤
    (2 - s / 2) * (6 / 7) + (1 - c / 2 - m) / 2 - 3 / 2
  linarith

/-- Positive endpoint data stay positive above the rational chord. -/
private theorem firstBound_affine (S C s c m : ℝ) (hC : 0 < C)
    (hChalf : C ≤ 1 / 2) (hs1 : s ≤ 1)
    (hchord : 1 - (2 / 7) * C ≤ S)
    (hendpoint : (1 : ℝ) / 140 ≤
      (2 - s / 2) * (6 / 7) + (1 - c / 2 - m) / 2 - 3 / 2) :
    0 < (2 - s / 2) * S + (1 - c / 2 - m) * C - 3 / 2 := by
  have hA : 0 ≤ 2 - s / 2 := by linarith
  have hinterp :
      (1 - 2 * C) * ((1 - s) / 2) +
        2 * C * ((2 - s / 2) * (6 / 7) + (1 - c / 2 - m) / 2 - 3 / 2) ≤
      (2 - s / 2) * S + (1 - c / 2 - m) * C - 3 / 2 := by
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hchord)]
  have hp1 : 0 ≤ (1 - 2 * C) * ((1 - s) / 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hp2 : 0 < 2 * C *
      ((2 - s / 2) * (6 / 7) + (1 - c / 2 - m) / 2 - 3 / 2) :=
    mul_pos (by linarith) (by linarith)
  linarith

/-- The first strict lower bound for the reversed-straddle glide. -/
theorem firstLowerBound_pos (α β : ℝ) (hα : Real.pi / 3 ≤ α) (hβ : 0 < β)
    (hβα : β ≤ α) (hαhalf : α < Real.pi / 2) :
    0 < Real.sin α - (1 + Real.cos (α - β)) / 2 +
      Real.cos α * (1 - min (1 / 2) (Real.cos β / (1 + Real.sin β)) -
        Real.cos α / (1 + Real.sin α)) := by
  have hπ := Real.pi_pos
  have hsβ : 0 ≤ Real.sin β :=
    Real.sin_nonneg_of_mem_Icc ⟨hβ.le, by linarith⟩
  have hendpoint := firstEndpoint_lower (Real.sin β) (Real.cos β) hsβ
    (Real.sin_le_one β) (Real.cos_sq_add_sin_sq β)
  have hS : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hC : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hαhalf⟩
  have hChalf : Real.cos α ≤ 1 / 2 := by
    simpa only [Real.cos_pi_div_three] using
      (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ Real.pi / 3)
        (by linarith : α ≤ Real.pi) hα)
  have hchord := firstBound_chord (Real.sin α) (Real.cos α) hS hC.le hChalf
    (Real.sin_sq_add_cos_sq α)
  have hpos := firstBound_affine (Real.sin α) (Real.cos α) (Real.sin β) (Real.cos β)
    (min (1 / 2) (Real.cos β / (1 + Real.sin β))) hC hChalf (Real.sin_le_one β)
      hchord hendpoint
  have hden : 1 + Real.sin α ≠ 0 := by linarith
  have hquot : Real.cos α * (Real.cos α / (1 + Real.sin α)) = 1 - Real.sin α := by
    rw [← mul_div_assoc, div_eq_iff hden]
    nlinarith [Real.sin_sq_add_cos_sq α]
  rw [Real.cos_sub]
  nlinarith [hquot]

end Puzzling139335.GlideCrossing
