import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionMinimum

/-!
# The positive denominator of the cylinder retraction

Radial projection from the point of height two over the barycenter uses
the maximum of its bottom-hitting and face-hitting denominators.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- One coordinate of the barycenter of the standard `n`-simplex. -/
def barycenterCoordinate (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem simplexCard_pos (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity

theorem barycenterCoordinate_pos (n : ℕ) : 0 < barycenterCoordinate n :=
  inv_pos.mpr (simplexCard_pos n)

theorem card_mul_barycenterCoordinate (n : ℕ) :
    ((n : ℝ) + 1) * barycenterCoordinate n = 1 :=
  mul_inv_cancel₀ (ne_of_gt (simplexCard_pos n))

/-- The denominator in the ray from height two over the barycenter. -/
def cylinderDenominator {n : ℕ} (u : unitInterval × Simplex n) : ℝ :=
  max (1 - (u.1 : ℝ) / 2) (1 - ((n : ℝ) + 1) * minimumCoordinate u.2)

theorem cylinderDenominator_half_le {n : ℕ} (u : unitInterval × Simplex n) :
    1 / 2 ≤ cylinderDenominator u := by
  have ht := u.1.property.2
  exact (show 1 / 2 ≤ 1 - (u.1 : ℝ) / 2 by linarith).trans (le_max_left _ _)

theorem cylinderDenominator_pos {n : ℕ} (u : unitInterval × Simplex n) :
    0 < cylinderDenominator u :=
  lt_of_lt_of_le (by norm_num) (cylinderDenominator_half_le u)

theorem cylinderDenominator_ne_zero {n : ℕ} (u : unitInterval × Simplex n) :
    cylinderDenominator u ≠ 0 := ne_of_gt (cylinderDenominator_pos u)

theorem cylinderDenominator_le_one {n : ℕ} (u : unitInterval × Simplex n) :
    cylinderDenominator u ≤ 1 := by
  apply max_le
  · have ht := u.1.property.1
    linarith
  · have hm := mul_nonneg (le_of_lt (simplexCard_pos n)) (minimumCoordinate_nonneg u.2)
    linarith

theorem bottomDenominator_le {n : ℕ} (u : unitInterval × Simplex n) :
    1 - (u.1 : ℝ) / 2 ≤ cylinderDenominator u := le_max_left _ _

theorem sideDenominator_le {n : ℕ} (u : unitInterval × Simplex n) :
    1 - ((n : ℝ) + 1) * minimumCoordinate u.2 ≤ cylinderDenominator u :=
  le_max_right _ _

theorem coordinateDenominator_le {n : ℕ} (u : unitInterval × Simplex n)
    (i : Fin (n + 1)) :
    1 - ((n : ℝ) + 1) * u.2 i ≤ cylinderDenominator u := by
  have hm := mul_le_mul_of_nonneg_left (minimumCoordinate_le u.2 i)
    (le_of_lt (simplexCard_pos n))
  exact (sub_le_sub_left hm 1).trans (sideDenominator_le u)

theorem continuous_cylinderDenominator (n : ℕ) :
    Continuous (cylinderDenominator (n := n)) :=
  (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (continuous_const.sub
      (continuous_const.mul ((continuous_minimumCoordinate n).comp continuous_snd)))

theorem cylinderDenominator_eq_one_of_mem {n : ℕ} {u : unitInterval × Simplex n}
    (hu : u ∈ bottomOrSide n) : cylinderDenominator u = 1 := by
  apply le_antisymm (cylinderDenominator_le_one u)
  rcases hu with ht | hs
  · have h := bottomDenominator_le u
    rw [ht] at h
    change 1 - (0 : ℝ) / 2 ≤ cylinderDenominator u at h
    simpa only [zero_div, sub_zero] using h
  · have h := sideDenominator_le u
    simpa only [minimumCoordinate_eq_zero_of_mem_boundary hs, mul_zero, sub_zero] using h

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
