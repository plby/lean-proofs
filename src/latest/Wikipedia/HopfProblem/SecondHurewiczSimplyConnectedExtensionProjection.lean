import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionDenominator

/-!
# Radial projection inside the simplex cylinder

The projected time belongs to the unit interval, and the projected
barycentric coordinates are nonnegative and still sum to one.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

theorem retractedTime_nonneg {n : ℕ} (u : unitInterval × Simplex n) :
    0 ≤ ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u := by
  apply div_nonneg _ (le_of_lt (cylinderDenominator_pos u))
  have h := bottomDenominator_le u
  linarith

theorem retractedTime_le_one {n : ℕ} (u : unitInterval × Simplex n) :
    ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u ≤ 1 := by
  apply (div_le_one (cylinderDenominator_pos u)).mpr
  have ht := u.1.property.2
  have hd := cylinderDenominator_le_one u
  linarith

/-- The time coordinate after radial projection from height two. -/
def retractedTime {n : ℕ} (u : unitInterval × Simplex n) : unitInterval :=
  ⟨((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u,
    retractedTime_nonneg u, retractedTime_le_one u⟩

theorem continuous_retractedTime (n : ℕ) :
    Continuous (retractedTime (n := n)) := by
  apply Continuous.subtype_mk
  exact (((continuous_subtype_val.comp continuous_fst).add
    (continuous_const.mul (continuous_cylinderDenominator n))).sub continuous_const).div
      (continuous_cylinderDenominator n) cylinderDenominator_ne_zero

theorem retractedCoordinate_numerator_nonneg {n : ℕ} (u : unitInterval × Simplex n)
    (i : Fin (n + 1)) :
    0 ≤ u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n := by
  have h := mul_nonneg (sub_nonneg.mpr (coordinateDenominator_le u i))
    (le_of_lt (barycenterCoordinate_pos n))
  have he :
      (cylinderDenominator u - (1 - ((n : ℝ) + 1) * u.2 i)) * barycenterCoordinate n =
        u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n := by
    calc
      _ = (cylinderDenominator u - 1) * barycenterCoordinate n +
          u.2 i * (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
      _ = _ := by rw [card_mul_barycenterCoordinate]; ring
  exact he ▸ h

theorem retractedCoordinate_nonneg {n : ℕ} (u : unitInterval × Simplex n)
    (i : Fin (n + 1)) :
    0 ≤ (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) /
      cylinderDenominator u :=
  div_nonneg (retractedCoordinate_numerator_nonneg u i)
    (le_of_lt (cylinderDenominator_pos u))

theorem retractedCoordinates_sum {n : ℕ} (u : unitInterval × Simplex n) :
    ∑ i : Fin (n + 1),
      (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) /
        cylinderDenominator u = 1 := by
  have hsum : (∑ _i : Fin (n + 1),
      (cylinderDenominator u - 1) * barycenterCoordinate n) = cylinderDenominator u - 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    calc
      _ = (cylinderDenominator u - 1) * (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
      _ = _ := by rw [card_mul_barycenterCoordinate, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, stdSimplex.sum_eq_one, hsum]
  rw [show 1 + (cylinderDenominator u - 1) = cylinderDenominator u by ring,
    mul_inv_cancel₀ (cylinderDenominator_ne_zero u)]

/-- The simplex coordinate after radial projection from above its barycenter. -/
def retractedSimplex {n : ℕ} (u : unitInterval × Simplex n) : Simplex n :=
  ⟨fun i => (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) /
      cylinderDenominator u,
    retractedCoordinate_nonneg u, retractedCoordinates_sum u⟩

theorem continuous_retractedSimplex (n : ℕ) :
    Continuous (retractedSimplex (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).add
    (((continuous_cylinderDenominator n).sub continuous_const).mul continuous_const)).div
      (continuous_cylinderDenominator n) cylinderDenominator_ne_zero

theorem retractedTime_eq_of_mem {n : ℕ} {u : unitInterval × Simplex n}
    (hu : u ∈ bottomOrSide n) : retractedTime u = u.1 := by
  apply Subtype.ext
  change ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u = (u.1 : ℝ)
  rw [cylinderDenominator_eq_one_of_mem hu]
  ring

theorem retractedSimplex_eq_of_mem {n : ℕ} {u : unitInterval × Simplex n}
    (hu : u ∈ bottomOrSide n) : retractedSimplex u = u.2 := by
  apply Subtype.ext
  funext i
  change (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) /
    cylinderDenominator u = u.2 i
  rw [cylinderDenominator_eq_one_of_mem hu]
  simp

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
