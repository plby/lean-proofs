import ErdosProblems.Erdos633b.SmallAngleCornerLimits
import ErdosProblems.Erdos633b.BoundedCornerAngles

/-! For a 120-degree reference tile, the only unbounded corner regime
has the exact geometric corner-column totals (3,3,0). -/

namespace Erdos633b.Tiling

theorem small_two_pi_thirds_corner_columns {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T)
    (hsmall : d.tile.angle 0 < Real.pi / 21) (hg : d.tile.angle 2 = 2 * Real.pi / 3) :
    d.cornerColumnCount 0 = 3 ∧ d.cornerColumnCount 1 = 3 ∧ d.cornerColumnCount 2 = 0 := by
  have hβ : d.tile.angle 1 ≤ 2 * Real.pi / 5 := by
    linarith [d.tile.angle_sum, d.tile.angle_pos 0, Real.pi_pos]
  have hb : 3 * d.tile.angle 1 = Real.pi + (-3) * d.tile.angle 0 := by
    linarith [d.tile.angle_sum]
  have hw := d.small_angle_thirds_corner_bound hsmall hβ hg.le (-3)
    (by norm_num) (by norm_num) hb
  obtain ⟨hRle, hRone⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have hR : d.cornerColumnCount 2 = 0 := by
    by_contra hz
    have hQ0 := (hRone (by omega)).1
    omega
  have hβmin := (d.tile.small_first_angle_bounds hsmall hβ hg.le).1
  have hQ4 := d.corner_column_lt_of_pi_lt_multiple 1 4 (by norm_num; linarith [Real.pi_pos])
  have hQ : d.cornerColumnCount 1 = 3 := by omega
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, hQ, hR] at hc
  norm_num only [Nat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero] at hc
  have he : ((d.cornerColumnCount 0 : ℝ) - 3) * d.tile.angle 0 = 0 := by
    linear_combination hc - hb
  have hP : d.cornerColumnCount 0 = 3 := by
    have hh := (mul_eq_zero.mp he).resolve_right (d.tile.angle_pos 0).ne'
    have hh' : (d.cornerColumnCount 0 : ℝ) = 3 := by linarith
    exact_mod_cast hh'
  exact ⟨hP, hQ, hR⟩

theorem two_pi_thirds_zero_determinant_columns {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (hd : cornerLocalDeterminant (d.cornerColumnCount 0) (d.cornerColumnCount 1)
      (d.cornerColumnCount 2) (3, 3, 1) = 0) :
    d.cornerColumnCount 0 = 3 ∧ d.cornerColumnCount 1 = 3 ∧ d.cornerColumnCount 2 = 0 := by
  have he : (3 : ℝ) * d.tile.angle 0 + 3 * d.tile.angle 1 = Real.pi := by
    linarith [d.tile.angle_sum]
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  obtain ⟨ha, hb⟩ := corner_local_zero_numerators _ _ _ d.tile.angle_sum _ _ _ hc
    (3, 3, 1) (by simpa using he) hd
  obtain ⟨hRle, hRone⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  norm_num [cornerLocalDeterminant, cornerLocalAlphaNumerator,
    cornerLocalBetaNumerator] at hd ha hb
  have hR : d.cornerColumnCount 2 = 0 := by
    by_contra hz
    have hQ0 := (hRone (by omega)).1
    omega
  exact ⟨by omega, by omega, hR⟩

theorem two_pi_thirds_bounded_weights_or_columns {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3) :
    (∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N) ∨
    (d.cornerColumnCount 0 = 3 ∧ d.cornerColumnCount 1 = 3 ∧ d.cornerColumnCount 2 = 0) := by
  by_cases hsmall : d.tile.angle 0 < Real.pi / 21
  · exact Or.inr (d.small_two_pi_thirds_corner_columns h01 h12 hscalene hrep hsmall hg)
  by_cases hd : cornerLocalDeterminant (d.cornerColumnCount 0) (d.cornerColumnCount 1)
      (d.cornerColumnCount 2) (3, 3, 1) = 0
  · exact Or.inr (d.two_pi_thirds_zero_determinant_columns h01 h12 hscalene hrep hg hd)
  left
  have hP := d.corner_column_le_twenty_one_of_angle_lower 0 (le_of_not_gt hsmall)
  have hQ := d.ordered_middle_column_le_five h01 hg.le
  have hR := (d.ordered_corner_columns h01 h12 hscalene hrep).1
  apply d.corner_angle_denominator_bound hP hQ hR (3, 3, 1) (by decide) ?_ hd
  norm_num
  linarith [d.tile.angle_sum]

end Erdos633b.Tiling
