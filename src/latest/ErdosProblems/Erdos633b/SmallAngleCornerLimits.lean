import ErdosProblems.Erdos633b.SmallAngleInventoryLimits
import ErdosProblems.Erdos633b.CornerReindex

/-! Actual corner totals eliminate the small-angle fifths regime and
force a 120-degree tile in the thirds regime. -/

namespace Erdos633b.Tiling

theorem groupOne_swapped_corner_columns_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hscalene : Function.Injective T.angle)
    (hP : d.cornerColumnCount 0 = 2) (hQ : d.cornerColumnCount 1 = 3)
    (hR : d.cornerColumnCount 2 = 0) : EightCases T := by
  apply (d.reindexTile (Equiv.swap 0 1)).groupOne_corner_columns_necessary hn hscalene
  · rw [d.cornerColumnCount_reindexTile]
    exact hQ
  · rw [d.cornerColumnCount_reindexTile]
    exact hP
  · rw [d.cornerColumnCount_reindexTile]
    exact hR

theorem corner_column_lt_of_pi_lt_multiple {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (m : ℕ) (hm : Real.pi < (m : ℝ) * d.tile.angle j) :
    d.cornerColumnCount j < m := by
  have hs : (d.cornerColumnCount j : ℝ) * d.tile.angle j ≤ Real.pi := by
    rw [← d.corner_column_angle_sum]
    exact Finset.single_le_sum (fun i _ => mul_nonneg (Nat.cast_nonneg _)
      (d.tile.angle_pos i).le) (Finset.mem_univ j)
  by_contra hn
  have hh : (m : ℝ) ≤ d.cornerColumnCount j := by
    exact_mod_cast (show m ≤ d.cornerColumnCount j by omega)
  have hp := mul_le_mul_of_nonneg_right hh (d.tile.angle_pos j).le
  linarith

theorem small_angle_thirds_forces_two_pi_thirds {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hsmall : d.tile.angle 0 < Real.pi / 21) (u : ℝ) (hu : -3 ≤ u) (hu' : u ≤ 1)
    (hb : 3 * d.tile.angle 1 = Real.pi + u * d.tile.angle 0) :
    d.tile.angle 2 = 2 * Real.pi / 3 := by
  have hβ := d.middle_angle_le_two_pi_fifths_of_counterexample hn hnot h01 h12
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  obtain ⟨hRle, hRone⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have hw := d.small_angle_thirds_corner_bound hsmall hβ hγ u hu hu' hb
  have hR : d.cornerColumnCount 2 = 0 := by
    by_contra hz
    have hQ0 := (hRone (by omega)).1
    omega
  have hβmin := (d.tile.small_first_angle_bounds hsmall hβ hγ).1
  have hQ4 := d.corner_column_lt_of_pi_lt_multiple 1 4 (by norm_num; linarith [Real.pi_pos])
  have hQ : d.cornerColumnCount 1 = 3 := by omega
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, hQ, hR] at hc
  norm_num only [Nat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero] at hc
  have he : ((d.cornerColumnCount 0 : ℝ) + u) * d.tile.angle 0 = 0 := by
    linear_combination hc - hb
  have hPu : (d.cornerColumnCount 0 : ℝ) + u = 0 :=
    (mul_eq_zero.mp he).resolve_right (d.tile.angle_pos 0).ne'
  have hP3 : d.cornerColumnCount 0 ≤ 3 := by
    exact_mod_cast (show (d.cornerColumnCount 0 : ℝ) ≤ 3 by linarith)
  have htotal := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at htotal
  have hP : d.cornerColumnCount 0 = 2 ∨ d.cornerColumnCount 0 = 3 := by omega
  rcases hP with hP2 | hP3
  · exact False.elim (hnot (d.groupOne_swapped_corner_columns_necessary hn hscalene hP2 hQ hR))
  · rw [hP3] at hPu
    norm_num at hPu
    have hu3 : u = -3 := by linarith
    rw [hu3] at hb
    linarith [d.tile.angle_sum]

theorem small_angle_fifths_impossible {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hsmall : d.tile.angle 0 < Real.pi / 21) (u : ℝ) (hu : -1 ≤ u) (hu' : u ≤ 0)
    (hb : 5 * d.tile.angle 1 = 2 * Real.pi + u * d.tile.angle 0) : False := by
  have hβ := d.middle_angle_le_two_pi_fifths_of_counterexample hn hnot h01 h12
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  obtain ⟨hRle, hRone⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have hw := d.small_angle_fifths_corner_bound hsmall hβ hγ u hu hu' hb
  have hR : d.cornerColumnCount 2 = 0 := by
    by_contra hz
    have hQ0 := (hRone (by omega)).1
    omega
  have hβmin : Real.pi / 3 < d.tile.angle 1 := by
    have hh := mul_le_mul_of_nonneg_right hu (d.tile.angle_pos 0).le
    linarith [Real.pi_pos]
  have hQ3 := d.corner_column_lt_of_pi_lt_multiple 1 3 (by norm_num; linarith)
  omega

end Erdos633b.Tiling
