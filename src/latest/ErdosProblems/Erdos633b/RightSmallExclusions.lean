import ErdosProblems.Erdos633b.RightAngleCandidates
import ErdosProblems.Erdos633b.ThreeAngleWeights

/-! Pure angle-inventory exclusions leave pi/8 and pi/10 as the only
possible smaller acute angles in a non-reptiling of a scalene triangle
by a strictly ordered right tile. -/

namespace Erdos633b.Tiling

theorem right_pi_five_nonreptiling_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hαβ : d.tile.angle 0 < d.tile.angle 1)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T)
    (hα : d.tile.angle 0 = Real.pi / 5) : False := by
  have hβ : d.tile.angle 1 = 3 * Real.pi / 10 := by linarith [d.tile.angle_sum]
  obtain ⟨hP, hQR⟩ := d.right_corner_column_alternatives hright hαβ hscalene hrep
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, hα, hβ, hright] at hc
  have heReal : ((2 * d.cornerColumnCount 0 + 3 * d.cornerColumnCount 1 +
      5 * d.cornerColumnCount 2 : ℕ) : ℝ) = 10 := by
    push_cast
    apply mul_right_cancel₀ Real.pi_ne_zero
    linear_combination 10 * hc
  have he : 2 * d.cornerColumnCount 0 + 3 * d.cornerColumnCount 1 +
      5 * d.cornerColumnCount 2 = 10 := by exact_mod_cast heReal
  have hP5 : d.cornerColumnCount 0 = 5 := by omega
  have hQ0 : d.cornerColumnCount 1 = 0 := by omega
  have hR0 : d.cornerColumnCount 2 = 0 := by omega
  let c : Fin 3 → ℕ := fun i => d.cornerAngleCount i 0
  have hrow (i : Fin 3) : T.angle i = (c i : ℝ) * (Real.pi / 5) := by
    rw [d.angle_eq_three_counts i,
      d.corner_count_zero_of_column_zero 1 hQ0 i,
      d.corner_count_zero_of_column_zero 2 hR0 i, hα]
    simp only [Nat.cast_zero, zero_mul, add_zero, c]
  have hp (i : Fin 3) : 0 < c i := by
    by_contra hn
    have hz : c i = 0 := by omega
    have hh := hrow i
    rw [hz, Nat.cast_zero, zero_mul] at hh
    exact (T.angle_pos i).ne' hh
  have hinj : Function.Injective c := by
    intro i j hij
    apply hscalene
    rw [hrow i, hrow j, hij]
  have hs : ∑ i, c i = 5 := hP5
  have hb := three_distinct_positive_sum_ge_six c hp hinj
  omega

theorem right_pi_six_reptiling {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hα : d.tile.angle 0 = Real.pi / 6)
    (hscalene : Function.Injective T.angle) : ReptilingAngles d.tile T := by
  have hβ : d.tile.angle 1 = Real.pi / 3 := by linarith [d.tile.angle_sum]
  let c : Fin 3 → ℕ := fun i => d.cornerAngleCount i 0 +
    2 * d.cornerAngleCount i 1 + 3 * d.cornerAngleCount i 2
  have hrow (i : Fin 3) : T.angle i = (c i : ℝ) * (Real.pi / 6) := by
    rw [d.angle_eq_three_counts i, hα, hβ, hright]
    dsimp only [c]
    push_cast
    ring
  have hp (i : Fin 3) : 0 < c i := by
    by_contra hn
    have hz : c i = 0 := by omega
    have hh := hrow i
    rw [hz, Nat.cast_zero, zero_mul] at hh
    exact (T.angle_pos i).ne' hh
  have hinj : Function.Injective c := by
    intro i j hij
    apply hscalene
    rw [hrow i, hrow j, hij]
  have he : ((∑ i, c i : ℕ) : ℝ) * (Real.pi / 6) = Real.pi := by
    rw [Nat.cast_sum, Finset.sum_mul]
    simp_rw [← hrow]
    simpa only [Fin.sum_univ_three] using T.angle_sum
  have hsReal : ((∑ i, c i : ℕ) : ℝ) = 6 := by
    apply mul_right_cancel₀ (div_ne_zero Real.pi_ne_zero (by norm_num : (6 : ℝ) ≠ 0))
    linear_combination he
  have hs : ∑ i, c i = 6 := by exact_mod_cast hsReal
  obtain ⟨i, j, hij, hi, hj⟩ := unit_double_of_three_distinct_sum_six c hp hinj hs
  apply reptilingAngles_of_two_matched_angles d.tile T i j 0 1 hij (by decide)
  · rw [hrow i, hi, hα]
    simp only [Nat.cast_one, one_mul]
  · rw [hrow j, hj, hβ]
    norm_num
    ring

theorem right_angle_two_candidates {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hαβ : d.tile.angle 0 < d.tile.angle 1)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    d.tile.angle 0 = Real.pi / 8 ∨ d.tile.angle 0 = Real.pi / 10 := by
  rcases d.right_angle_four_candidates hright hαβ hscalene hrep with h | h | h | h
  · exact False.elim (d.right_pi_five_nonreptiling_impossible hright hαβ hscalene hrep h)
  · exact False.elim (hrep (d.right_pi_six_reptiling hright h hscalene))
  · exact Or.inl h
  · exact Or.inr h

end Erdos633b.Tiling
