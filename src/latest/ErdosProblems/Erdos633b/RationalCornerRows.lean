import ErdosProblems.Erdos633b.TileCornerBounds

/-! Commensurable outer angles make every corner row proportional to the
total corner vector when the reference tile is incommensurable. -/

namespace Erdos633b.Tiling

theorem rational_corner_row_proportional {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi)) (i : Fin 3) (t : ℚ)
    (ht : (t : ℝ) = T.angle i / Real.pi) :
    (d.cornerAngleCount i 0 : ℝ) = (t : ℝ) * d.cornerColumnCount 0 ∧
      (d.cornerAngleCount i 1 : ℝ) = (t : ℝ) * d.cornerColumnCount 1 := by
  have hd : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_nz
  have hden : (t.den : ℝ) * (t : ℝ) = t.num := by
    rw [Rat.cast_def]
    field_simp [hd]
  have ht' : (t : ℝ) * Real.pi = T.angle i := (eq_div_iff Real.pi_ne_zero).mp ht
  have hrow : T.angle i = (d.cornerAngleCount i 0 : ℝ) * d.tile.angle 0 +
      (d.cornerAngleCount i 1 : ℝ) * d.tile.angle 1 := by
    rw [d.angle_eq_three_counts i, d.corner_count_zero_of_column_zero 2 h2 i,
      Nat.cast_zero, zero_mul, add_zero]
  let u : ℤ := (t.den : ℤ) * d.cornerAngleCount i 0 - t.num * d.cornerColumnCount 0
  let v : ℤ := (t.den : ℤ) * d.cornerAngleCount i 1 - t.num * d.cornerColumnCount 1
  have he : (u : ℝ) * d.tile.angle 0 + (v : ℝ) * d.tile.angle 1 = 0 := by
    dsimp only [u, v]
    push_cast
    linear_combination -(t.den : ℝ) * hrow - (t.den : ℝ) * ht' +
      Real.pi * hden - (t.num : ℝ) * d.corner_two_angle_sum h2
  obtain ⟨hu, hv⟩ := d.corner_pair_integer_independent_of_tile h2 hirr u v he
  have hu' : (t.den : ℝ) * d.cornerAngleCount i 0 - (t.num : ℝ) * d.cornerColumnCount 0 = 0 := by
    exact_mod_cast hu
  have hv' : (t.den : ℝ) * d.cornerAngleCount i 1 - (t.num : ℝ) * d.cornerColumnCount 1 = 0 := by
    exact_mod_cast hv
  constructor
  · apply mul_left_cancel₀ hd
    linear_combination hu' - (d.cornerColumnCount 0 : ℝ) * hden
  · apply mul_left_cancel₀ hd
    linear_combination hv' - (d.cornerColumnCount 1 : ℝ) * hden

theorem rational_corner_row_positive {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hrat : ∀ i, IsRational (T.angle i / Real.pi)) (j : Fin 3) (hj : j ≠ 2)
    (hc : 0 < d.cornerColumnCount j) : ∀ i, 0 < d.cornerAngleCount i j := by
  intro i
  obtain ⟨t, ht⟩ := hrat i
  have htp : (0 : ℝ) < t := by rw [ht]; exact div_pos (T.angle_pos i) Real.pi_pos
  have hcp : (0 : ℝ) < d.cornerColumnCount j := by exact_mod_cast hc
  have hp := mul_pos htp hcp
  obtain ⟨h0, h1⟩ := d.rational_corner_row_proportional h2 hirr i t ht
  have he : (d.cornerAngleCount i j : ℝ) = (t : ℝ) * d.cornerColumnCount j := by
    fin_cases j
    · exact h0
    · exact h1
    · exact False.elim (hj rfl)
  rw [← he] at hp
  exact_mod_cast hp

end Erdos633b.Tiling
