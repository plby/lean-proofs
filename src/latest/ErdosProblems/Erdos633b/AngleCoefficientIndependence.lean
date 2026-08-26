import ErdosProblems.Erdos633b.CornerColumnTotals
import ErdosProblems.Erdos633b.ReptilingAlgebra

/-! Independence of the two angles appearing at corners of an incommensurable
outer triangle, and the resulting exact integer coefficient equations. -/

namespace Erdos633b

theorem two_angle_integer_coefficients {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (h : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (u v : ℤ) (huv : (u : ℝ) * a + (v : ℝ) * b = 0) : u = 0 ∧ v = 0 := by
  have he : ((u * Q - v * P : ℤ) : ℝ) * (a / Real.pi) = (-v : ℤ) := by
    push_cast
    rw [← mul_div_assoc]
    apply (div_eq_iff Real.pi_ne_zero).mpr
    linear_combination (Q : ℝ) * huv - (v : ℝ) * h
  obtain ⟨hc, hv⟩ := int_coefficients_of_irrational ha _ _ he
  have hv0 : v = 0 := by omega
  rw [hv0, zero_mul, sub_zero] at hc
  exact ⟨(mul_eq_zero.mp hc).resolve_right hQ, hv0⟩

namespace Tiling

theorem corner_two_angle_sum {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0) :
    (d.cornerColumnCount 0 : ℝ) * d.tile.angle 0 +
      (d.cornerColumnCount 1 : ℝ) * d.tile.angle 1 = Real.pi := by
  simpa only [Fin.sum_univ_three, h2, Nat.cast_zero, zero_mul, add_zero] using
    d.corner_column_angle_sum

theorem first_angle_irrational_of_corner_missing {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) :
    Irrational (d.tile.angle 0 / Real.pi) := by
  have hQ := (d.other_corner_columns_pos h2 hirr).2
  have hQ0 : (d.cornerColumnCount 1 : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hs := d.corner_two_angle_sum h2
  rintro ⟨q, hq⟩
  have hqa : (q : ℝ) * Real.pi = d.tile.angle 0 :=
    (eq_div_iff Real.pi_ne_zero).mp hq
  let r : ℚ := (1 - (d.cornerColumnCount 0 : ℚ) * q) / d.cornerColumnCount 1
  have hr : (r : ℝ) = d.tile.angle 1 / Real.pi := by
    dsimp [r]
    push_cast
    apply (div_eq_div_iff hQ0 Real.pi_ne_zero).mpr
    linear_combination -hs - (d.cornerColumnCount 0 : ℝ) * hqa
  have ht : IsRational (d.tile.angle 2 / Real.pi) := by
    refine ⟨1 - q - r, ?_⟩
    push_cast
    rw [hq, hr]
    apply (eq_div_iff Real.pi_ne_zero).mpr
    field_simp
    linarith [d.tile.angle_sum]
  apply hirr
  apply d.rational_angles_of_tile
  intro i
  fin_cases i
  · exact ⟨q, hq⟩
  · exact ⟨r, hr⟩
  · exact ht

theorem corner_pair_integer_independent {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (u v : ℤ) (he : (u : ℝ) * d.tile.angle 0 + (v : ℝ) * d.tile.angle 1 = 0) :
    u = 0 ∧ v = 0 := by
  exact two_angle_integer_coefficients (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (by exact_mod_cast (d.other_corner_columns_pos h2 hirr).2.ne')
    (by simpa only [Int.cast_natCast] using d.corner_two_angle_sum h2)
    (d.first_angle_irrational_of_corner_missing h2 hirr) u v he

theorem vertex_angle_integer_equations {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) (p q r k : ℕ)
    (hs : (p : ℝ) * d.tile.angle 0 + (q : ℝ) * d.tile.angle 1 +
      (r : ℝ) * d.tile.angle 2 = k * Real.pi) :
    p + d.cornerColumnCount 0 * r = d.cornerColumnCount 0 * k + r ∧
      q + d.cornerColumnCount 1 * r = d.cornerColumnCount 1 * k + r := by
  let u : ℤ := p + (d.cornerColumnCount 0 : ℤ) * r - (d.cornerColumnCount 0 : ℤ) * k - r
  let v : ℤ := q + (d.cornerColumnCount 1 : ℤ) * r - (d.cornerColumnCount 1 : ℤ) * k - r
  have he : (u : ℝ) * d.tile.angle 0 + (v : ℝ) * d.tile.angle 1 = 0 := by
    dsimp [u, v]
    push_cast
    linear_combination hs - (r : ℝ) * d.tile.angle_sum +
      ((r : ℝ) - k) * d.corner_two_angle_sum h2
  obtain ⟨hu, hv⟩ := d.corner_pair_integer_independent h2 hirr u v he
  dsimp [u, v] at hu hv
  have hu' : (p : ℤ) + (d.cornerColumnCount 0 : ℤ) * r =
      (d.cornerColumnCount 0 : ℤ) * k + r := by omega
  have hv' : (q : ℤ) + (d.cornerColumnCount 1 : ℤ) * r =
      (d.cornerColumnCount 1 : ℤ) * k + r := by omega
  exact ⟨by exact_mod_cast hu', by exact_mod_cast hv'⟩

end Tiling

end Erdos633b
