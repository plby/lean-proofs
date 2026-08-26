import ErdosProblems.Erdos633b.AngleCoefficientIndependence

/-! Coefficient separation when the reference tile is incommensurable.
Unlike the earlier outer-angle version, either corner column may vanish. -/

namespace Erdos633b
namespace Triangle

theorem two_angle_integer_independent (S : Triangle)
    (hirr : ¬ ∀ i, IsRational (S.angle i / Real.pi)) (P Q : ℤ)
    (hpi : (P : ℝ) * S.angle 0 + (Q : ℝ) * S.angle 1 = Real.pi)
    (u v : ℤ) (he : (u : ℝ) * S.angle 0 + (v : ℝ) * S.angle 1 = 0) : u = 0 ∧ v = 0 := by
  let D : ℤ := u * Q - v * P
  have hA : (D : ℝ) * S.angle 0 = -(v : ℝ) * Real.pi := by
    dsimp only [D]
    push_cast
    linear_combination (Q : ℝ) * he - (v : ℝ) * hpi
  have hB : (D : ℝ) * S.angle 1 = (u : ℝ) * Real.pi := by
    dsimp only [D]
    push_cast
    linear_combination (u : ℝ) * hpi - (P : ℝ) * he
  by_cases hD : D = 0
  · rw [hD, Int.cast_zero, zero_mul] at hA hB
    have hv := (mul_eq_zero.mp hA.symm).resolve_right Real.pi_ne_zero
    have hu := (mul_eq_zero.mp hB.symm).resolve_right Real.pi_ne_zero
    exact ⟨by exact_mod_cast hu, by exact_mod_cast neg_eq_zero.mp hv⟩
  · have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
    have ha : IsRational (S.angle 0 / Real.pi) := by
      refine ⟨(-v : ℚ) / D, ?_⟩
      push_cast
      apply (div_eq_div_iff hDr Real.pi_ne_zero).mpr
      nlinarith [hA]
    have hb : IsRational (S.angle 1 / Real.pi) := by
      refine ⟨(u : ℚ) / D, ?_⟩
      push_cast
      apply (div_eq_div_iff hDr Real.pi_ne_zero).mpr
      nlinarith [hB]
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exfalso
    apply hirr
    intro i
    fin_cases i
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
    · refine ⟨1 - a - b, ?_⟩
      push_cast
      rw [ha, hb]
      field_simp
      linarith [S.angle_sum]

end Triangle
namespace Tiling

theorem corner_pair_integer_independent_of_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi))
    (u v : ℤ) (he : (u : ℝ) * d.tile.angle 0 + (v : ℝ) * d.tile.angle 1 = 0) :
    u = 0 ∧ v = 0 := by
  exact d.tile.two_angle_integer_independent hirr (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (by simpa only [Int.cast_natCast] using d.corner_two_angle_sum h2) u v he

theorem vertex_angle_integer_equations_of_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi)) (p q r k : ℕ)
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
  obtain ⟨hu, hv⟩ := d.corner_pair_integer_independent_of_tile h2 hirr u v he
  dsimp [u, v] at hu hv
  have hu' : (p : ℤ) + (d.cornerColumnCount 0 : ℤ) * r =
      (d.cornerColumnCount 0 : ℤ) * k + r := by omega
  have hv' : (q : ℤ) + (d.cornerColumnCount 1 : ℤ) * r =
      (d.cornerColumnCount 1 : ℤ) * k + r := by omega
  exact ⟨by exact_mod_cast hu', by exact_mod_cast hv'⟩

end Tiling
end Erdos633b
