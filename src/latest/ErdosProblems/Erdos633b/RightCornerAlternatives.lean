import ErdosProblems.Erdos633b.FewCornerAngles

/-! The possible outer-corner columns for a non-reptiling by a strictly
ordered right reference tile. -/

namespace Erdos633b

theorem right_corner_small_columns (α β : ℝ) (P Q R : ℕ)
    (hα : 0 < α) (hαβ : α < β) (hsum : α + β = Real.pi / 2)
    (hcorner : (P : ℝ) * α + (Q : ℝ) * β + (R : ℝ) * (Real.pi / 2) = Real.pi)
    (htotal : 5 ≤ P + Q + R) : 4 ≤ P ∧ Q + R ≤ 1 := by
  have hβ : 0 < β := hα.trans hαβ
  have hβ4 : Real.pi / 4 < β := by linarith
  have hp : 0 ≤ (P : ℝ) * α := mul_nonneg (Nat.cast_nonneg _) hα.le
  have hq : 0 ≤ (Q : ℝ) * β := mul_nonneg (Nat.cast_nonneg _) hβ.le
  have hr : 0 ≤ (R : ℝ) * (Real.pi / 2) := mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hR : R ≤ 1 := by
    by_contra hn
    have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast (show 2 ≤ R by omega)
    have hm := mul_le_mul_of_nonneg_right hR2 (by positivity : 0 ≤ Real.pi / 2)
    have hP0 : P = 0 := by
      by_contra h
      have hPpos : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero h
      have hh := mul_pos hPpos hα
      linarith
    have hQ0 : Q = 0 := by
      by_contra h
      have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero h
      have hh := mul_pos hQpos hβ
      linarith
    rw [hP0, hQ0] at hcorner
    norm_num at hcorner
    have hRreal : (R : ℝ) = 2 := by nlinarith [Real.pi_pos]
    have hRnat : R = 2 := by exact_mod_cast hRreal
    omega
  have hQR : Q + R ≤ 1 := by
    interval_cases R
    · have hQ3 : Q ≤ 3 := by
        by_contra hn
        have hQ4 : (4 : ℝ) ≤ Q := by exact_mod_cast (show 4 ≤ Q by omega)
        have hm := mul_le_mul_of_nonneg_right hQ4 hβ.le
        norm_num at hcorner
        linarith
      have hQ2 : Q ≠ 2 := by
        intro h
        rw [h] at hcorner
        norm_num at hcorner
        have he : (P : ℝ) * α = 2 * α := by linarith
        have hP2 : P = 2 := by exact_mod_cast mul_right_cancel₀ hα.ne' he
        omega
      have hQne3 : Q ≠ 3 := by
        intro h
        rw [h] at hcorner
        norm_num at hcorner
        have hP0 : P = 0 := by
          by_contra hn
          have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast Nat.pos_of_ne_zero hn
          have hm := mul_le_mul_of_nonneg_right hP1 hα.le
          linarith
        omega
      omega
    · have hQ1 : Q ≤ 1 := by
        by_contra hn
        have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast (show 2 ≤ Q by omega)
        have hm := mul_le_mul_of_nonneg_right hQ2 hβ.le
        norm_num at hcorner
        linarith
      have hQ0 : Q = 0 := by
        by_contra hn
        have heQ : Q = 1 := by omega
        rw [heQ] at hcorner
        norm_num at hcorner
        have he : (P : ℝ) * α = 1 * α := by linarith
        have hP1 : P = 1 := by exact_mod_cast mul_right_cancel₀ hα.ne' he
        omega
      omega
  exact ⟨by omega, hQR⟩

namespace Tiling

theorem five_le_corner_total_of_not_reptiling {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    5 ≤ ∑ j, d.cornerColumnCount j := by
  by_contra h
  exact hrep (d.reptiling_of_corner_total_le_four hscalene (by omega))

theorem right_corner_column_alternatives {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hαβ : d.tile.angle 0 < d.tile.angle 1)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    4 ≤ d.cornerColumnCount 0 ∧ d.cornerColumnCount 1 + d.cornerColumnCount 2 ≤ 1 := by
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, hright] at hc
  have ht := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at ht
  apply right_corner_small_columns (d.tile.angle 0) (d.tile.angle 1)
    (d.cornerColumnCount 0) (d.cornerColumnCount 1) (d.cornerColumnCount 2)
    (d.tile.angle_pos 0) hαβ _ hc ht
  linarith [d.tile.angle_sum]

end Tiling
end Erdos633b
