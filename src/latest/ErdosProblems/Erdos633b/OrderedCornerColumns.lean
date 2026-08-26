import ErdosProblems.Erdos633b.RightCornerAlternatives

/-! Small outer-corner column bounds for strictly ordered reference angles,
without assuming commensurability or a classification theorem. -/

namespace Erdos633b

theorem ordered_corner_last_column_le_one (α β γ : ℝ) (P Q R : ℕ)
    (hα : 0 < α) (hαβ : α < β) (hβγ : β < γ) (hs : α + β + γ = Real.pi)
    (hc : (P : ℝ) * α + (Q : ℝ) * β + (R : ℝ) * γ = Real.pi)
    (ht : 5 ≤ P + Q + R) : R ≤ 1 := by
  have hγ : Real.pi / 3 < γ := by linarith
  have hp : 0 ≤ (P : ℝ) * α := mul_nonneg (Nat.cast_nonneg _) hα.le
  have hq : 0 ≤ (Q : ℝ) * β := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hR2 : R ≤ 2 := by
    by_contra hn
    have hR3 : (3 : ℝ) ≤ R := by exact_mod_cast (show 3 ≤ R by omega)
    have hm := mul_le_mul_of_nonneg_right hR3 (show 0 ≤ γ by linarith)
    linarith
  by_contra hn
  have hR : R = 2 := by omega
  have hPQ : (3 : ℝ) ≤ (P : ℝ) + Q := by exact_mod_cast (show 3 ≤ P + Q by omega)
  have hm := mul_le_mul_of_nonneg_right hPQ hα.le
  have hQ := mul_le_mul_of_nonneg_left hαβ.le (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)
  rw [hR] at hc
  norm_num at hc
  nlinarith

theorem ordered_corner_last_one (α β γ : ℝ) (P Q : ℕ)
    (hα : 0 < α) (hαβ : α < β) (hs : α + β + γ = Real.pi)
    (hc : (P : ℝ) * α + (Q : ℝ) * β + γ = Real.pi)
    (ht : 4 ≤ P + Q) : Q = 0 ∧ 4 ≤ P := by
  have hβ : 0 < β := hα.trans hαβ
  have hPpos : 0 < P := by
    by_contra hn
    have hP0 : P = 0 := by omega
    have hQ4 : (4 : ℝ) ≤ Q := by exact_mod_cast (show 4 ≤ Q by omega)
    have hm := mul_le_mul_of_nonneg_right hQ4 hβ.le
    rw [hP0] at hc
    norm_num at hc
    linarith
  have hQ0 : Q = 0 := by
    by_contra hn
    have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hPpos
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hP := mul_le_mul_of_nonneg_right hP1 hα.le
    have hQ := mul_le_mul_of_nonneg_right hQ1 hβ.le
    have heP : (P : ℝ) * α = 1 * α := by linarith
    have heQ : (Q : ℝ) * β = 1 * β := by linarith
    have hPnat : P = 1 := by exact_mod_cast mul_right_cancel₀ hα.ne' heP
    have hQnat : Q = 1 := by exact_mod_cast mul_right_cancel₀ hβ.ne' heQ
    omega
  exact ⟨hQ0, by omega⟩

namespace Tiling

theorem ordered_corner_columns {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    d.cornerColumnCount 2 ≤ 1 ∧ (d.cornerColumnCount 2 = 1 →
      d.cornerColumnCount 1 = 0 ∧ 4 ≤ d.cornerColumnCount 0) := by
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  have ht := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at ht
  refine ⟨ordered_corner_last_column_le_one _ _ _ _ _ _ (d.tile.angle_pos 0)
    h01 h12 d.tile.angle_sum hc ht, ?_⟩
  intro hR
  rw [hR] at hc ht
  norm_num at hc
  exact ordered_corner_last_one _ _ _ _ _ (d.tile.angle_pos 0) h01 d.tile.angle_sum hc
    (by omega)

theorem ordered_middle_angle_gt_pi_six {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3) :
    Real.pi / 6 < d.tile.angle 1 := by linarith [d.tile.angle_sum]

theorem ordered_middle_column_le_five {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3) :
    d.cornerColumnCount 1 ≤ 5 := by
  have hβ := d.ordered_middle_angle_gt_pi_six h01 hγ
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  have hp : 0 ≤ (d.cornerColumnCount 0 : ℝ) * d.tile.angle 0 :=
    mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 0).le
  have hr : 0 ≤ (d.cornerColumnCount 2 : ℝ) * d.tile.angle 2 :=
    mul_nonneg (Nat.cast_nonneg _) (d.tile.angle_pos 2).le
  by_contra hn
  have hQ : (6 : ℝ) ≤ d.cornerColumnCount 1 := by
    exact_mod_cast (show 6 ≤ d.cornerColumnCount 1 by omega)
  have hm := mul_le_mul_of_nonneg_right hQ (d.tile.angle_pos 1).le
  linarith

end Tiling
end Erdos633b
