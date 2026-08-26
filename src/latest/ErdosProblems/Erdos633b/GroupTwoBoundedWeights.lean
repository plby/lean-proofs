import ErdosProblems.Erdos633b.GroupTwoOrderBounds
import ErdosProblems.Erdos633b.SmallTotientOrders
import ErdosProblems.Erdos633b.RationalSmallAngleOrder
import ErdosProblems.Erdos633b.IntegerAngleWeights

/-! Actual rational-angle group-2 tilings have positive common angle
weights with denominator at most 252. -/

namespace Erdos633b
namespace Triangle

theorem groupTwo_weights_of_phase (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (D j : ℕ) (hD : 0 < D) (hDb : D ≤ 42)
    (ha : S.angle 0 = 2 * Real.pi * j / D) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 252 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, S.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  let K : ℤ := 6 * (D : ℤ)
  let v : Fin 3 → ℤ := ![12 * (j : ℤ), 2 * (D : ℤ) - 12 * j, 4 * (D : ℤ)]
  have hK : K ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hD.ne')
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have ha0 : (K : ℝ) * S.angle 0 = (12 * (j : ℤ) : ℤ) * Real.pi := by
    rw [ha]
    dsimp only [K]
    push_cast
    field_simp [hDr]
    ring
  have hab : S.angle 0 + S.angle 1 = Real.pi / 3 := by linarith [S.angle_sum]
  have hv (i : Fin 3) : (K : ℝ) * S.angle i = (v i : ℝ) * Real.pi := by
    fin_cases i
    · exact ha0
    · change (K : ℝ) * S.angle 1 = ((2 * (D : ℤ) - 12 * j : ℤ) : ℝ) * Real.pi
      dsimp only [K] at ha0 ⊢
      push_cast at ha0 ⊢
      linear_combination 6 * (D : ℝ) * hab - ha0
    · change (K : ℝ) * S.angle 2 = ((4 * (D : ℤ) : ℤ) : ℝ) * Real.pi
      rw [hg]
      dsimp only [K]
      push_cast
      ring
  obtain ⟨hN, w, hw, hwp, hws⟩ := S.integer_angle_weights_of_scaled K hK v hv
  refine ⟨K.natAbs, hN, ?_, w, hw, hwp, hws⟩
  have hh : (K.natAbs : ℤ) ≤ 252 := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by dsimp [K]; positivity)]
    dsimp only [K]
    omega
  exact_mod_cast hh

end Triangle
namespace Tiling

theorem groupTwo_bounded_angle_weights {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)) (hs : GroupTwoShape d.tile T) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 252 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  have hg := hs.1
  have hsmall : d.tile.angle 0 < Real.pi / 3 := by
    linarith [d.tile.angle_sum, d.tile.angle_pos 1]
  obtain ⟨D, j, hD, _, _, _, ha, hz⟩ := d.tile.rational_small_angle_primitive_order hrat hsmall
  have hφ := d.groupTwo_order_totient_bound hs D (by omega) hz
  exact d.tile.groupTwo_weights_of_phase hg D j (by omega)
    (le_forty_two_of_totient_le_twelve D hφ) ha

end Tiling
end Erdos633b
