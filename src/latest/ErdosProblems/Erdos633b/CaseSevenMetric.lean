import ErdosProblems.Erdos633b.TriquadraticArea
import ErdosProblems.Erdos633b.TilingSquareClass

/-! Exact side and area scaling for case (7), valid before side rationality. -/

namespace Erdos633b
namespace Triangle

theorem groupOne_parameter_bounds (S : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi) :
    0 < 2 * Real.sin (S.angle 0 / 2) ∧ 2 * Real.sin (S.angle 0 / 2) < 1 := by
  obtain ⟨ha, hb⟩ := S.groupOne_side_ratios hrel
  have hpos : 0 < 2 * Real.sin (S.angle 0 / 2) := by
    rw [← ha]
    exact div_pos (S.side_pos 0) (S.side_pos 2)
  have hsq : 0 < 1 - (2 * Real.sin (S.angle 0 / 2)) ^ 2 := by
    rw [← hb]
    exact div_pos (S.side_pos 1) (S.side_pos 2)
  exact ⟨hpos, by nlinarith⟩

theorem caseSeven_side_scale (S T : Triangle)
    (h0 : T.angle 0 = 2 * S.angle 0) (h1 : T.angle 1 = S.angle 1)
    (h2 : T.angle 2 = S.angle 0 + S.angle 1) :
    T.side 0 = (T.side 1 / S.side 1) *
      ((2 - (2 * Real.sin (S.angle 0 / 2)) ^ 2) * S.side 0) ∧
      T.side 2 = (T.side 1 / S.side 1) * S.side 2 := by
  have hc : 2 * Real.cos (S.angle 0) = 2 - (2 * Real.sin (S.angle 0 / 2)) ^ 2 := by
    have hh : Real.cos (S.angle 0) = 2 * Real.cos (S.angle 0 / 2) ^ 2 - 1 := by
      convert Real.cos_two_mul (S.angle 0 / 2) using 1
      congr 1
      ring
    nlinarith [Real.sin_sq_add_cos_sq (S.angle 0 / 2)]
  have hs : Real.sin (2 * S.angle 0) =
      (2 - (2 * Real.sin (S.angle 0 / 2)) ^ 2) * Real.sin (S.angle 0) := by
    rw [Real.sin_two_mul, ← hc]
    ring
  have hg : Real.sin (S.angle 0 + S.angle 1) = Real.sin (S.angle 2) := by
    rw [show S.angle 0 + S.angle 1 = Real.pi - S.angle 2 by linarith [S.angle_sum],
      Real.sin_pi_sub]
  have hX : T.side 0 / T.side 1 = (2 - (2 * Real.sin (S.angle 0 / 2)) ^ 2) *
      (S.side 0 / S.side 1) := by
    rw [T.side_ratio_eq_sine_ratio, S.side_ratio_eq_sine_ratio, h0, h1, hs]
    ring
  have hZ : T.side 2 / T.side 1 = S.side 2 / S.side 1 := by
    rw [T.side_ratio_eq_sine_ratio, S.side_ratio_eq_sine_ratio, h2, h1, hg]
  constructor
  · field_simp [(T.side_pos 1).ne', (S.side_pos 1).ne'] at hX ⊢
    nlinarith [hX]
  · field_simp [(T.side_pos 1).ne', (S.side_pos 1).ne'] at hZ ⊢
    nlinarith [hZ]

end Triangle
namespace Tiling

open TriquadraticCoordinates

theorem caseSeven_area_scale {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    (n : ℝ) = (T.side 1 / d.tile.side 1) ^ 2 *
      (2 - (2 * Real.sin (d.tile.angle 0 / 2)) ^ 2) := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  let s := 2 * Real.sin (d.tile.angle 0 / 2)
  obtain ⟨hs, hs1⟩ := d.tile.groupOne_parameter_bounds hrel
  change 0 < s at hs
  change s < 1 at hs1
  let v := Real.sqrt (4 - s ^ 2)
  have hrad : 0 < 4 - s ^ 2 := by nlinarith
  have hv : 0 < v := Real.sqrt_pos.mpr hrad
  have hv2 : v ^ 2 = 4 - s ^ 2 := Real.sq_sqrt hrad.le
  let R := reference 1 s v (by norm_num) hs hs1 hv
  let U := outer 1 s v (by norm_num) hs hs1 hv
  have hR : ∀ i, R.angle i = d.tile.angle i :=
    reference_angles_of_groupOne d.tile hrel 1 s v (by norm_num) hs hs1 hv hv2 rfl
  have hU : ∀ i, U.angle i = T.angle i :=
    outer_angles_of_groupOne d.tile T h0 h1 h2 1 s v (by norm_num) hs hs1 hv hv2 rfl
  have hRs : R.side 1 = 1 - s ^ 2 := by
    simpa only [R, Matrix.cons_val_one, Matrix.cons_val_zero, one_mul] using
      reference_sides 1 s v (by norm_num) hs hs1 hv hv2 1
  have hUs : U.side 1 = 1 - s ^ 2 := by
    simpa only [U, one_pow, one_mul] using outer_side_one 1 s v (by norm_num) hs hs1 hv
  have hTa := U.area_eq_sq_ratio_of_angles_at T hU 1
  have hSa := R.area_eq_sq_ratio_of_angles_at d.tile hR 1
  have hUa : U.area = (2 - s ^ 2) * R.area := normalized_outer_area s v hs hs1 hv
  rw [hUs, hUa] at hTa
  rw [hRs] at hSa
  have hbase : (n : ℝ) * (d.tile.side 1 / (1 - s ^ 2)) ^ 2 =
      (T.side 1 / (1 - s ^ 2)) ^ 2 * (2 - s ^ 2) := by
    apply mul_right_cancel₀ R.area_pos.ne'
    linear_combination hTa - d.area_eq_mul - (n : ℝ) * hSa
  have hb : 1 - s ^ 2 ≠ 0 := (parameter_denominator_pos s hs hs1).1.ne'
  have hx : T.side 1 / (1 - s ^ 2) =
      (T.side 1 / d.tile.side 1) * (d.tile.side 1 / (1 - s ^ 2)) := by
    field_simp [(d.tile.side_pos 1).ne']
  apply mul_right_cancel₀ (pow_ne_zero 2 (div_ne_zero (d.tile.side_pos 1).ne' hb))
  change (n : ℝ) * (d.tile.side 1 / (1 - s ^ 2)) ^ 2 =
    ((T.side 1 / d.tile.side 1) ^ 2 * (2 - s ^ 2)) *
      (d.tile.side 1 / (1 - s ^ 2)) ^ 2
  rw [hbase, hx]
  ring

end Tiling
end Erdos633b
