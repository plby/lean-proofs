import ErdosProblems.Erdos633b.ReptilingScale
import ErdosProblems.Erdos633b.RationalSides
import Mathlib.Data.Rat.Lemmas

/-! Compare exact counts using two genuine tilings and proved similarity/area scaling. -/

namespace Erdos633b

namespace Triangle

theorem area_eq_sq_ratio_of_angles_at (S T : Triangle)
    (h : ∀ i, S.angle i = T.angle i) (i : Fin 3) :
    T.area = (T.side i / S.side i) ^ 2 * S.area := by
  have hr : T.side i / S.side i = T.side 0 / S.side 0 := by
    rw [S.side_ratio_of_angles T h i]
    exact mul_div_cancel_right₀ _ (S.side_pos i).ne'
  rw [hr]
  exact S.area_eq_sq_ratio_of_angles T h

end Triangle

namespace Tiling

theorem count_comparison {T U : Triangle} {n m : ℕ} (d : Tiling T n) (e : Tiling U m)
    (hout : ∀ i, U.angle i = T.angle i) (htile : ∀ i, e.tile.angle i = d.tile.angle i)
    (i : Fin 3) :
    (n : ℝ) = ((T.side i / U.side i) / (d.tile.side i / e.tile.side i)) ^ 2 * m := by
  let x := T.side i / U.side i
  let y := d.tile.side i / e.tile.side i
  have hT : T.area = x ^ 2 * U.area := U.area_eq_sq_ratio_of_angles_at T hout i
  have hS : d.tile.area = y ^ 2 * e.tile.area :=
    e.tile.area_eq_sq_ratio_of_angles_at d.tile htile i
  have hbase : (n : ℝ) * y ^ 2 = x ^ 2 * m := by
    apply mul_right_cancel₀ e.tile.area_pos.ne'
    linear_combination hT - d.area_eq_mul - (n : ℝ) * hS + x ^ 2 * e.area_eq_mul
  have hy : y ≠ 0 := div_ne_zero (d.tile.side_pos i).ne' (e.tile.side_pos i).ne'
  change (n : ℝ) = (x / y) ^ 2 * m
  rw [div_pow, div_mul_eq_mul_div]
  exact (eq_div_iff (pow_ne_zero 2 hy)).mpr hbase

theorem square_count_of_comparison {T U : Triangle} {n m : ℕ}
    (d : Tiling T n) (e : Tiling U m)
    (hout : ∀ i, U.angle i = T.angle i) (htile : ∀ i, e.tile.angle i = d.tile.angle i)
    (i : Fin 3)
    (hq : IsRational ((T.side i / U.side i) / (d.tile.side i / e.tile.side i)))
    (hm : IsSquare m) : IsSquare n := by
  obtain ⟨q, hq⟩ := hq
  have hc := d.count_comparison e hout htile i
  rw [← hq] at hc
  have hqcount : (n : ℚ) = q ^ 2 * m := by exact_mod_cast hc
  apply Rat.isSquare_natCast_iff.mp
  rw [hqcount]
  exact (IsSquare.sq q).mul (Rat.isSquare_natCast_iff.mpr hm)

end Tiling

end Erdos633b
