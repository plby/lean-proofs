import ErdosProblems.Erdos633b.Similarity

/-! The similarity scale of an actual ordered reptiling is the positive square root
of its number of pieces. The proof uses area additivity, not boundary alignment. -/

namespace Erdos633b

namespace Triangle

theorem area_move (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    (T.move g).area = T.area := by
  unfold area
  rw [support_move, volume_rigidMotion_support]

theorem area_eq_sq_ratio_of_angles (S T : Triangle)
    (h : ∀ i, S.angle i = T.angle i) :
    T.area = (T.side 0 / S.side 0) ^ 2 * S.area := by
  let r : ℝ := T.side 0 / S.side 0
  have hr : r ≠ 0 := div_ne_zero (T.side_pos 0).ne' (S.side_pos 0).ne'
  let U : Triangle := S.dilate r hr
  have hs : ∀ i, U.side i = T.side i := S.dilate_sides_of_angles T h
  have hd := U.distances_of_sides T hs
  calc
    T.area = (U.move (U.vertexIsometry T hd)).area := by rw [U.move_vertexIsometry T hd]
    _ = U.area := U.area_move _
    _ = r ^ 2 * S.area := S.area_dilate r hr

end Triangle

namespace Tiling

theorem side_ratio_sq_of_angles {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i) :
    (T.side 0 / d.tile.side 0) ^ 2 = (n : ℝ) := by
  apply mul_right_cancel₀ d.tile.area_pos.ne'
  exact (d.tile.area_eq_sq_ratio_of_angles T h).symm.trans d.area_eq_mul

theorem side_ratio_eq_sqrt_of_angles {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i) :
    T.side 0 / d.tile.side 0 = Real.sqrt n := by
  have hr := div_pos (T.side_pos 0) (d.tile.side_pos 0)
  rw [← d.side_ratio_sq_of_angles h, Real.sqrt_sq_eq_abs, abs_of_pos hr]

theorem side_eq_sqrt_mul_of_angles {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i) (i : Fin 3) :
    T.side i = Real.sqrt n * d.tile.side i := by
  rw [d.tile.side_ratio_of_angles T h i, d.side_ratio_eq_sqrt_of_angles h]

end Tiling

end Erdos633b
