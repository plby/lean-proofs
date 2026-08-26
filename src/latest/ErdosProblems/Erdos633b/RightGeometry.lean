import ErdosProblems.Erdos633b.EdgeSplit
import ErdosProblems.Erdos633b.Similarity
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-! Metric certificates for the altitude partition of a right triangle. -/

namespace Erdos633b.Triangle

theorem right_inner (T : Triangle) (h : T.angle 2 = Real.pi / 2) :
    inner ℝ (T.points 0 - T.points 2) (T.points 1 - T.points 2) = 0 := by
  apply (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr
  exact h

theorem right_pythagoras (T : Triangle) (h : T.angle 2 = Real.pi / 2) :
    T.side 2 ^ 2 = T.side 0 ^ 2 + T.side 1 ^ 2 := by
  have hp := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
    (T.points 0) (T.points 2) (T.points 1)).mpr h
  change dist (T.points 0) (T.points 1) ^ 2 =
    dist (T.points 1) (T.points 2) ^ 2 + dist (T.points 2) (T.points 0) ^ 2
  rw [dist_comm (T.points 2) (T.points 0)]
  nlinarith

theorem edgePoint_dist_zero (T : Triangle) (w : ℝ) (hw : 0 ≤ w) :
    dist (T.edgePoint w) (T.points 0) = w * T.side 2 := by
  have hv : T.edgePoint w - T.points 0 = w • (T.points 1 - T.points 0) := by
    rw [edgePoint_eq]
    module
  rw [dist_eq_norm, hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw, ← dist_eq_norm]
  rw [dist_comm (T.points 1) (T.points 0)]
  rfl

theorem edgePoint_dist_one (T : Triangle) (w : ℝ) (hw : w ≤ 1) :
    dist (T.edgePoint w) (T.points 1) = (1 - w) * T.side 2 := by
  have hv : T.edgePoint w - T.points 1 = (1 - w) • (T.points 0 - T.points 1) := by
    rw [edgePoint_eq]
    module
  rw [dist_eq_norm, hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hw),
    ← dist_eq_norm]
  rfl

theorem right_edgePoint_dist_sq (T : Triangle) (h : T.angle 2 = Real.pi / 2) (w : ℝ) :
    dist (T.edgePoint w) (T.points 2) ^ 2 =
      (1 - w) ^ 2 * T.side 1 ^ 2 + w ^ 2 * T.side 0 ^ 2 := by
  have hv : T.edgePoint w - T.points 2 =
      (1 - w) • (T.points 0 - T.points 2) + w • (T.points 1 - T.points 2) := by
    rw [edgePoint_eq]
    module
  rw [dist_eq_norm, hv, norm_add_sq_real]
  have hx : ‖T.points 0 - T.points 2‖ = T.side 1 := by
    rw [← dist_eq_norm, dist_comm]
    rfl
  have hy : ‖T.points 1 - T.points 2‖ = T.side 0 := rfl
  simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left, inner_smul_right,
    T.right_inner h, mul_zero, add_zero, mul_pow, sq_abs, hx, hy]

theorem right_weight_bounds (T : Triangle) (h : T.angle 2 = Real.pi / 2) :
    0 < T.side 1 ^ 2 / T.side 2 ^ 2 ∧ T.side 1 ^ 2 / T.side 2 ^ 2 < 1 := by
  have hp := T.right_pythagoras h
  have ha := sq_pos_of_pos (T.side_pos 0)
  have hb := sq_pos_of_pos (T.side_pos 1)
  have hc := sq_pos_of_pos (T.side_pos 2)
  exact ⟨div_pos hb hc, (div_lt_one hc).mpr (by linarith)⟩

theorem right_weight_complement (T : Triangle) (h : T.angle 2 = Real.pi / 2) :
    1 - T.side 1 ^ 2 / T.side 2 ^ 2 = T.side 0 ^ 2 / T.side 2 ^ 2 := by
  apply (eq_div_iff (sq_pos_of_pos (T.side_pos 2)).ne').mpr
  field_simp [(T.side_pos 2).ne']
  nlinarith [T.right_pythagoras h]

theorem right_edgePoint_height (T : Triangle) (h : T.angle 2 = Real.pi / 2) :
    dist (T.edgePoint (T.side 1 ^ 2 / T.side 2 ^ 2)) (T.points 2) =
      T.side 0 * T.side 1 / T.side 2 := by
  have hp := T.right_pythagoras h
  have hs := T.right_edgePoint_dist_sq h (T.side 1 ^ 2 / T.side 2 ^ 2)
  rw [T.right_weight_complement h] at hs
  have he : (T.side 0 ^ 2 / T.side 2 ^ 2) ^ 2 * T.side 1 ^ 2 +
      (T.side 1 ^ 2 / T.side 2 ^ 2) ^ 2 * T.side 0 ^ 2 =
      (T.side 0 * T.side 1 / T.side 2) ^ 2 := by
    field_simp [(T.side_pos 2).ne']
    linear_combination -(T.side 0 ^ 2 * T.side 1 ^ 2) * hp
  rw [he] at hs
  have hpos := div_pos (mul_pos (T.side_pos 0) (T.side_pos 1)) (T.side_pos 2)
  nlinarith [dist_nonneg (x := T.edgePoint (T.side 1 ^ 2 / T.side 2 ^ 2)) (y := T.points 2)]

theorem right_edgeFirst_sides (T : Triangle) (h : T.angle 2 = Real.pi / 2) :
    let w := T.side 1 ^ 2 / T.side 2 ^ 2
    let R := T.edgeFirst w (T.right_weight_bounds h).1
    R.side 0 = T.side 1 ^ 2 / T.side 2 ∧
      R.side 1 = T.side 0 * T.side 1 / T.side 2 ∧ R.side 2 = T.side 1 := by
  let w := T.side 1 ^ 2 / T.side 2 ^ 2
  let R := T.edgeFirst w (T.right_weight_bounds h).1
  have hv : R.points = ![T.points 2, T.points 0, T.edgePoint w] := T.edgeFirst_points _ _
  have hside (i : Fin 3) : R.side i =
      dist (![T.points 2, T.points 0, T.edgePoint w] (i + 1))
        (![T.points 2, T.points 0, T.edgePoint w] (i + 2)) := by
    change dist (R.points (i + 1)) (R.points (i + 2)) = _
    rw [hv]
  change R.side 0 = _ ∧ R.side 1 = _ ∧ R.side 2 = _
  rw [hside, hside, hside]
  constructor
  · change dist (T.points 0) (T.edgePoint _) = _
    rw [dist_comm, T.edgePoint_dist_zero _ (T.right_weight_bounds h).1.le]
    field_simp
  constructor
  · exact T.right_edgePoint_height h
  · rfl

theorem right_edgeSecond_sides (T : Triangle) (h : T.angle 2 = Real.pi / 2) :
    let w := T.side 1 ^ 2 / T.side 2 ^ 2
    let S := T.edgeSecond w (T.right_weight_bounds h).2
    S.side 0 = T.side 0 ^ 2 / T.side 2 ∧
      S.side 1 = T.side 0 * T.side 1 / T.side 2 ∧ S.side 2 = T.side 0 := by
  let w := T.side 1 ^ 2 / T.side 2 ^ 2
  let S := T.edgeSecond w (T.right_weight_bounds h).2
  have hv : S.points = ![T.points 2, T.points 1, T.edgePoint w] := T.edgeSecond_points _ _
  have hside (i : Fin 3) : S.side i =
      dist (![T.points 2, T.points 1, T.edgePoint w] (i + 1))
        (![T.points 2, T.points 1, T.edgePoint w] (i + 2)) := by
    change dist (S.points (i + 1)) (S.points (i + 2)) = _
    rw [hv]
  change S.side 0 = _ ∧ S.side 1 = _ ∧ S.side 2 = _
  rw [hside, hside, hside]
  constructor
  · change dist (T.points 1) (T.edgePoint _) = _
    rw [dist_comm, T.edgePoint_dist_one _ (T.right_weight_bounds h).2.le,
      T.right_weight_complement h]
    field_simp
  constructor
  · exact T.right_edgePoint_height h
  · exact dist_comm _ _

end Erdos633b.Triangle
