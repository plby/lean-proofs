import ErdosProblems.Erdos633b.BarycentricTriangle
import ErdosProblems.Erdos633b.EdgeSplit

/-! Extend a triangle beyond its third vertex and recover it as an exact edge piece. -/

namespace Erdos633b.Triangle

noncomputable def extendedPoint (T : Triangle) (t : ℝ) : Plane :=
  (1 + t) • T.points 2 - t • T.points 1

noncomputable def edgeExtension (T : Triangle) (t : ℝ) (ht : 0 < t) : Triangle :=
  T.ofCoords 1 0 (-t) (1 + t) 0 0 (by simpa using (show 0 < 1 + t by linarith).ne')

theorem edgeExtension_points (T : Triangle) (t : ℝ) (ht : 0 < t) :
    (T.edgeExtension t ht).points = ![T.points 1, T.extendedPoint t, T.points 0] := by
  funext i
  rw [edgeExtension, ofCoords_point]
  fin_cases i
  · change T.latticeShift 1 0 + T.points 0 = T.points 1
    simp [latticeShift, edgeVector]
  · change T.latticeShift (-t) (1 + t) + T.points 0 = T.extendedPoint t
    dsimp only [latticeShift, edgeVector, extendedPoint]
    module
  · change T.latticeShift 0 0 + T.points 0 = T.points 0
    simp [latticeShift]

theorem extension_weight_pos (t : ℝ) (ht : 0 < t) : 0 < 1 / (1 + t) := by positivity

theorem extension_weight_lt_one (t : ℝ) (ht : 0 < t) : 1 / (1 + t) < 1 := by
  apply (div_lt_one (by linarith : 0 < 1 + t)).mpr
  linarith

theorem edgeExtension_edgePoint (T : Triangle) (t : ℝ) (ht : 0 < t) :
    (T.edgeExtension t ht).edgePoint (1 / (1 + t)) = T.points 2 := by
  have hp : 0 < 1 + t := by linarith
  have h1 : (1 / (1 + t)) * (1 + t) = 1 := by field_simp
  have h0 : 1 - 1 / (1 + t) - (1 / (1 + t)) * t = 0 := by field_simp; ring
  calc
    _ = (1 - 1 / (1 + t) - (1 / (1 + t)) * t) • T.points 1 +
        ((1 / (1 + t)) * (1 + t)) • T.points 2 := by
      rw [edgePoint_eq, edgeExtension_points]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, extendedPoint]
      module
    _ = T.points 2 := by rw [h0, h1]; simp

theorem edgeExtension_first (T : Triangle) (t : ℝ) (ht : 0 < t) :
    (T.edgeExtension t ht).edgeFirst (1 / (1 + t)) (extension_weight_pos t ht) = T := by
  apply Affine.Simplex.ext
  intro i
  rw [edgeFirst_points, edgeExtension_edgePoint, edgeExtension_points]
  fin_cases i <;> rfl

theorem edgeExtension_second_points (T : Triangle) (t : ℝ) (ht : 0 < t) :
    ((T.edgeExtension t ht).edgeSecond (1 / (1 + t)) (extension_weight_lt_one t ht)).points =
      ![T.points 0, T.extendedPoint t, T.points 2] := by
  rw [edgeSecond_points, edgeExtension_edgePoint, edgeExtension_points]
  rfl

theorem edgeExtension_angle_zero (T : Triangle) (t : ℝ) (ht : 0 < t) :
    (T.edgeExtension t ht).angle 0 = T.angle 1 := by
  have hz : T.extendedPoint t - T.points 1 = (1 + t) • (T.points 2 - T.points 1) := by
    dsimp only [extendedPoint]
    module
  change InnerProductGeometry.angle
    ((T.edgeExtension t ht).points 1 - (T.edgeExtension t ht).points 0)
    ((T.edgeExtension t ht).points 2 - (T.edgeExtension t ht).points 0) = _
  rw [edgeExtension_points]
  change InnerProductGeometry.angle (T.extendedPoint t - T.points 1) (T.points 0 - T.points 1) = _
  rw [hz, InnerProductGeometry.angle_smul_left_of_pos _ _ (by linarith : 0 < 1 + t)]
  rfl

theorem edgeExtension_angle_one (T : Triangle) (t : ℝ) (ht : 0 < t) :
    (T.edgeExtension t ht).angle 1 =
      ((T.edgeExtension t ht).edgeSecond (1 / (1 + t)) (extension_weight_lt_one t ht)).angle 1 := by
  have hp : 0 < 1 + t := by linarith
  have hc : T.points 2 - T.extendedPoint t =
      (t / (1 + t)) • (T.points 1 - T.extendedPoint t) := by
    have heq : (t / (1 + t)) * (1 + t) = t := by field_simp
    calc
      _ = -t • (T.points 2 - T.points 1) := by dsimp only [extendedPoint]; module
      _ = (t / (1 + t)) • (-(1 + t) • (T.points 2 - T.points 1)) := by
        rw [smul_smul, mul_neg, heq]
      _ = _ := by dsimp only [extendedPoint]; module
  change InnerProductGeometry.angle
    ((T.edgeExtension t ht).points 2 - (T.edgeExtension t ht).points 1)
    ((T.edgeExtension t ht).points 0 - (T.edgeExtension t ht).points 1) =
    InnerProductGeometry.angle
      (((T.edgeExtension t ht).edgeSecond (1 / (1 + t)) (extension_weight_lt_one t ht)).points 2 -
        ((T.edgeExtension t ht).edgeSecond (1 / (1 + t)) (extension_weight_lt_one t ht)).points 1)
      (((T.edgeExtension t ht).edgeSecond (1 / (1 + t)) (extension_weight_lt_one t ht)).points 0 -
        ((T.edgeExtension t ht).edgeSecond (1 / (1 + t)) (extension_weight_lt_one t ht)).points 1)
  rw [edgeExtension_second_points, edgeExtension_points]
  change InnerProductGeometry.angle
      (T.points 0 - T.extendedPoint t) (T.points 1 - T.extendedPoint t) =
    InnerProductGeometry.angle (T.points 2 - T.extendedPoint t) (T.points 0 - T.extendedPoint t)
  rw [hc, InnerProductGeometry.angle_smul_left_of_pos _ _ (div_pos ht hp)]
  exact InnerProductGeometry.angle_comm _ _

end Erdos633b.Triangle
