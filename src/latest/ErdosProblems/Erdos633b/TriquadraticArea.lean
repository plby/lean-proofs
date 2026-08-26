import ErdosProblems.Erdos633b.AffineAreaScaling

/-! The real-parameter case-(7) outer/reference area ratio follows from an
explicit linear map of determinant -(2-s^2), before any rationality assumption. -/

namespace Erdos633b.TriquadraticCoordinates

noncomputable def areaMap (s d : ℝ) : Plane →ₗ[ℝ] Plane :=
  Matrix.toEuclideanLin !![1 - 2 * s ^ 2 + s ^ 4 / 2,
    (1 - (1 - s ^ 2 / 2) * (1 - 2 * s ^ 2 + s ^ 4 / 2)) / (s * d / 2);
    (2 - s ^ 2) * (s * d / 2), -(1 - s ^ 2 / 2) * (2 - s ^ 2)]

theorem areaMap_apply (s d : ℝ) (p : Plane) :
    areaMap s d p = !₂[(1 - 2 * s ^ 2 + s ^ 4 / 2) * p 0 +
      ((1 - (1 - s ^ 2 / 2) * (1 - 2 * s ^ 2 + s ^ 4 / 2)) / (s * d / 2)) * p 1,
      ((2 - s ^ 2) * (s * d / 2)) * p 0 - (1 - s ^ 2 / 2) * (2 - s ^ 2) * p 1] := by
  ext i
  fin_cases i
  · simp [areaMap, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two]
  · simp [areaMap, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two]
    ring

theorem areaMap_det (s d : ℝ) (hs : s ≠ 0) (hd : d ≠ 0) :
    LinearMap.det (areaMap s d) = -(2 - s ^ 2) := by
  rw [areaMap, det_plane_matrix, Matrix.det_fin_two]
  change (1 - 2 * s ^ 2 + s ^ 4 / 2) * (-(1 - s ^ 2 / 2) * (2 - s ^ 2)) -
    ((1 - (1 - s ^ 2 / 2) * (1 - 2 * s ^ 2 + s ^ 4 / 2)) / (s * d / 2)) *
      ((2 - s ^ 2) * (s * d / 2)) = -(2 - s ^ 2)
  field_simp [hs, hd]
  ring

theorem areaMap_vertices (s d : ℝ) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) (i : Fin 3) :
    (outer 1 s d (by norm_num) hs hs1 hd).points i =
      areaMap s d ((reference 1 s d (by norm_num) hs hs1 hd).points i) := by
  rw [areaMap_apply]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [outer, reference, bigB, bigC, w] <;>
    field_simp [hs.ne', hd.ne'] <;> ring

theorem normalized_outer_area (s d : ℝ) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    (outer 1 s d (by norm_num) hs hs1 hd).area =
      (2 - s ^ 2) * (reference 1 s d (by norm_num) hs hs1 hd).area := by
  have h := (reference 1 s d (by norm_num) hs hs1 hd).area_eq_abs_det_mul
    (outer 1 s d (by norm_num) hs hs1 hd) (areaMap s d) (areaMap_vertices s d hs hs1 hd)
  rw [areaMap_det s d hs.ne' hd.ne', abs_neg,
    abs_of_pos (parameter_denominator_pos s hs hs1).2] at h
  exact h

end Erdos633b.TriquadraticCoordinates
