import ErdosProblems.Erdos633b.EdgeExtension
import ErdosProblems.Erdos633b.DoubledAngles

/-! Explicit coordinates and exact side lengths for the tile attached in case (5). -/

namespace Erdos633b

theorem Triangle.extendedPoint_dist (T : Triangle) (t : ℝ) (ht : 0 < t) :
    dist (T.extendedPoint t) (T.points 2) = t * T.side 0 := by
  have hv : T.extendedPoint t - T.points 2 = t • (T.points 2 - T.points 1) := by
    dsimp only [extendedPoint]
    module
  rw [dist_eq_norm, hv, norm_smul, Real.norm_of_nonneg ht.le]
  change t * ‖T.points 2 - T.points 1‖ = t * dist (T.points 1) (T.points 2)
  rw [dist_eq_norm, norm_sub_rev]

namespace CaseFiveCoordinates

open Sixty

noncomputable def extensionRatio (a b : ℝ) : ℝ := (a + 2 * b) / (2 * a + b)

theorem extensionRatio_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < extensionRatio a b := by
  unfold extensionRatio
  positivity

noncomputable def tip (d a b c m : ℝ) : Plane :=
  point d (m * (a + 2 * b) * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3) / c ^ 2)
    (3 * m * a * b * (a + 2 * b) * (a + b) / c ^ 2)

theorem extendedPoint_eq (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (DoubledCoordinates.outer d hd a b c m ha hb hc hm).extendedPoint (extensionRatio a b) =
      tip d a b c m := by
  have hQ : 0 < 2 * a + b := by linarith
  have hC : a ^ 2 + a * b + b ^ 2 ≠ 0 := by rw [← hrel]; exact (sq_pos_of_pos hc).ne'
  rw [Triangle.extendedPoint, DoubledCoordinates.outer_points]
  change (1 + extensionRatio a b) • DoubledCoordinates.bigC d a b c m -
    extensionRatio a b • DoubledCoordinates.bigB d c m = tip d a b c m
  rw [DoubledCoordinates.bigC, DoubledCoordinates.bigB, ← point_smul, ← point_smul, point_sub]
  unfold tip
  congr 1 <;> dsimp only [extensionRatio, DoubledCoordinates.cX, DoubledCoordinates.cY] <;>
    rw [hrel] <;> field_simp <;> ring

theorem tip_norm (d : ℝ) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) : ‖tip d a b c m‖ = m * (a + 2 * b) * c := by
  have hC : a ^ 2 + a * b + b ^ 2 ≠ 0 := by rw [← hrel]; exact (sq_pos_of_pos hc).ne'
  have hs : ‖tip d a b c m‖ ^ 2 = (m * (a + 2 * b) * c) ^ 2 := by
    rw [tip, point_norm_sq d he]
    simp only [div_pow, mul_pow, hrel]
    field_simp
    ring
  have hp : 0 < m * (a + 2 * b) * c := by positivity
  nlinarith [norm_nonneg (tip d a b c m)]

noncomputable def outer (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m) : Triangle :=
  (DoubledCoordinates.outer d hd a b c m ha hb hc hm).edgeExtension
    (extensionRatio a b) (extensionRatio_pos a b ha hb)

noncomputable def attached (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m) : Triangle :=
  (outer d hd a b c m ha hb hc hm).edgeSecond (1 / (1 + extensionRatio a b))
    (Triangle.extension_weight_lt_one _ (extensionRatio_pos a b ha hb))

theorem attached_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 3) :
    (attached d hd a b c m ha hb hc hm).side i = m * (a + 2 * b) * ![b, a, c] i := by
  let S := DoubledCoordinates.outer d hd a b c m ha hb hc hm
  let V := attached d hd a b c m ha hb hc hm
  have hv : V.points = ![S.points 0, S.extendedPoint (extensionRatio a b), S.points 2] :=
    S.edgeExtension_second_points _ (extensionRatio_pos a b ha hb)
  fin_cases i
  · change dist (V.points 1) (V.points 2) = m * (a + 2 * b) * b
    rw [hv]
    change dist (S.extendedPoint (extensionRatio a b)) (S.points 2) = _
    rw [S.extendedPoint_dist _ (extensionRatio_pos a b ha hb),
      DoubledCoordinates.outer_sides d hd he a b c m ha hb hc hm hrel]
    change extensionRatio a b * (m * b * (2 * a + b)) = m * (a + 2 * b) * b
    have hQ : 0 < 2 * a + b := by linarith
    unfold extensionRatio
    field_simp
  · change dist (V.points 2) (V.points 0) = m * (a + 2 * b) * a
    rw [hv]
    change S.side 1 = m * (a + 2 * b) * a
    rw [DoubledCoordinates.outer_sides d hd he a b c m ha hb hc hm hrel]
    change m * a * (a + 2 * b) = m * (a + 2 * b) * a
    ring
  · change dist (V.points 0) (V.points 1) = m * (a + 2 * b) * c
    rw [hv]
    change dist (S.points 0) (S.extendedPoint (extensionRatio a b)) = _
    rw [DoubledCoordinates.outer_zero, extendedPoint_eq d hd a b c m ha hb hc hm hrel,
      dist_zero_left, tip_norm d he a b c m ha hb hc hm hrel]

end CaseFiveCoordinates
end Erdos633b
