import ErdosProblems.Erdos633b.DoubledParameters
import ErdosProblems.Erdos633b.DoubledTriangles
import ErdosProblems.Erdos633b.SixtyAngles

/-! The explicit Euclidean outer triangle and its interior vertices for the doubled construction. -/

namespace Erdos633b.DoubledCoordinates

open Sixty

noncomputable def cX (a b c m : ℝ) : ℝ := m * a * (a + 2 * b) * (a - b) * (a + b) / c ^ 2
noncomputable def cY (a b c m : ℝ) : ℝ := m * a * b * (a + 2 * b) * (2 * a + b) / c ^ 2
noncomputable def bigB (d c m : ℝ) : Plane := point d (m * c ^ 2) 0
noncomputable def bigC (d a b c m : ℝ) : Plane := point d (cX a b c m) (cY a b c m)
noncomputable def pointD (d a b m : ℝ) : Plane := point d (m * a ^ 2) (m * a * b)
noncomputable def pointG (d a b m : ℝ) : Plane := point d (m * a * (a - b)) (m * a * (a + 2 * b))
noncomputable def pointE (d a b m : ℝ) : Plane := (2 * a / (a + b)) • pointD d a b m
noncomputable def pointF (d a b c m : ℝ) : Plane :=
  (2 * c ^ 2 / ((a + b) * (a + 2 * b))) • bigC d a b c m

theorem cY_pos (a b c m : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m) :
    0 < cY a b c m := by
  unfold cY
  positivity

noncomputable def outer (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m) : Triangle :=
  triangle d hd 0 0 (m * c ^ 2) 0 (cX a b c m) (cY a b c m) (by
    simpa using (mul_pos (mul_pos hm (sq_pos_of_pos hc)) (cY_pos a b c m ha hb hc hm)).ne')

theorem outer_points (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m) :
    (outer d hd a b c m ha hb hc hm).points = ![point d 0 0, bigB d c m, bigC d a b c m] := rfl

theorem outer_zero (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m) :
    (outer d hd a b c m ha hb hc hm).points 0 = 0 := point_zero d

theorem D_barycentric (d a b c m : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    pointD d a b m = (a / (2 * a + b)) • bigB d c m +
      (c ^ 2 / ((a + 2 * b) * (2 * a + b))) • bigC d a b c m := by
  have hP : 0 < a + 2 * b := by linarith
  have hQ : 0 < 2 * a + b := by linarith
  have hC : a ^ 2 + a * b + b ^ 2 ≠ 0 := by rw [← hrel]; exact (sq_pos_of_pos hc).ne'
  unfold pointD bigB bigC
  rw [← point_smul, ← point_smul, ← point_add]
  congr 1 <;> dsimp only [cX, cY] <;> rw [hrel] <;> field_simp <;> ring

theorem G_barycentric (d a b c m : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    pointG d a b m = (1 - c ^ 2 / (b * (2 * a + b))) • bigB d c m +
      (c ^ 2 / (b * (2 * a + b))) • bigC d a b c m := by
  have hQ : 0 < 2 * a + b := by linarith
  have hC : a ^ 2 + a * b + b ^ 2 ≠ 0 := by rw [← hrel]; exact (sq_pos_of_pos hc).ne'
  unfold pointG bigB bigC
  rw [← point_smul, ← point_smul, ← point_add]
  congr 1 <;> dsimp only [cX, cY] <;> rw [hrel] <;> field_simp <;> ring

theorem D_coords (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let T := outer d hd a b c m ha hb hc hm
    T.coord 1 (pointD d a b m) = a / (2 * a + b) ∧
      T.coord 2 (pointD d a b m) = c ^ 2 / ((a + 2 * b) * (2 * a + b)) := by
  let T := outer d hd a b c m ha hb hc hm
  rw [D_barycentric d a b c m ha hb hc hrel]
  exact T.coord_origin_combination (outer_zero d hd a b c m ha hb hc hm) _ _

theorem G_coords (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let T := outer d hd a b c m ha hb hc hm
    T.coord 1 (pointG d a b m) = 1 - c ^ 2 / (b * (2 * a + b)) ∧
      T.coord 2 (pointG d a b m) = c ^ 2 / (b * (2 * a + b)) := by
  let T := outer d hd a b c m ha hb hc hm
  rw [G_barycentric d a b c m ha hb hc hrel]
  exact T.coord_origin_combination (outer_zero d hd a b c m ha hb hc hm) _ _

theorem E_coords (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let T := outer d hd a b c m ha hb hc hm
    T.coord 1 (pointE d a b m) = (2 * a / (a + b)) * (a / (2 * a + b)) ∧
      T.coord 2 (pointE d a b m) =
        (2 * a / (a + b)) * (c ^ 2 / ((a + 2 * b) * (2 * a + b))) := by
  let T := outer d hd a b c m ha hb hc hm
  rw [pointE, D_barycentric d a b c m ha hb hc hrel, smul_add, smul_smul, smul_smul]
  exact T.coord_origin_combination (outer_zero d hd a b c m ha hb hc hm) _ _

theorem F_coords (d : ℝ) (hd : 0 < d) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m) :
    let T := outer d hd a b c m ha hb hc hm
    T.coord 1 (pointF d a b c m) = 0 ∧
      T.coord 2 (pointF d a b c m) = 2 * c ^ 2 / ((a + b) * (a + 2 * b)) := by
  let T := outer d hd a b c m ha hb hc hm
  have hh := T.coord_origin_combination (outer_zero d hd a b c m ha hb hc hm)
    0 (2 * c ^ 2 / ((a + b) * (a + 2 * b)))
  simpa [T, outer_points, pointF] using hh

end Erdos633b.DoubledCoordinates
