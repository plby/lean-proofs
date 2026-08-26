import ErdosProblems.Erdos633b.GroupTwoEquilateral
import ErdosProblems.Erdos633b.TriangularPatch

/-! An exact equilateral-plus-tile partition of a triangle with a sixty-degree corner. -/

namespace Erdos633b.Sixty

noncomputable def cornerTriangle (d : ℝ) (hd : 0 < d) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) : Triangle :=
  triangle d hd 0 0 x 0 0 y (by
    simp only [sub_zero, mul_zero, sub_zero]
    exact (mul_pos hx hy).ne')

theorem cornerTriangle_points (d : ℝ) (hd : 0 < d) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    (cornerTriangle d hd x y hx hy).points = ![point d 0 0, point d x 0, point d 0 y] := rfl

theorem corner_edgePoint (d : ℝ) (hd : 0 < d) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    (cornerTriangle d hd x y hx hy).edgePoint (y / x) = point d y 0 := by
  rw [Triangle.edgePoint_eq]
  change (1 - y / x) • point d 0 0 + (y / x) • point d x 0 = _
  rw [point_zero, smul_zero, zero_add, ← point_smul]
  congr 1
  · exact div_mul_cancel₀ y hx.ne'
  · ring

theorem corner_edgeFirst_points (d : ℝ) (hd : 0 < d) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    ((cornerTriangle d hd x y hx hy).edgeFirst (y / x) (div_pos hy hx)).points =
      ![point d 0 y, point d 0 0, point d y 0] := by
  rw [Triangle.edgeFirst_points, corner_edgePoint]
  rfl

theorem corner_edgeSecond_swap_points (d : ℝ) (hd : 0 < d) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hyx : y < x) :
    (((cornerTriangle d hd x y hx hy).edgeSecond (y / x)
      ((div_lt_one hx).mpr hyx)).reindex (Equiv.swap 0 2)).points =
      ![point d y 0, point d x 0, point d 0 y] := by
  funext i
  change ((cornerTriangle d hd x y hx hy).edgeSecond (y / x) ((div_lt_one hx).mpr hyx)).points
    ((Equiv.swap 0 2).symm i) = _
  rw [Triangle.edgeSecond_points, corner_edgePoint]
  fin_cases i <;> simp
  all_goals rfl

theorem corner_equilateral_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (i : Fin 3) :
    ((cornerTriangle d hd x y hx hy).edgeFirst (y / x) (div_pos hy hx)).side i = y := by
  let E := (cornerTriangle d hd x y hx hy).edgeFirst (y / x) (div_pos hy hx)
  have hsq : E.side i ^ 2 = y ^ 2 := by
    rw [side_sq_of_points d he E 0 y 0 0 y 0
      (corner_edgeFirst_points d hd x y hx hy)]
    fin_cases i
    · change (0 - y) ^ 2 + (0 - y) * (0 - 0) + (0 - 0) ^ 2 = y ^ 2
      ring
    · change (y - 0) ^ 2 + (y - 0) * (0 - y) + (0 - y) ^ 2 = y ^ 2
      ring
    · change (0 - 0) ^ 2 + (0 - 0) * (y - 0) + (y - 0) ^ 2 = y ^ 2
      ring
  nlinarith [E.side_pos i]

theorem corner_remainder_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 3) :
    Triangle.side (((cornerTriangle d hd (k * (a + b)) (k * a) (mul_pos hk (add_pos ha hb))
      (mul_pos hk ha)).edgeSecond (k * a / (k * (a + b)))
      ((div_lt_one (mul_pos hk (add_pos ha hb))).mpr (by nlinarith [mul_pos hk hb]))).reindex
      (Equiv.swap 0 2)) i =
      k * (groupTwoReference d hd a b ha hb).side i := by
  let x := k * (a + b)
  let y := k * a
  have hx : 0 < x := mul_pos hk (add_pos ha hb)
  have hy : 0 < y := mul_pos hk ha
  have hyx : y < x := by dsimp only [x, y]; nlinarith [mul_pos hk hb]
  let S : Triangle := ((cornerTriangle d hd x y hx hy).edgeSecond (y / x)
    ((div_lt_one hx).mpr hyx)).reindex (Equiv.swap 0 2)
  let R := groupTwoReference d hd a b ha hb
  have hsq : S.side i ^ 2 = (k * R.side i) ^ 2 := by
    rw [mul_pow, side_sq_of_points d he S y 0 x 0 0 y
      (corner_edgeSecond_swap_points d hd x y hx hy hyx),
      groupTwoReference_side_sq d hd he a b c ha hb hrel]
    fin_cases i
    · change (x - 0) ^ 2 + (x - 0) * (0 - y) + (0 - y) ^ 2 = k ^ 2 * c ^ 2
      dsimp only [x, y]
      linear_combination -(k ^ 2) * hrel
    · change (0 - y) ^ 2 + (0 - y) * (y - 0) + (y - 0) ^ 2 = k ^ 2 * a ^ 2
      dsimp only [y]
      ring
    · change (y - x) ^ 2 + (y - x) * (0 - 0) + (0 - 0) ^ 2 = k ^ 2 * b ^ 2
      dsimp only [x, y]
      ring
  nlinarith [S.side_pos i, mul_pos hk (R.side_pos i)]

end Erdos633b.Sixty
