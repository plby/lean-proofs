import ErdosProblems.Erdos633b.TrapezoidTriangles

/-! The three basic-trapezoid triangles have the required scaled tile side lengths. -/

namespace Erdos633b.Sixty

noncomputable def groupTwoReference (d : ℝ) (hd : 0 < d) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Triangle := triangle d hd 0 0 b 0 (-a) a (by
      simp only [sub_zero, mul_zero, sub_zero]
      exact (mul_pos hb ha).ne')

theorem groupTwoReference_points (d : ℝ) (hd : 0 < d) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (groupTwoReference d hd a b ha hb).points = ![point d 0 0, point d b 0, point d (-a) a] := rfl

theorem groupTwoReference_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (i : Fin 3) :
    (groupTwoReference d hd a b ha hb).side i ^ 2 = ![c ^ 2, a ^ 2, b ^ 2] i := by
  rw [side_sq_of_points d he _ 0 0 b 0 (-a) a (groupTwoReference_points d hd a b ha hb)]
  fin_cases i
  · change (b - -a) ^ 2 + (b - -a) * (0 - a) + (0 - a) ^ 2 = c ^ 2
    nlinarith
  · change (-a - 0) ^ 2 + (-a - 0) * (a - 0) + (a - 0) ^ 2 = a ^ 2
    ring
  · change (0 - b) ^ 2 + (0 - b) * (0 - 0) + (0 - 0) ^ 2 = b ^ 2
    ring

theorem basic_left_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (i : Fin 3) :
    (leftTriangle d hd (a ^ 2) (a * b) (sq_pos_of_pos ha) (mul_pos ha hb)).side i ^ 2 =
      ![a ^ 2 * c ^ 2, a ^ 4, a ^ 2 * b ^ 2] i := by
  rw [side_sq_of_points d he _ 0 (a * b) 0 0 (a ^ 2) (a * b)
    (leftTriangle_points d hd (a ^ 2) (a * b) (sq_pos_of_pos ha) (mul_pos ha hb))]
  fin_cases i
  · change (0 - a ^ 2) ^ 2 + (0 - a ^ 2) * (0 - a * b) + (0 - a * b) ^ 2 = a ^ 2 * c ^ 2
    linear_combination -(a ^ 2) * hc
  · change (a ^ 2 - 0) ^ 2 + (a ^ 2 - 0) * (a * b - a * b) +
      (a * b - a * b) ^ 2 = a ^ 4
    ring
  · change (0 - 0) ^ 2 + (0 - 0) * (a * b - 0) + (a * b - 0) ^ 2 = a ^ 2 * b ^ 2
    ring

theorem basic_right_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (i : Fin 3) :
    (rightTriangle d hd (a ^ 2) (b ^ 2) (a * b) (sq_pos_of_pos hb) (mul_pos ha hb)).side i ^ 2 =
      ![b ^ 2 * c ^ 2, a ^ 2 * b ^ 2, b ^ 4] i := by
  rw [side_sq_of_points d he _ (a ^ 2 + b ^ 2) (a * b) (a ^ 2) (a * b)
    (a ^ 2 + b ^ 2 + a * b) 0
    (rightTriangle_points d hd (a ^ 2) (b ^ 2) (a * b) (sq_pos_of_pos hb) (mul_pos ha hb))]
  fin_cases i
  · change (a ^ 2 - (a ^ 2 + b ^ 2 + a * b)) ^ 2 +
      (a ^ 2 - (a ^ 2 + b ^ 2 + a * b)) * (a * b - 0) +
      (a * b - 0) ^ 2 = b ^ 2 * c ^ 2
    linear_combination -(b ^ 2) * hc
  · change (a ^ 2 + b ^ 2 + a * b - (a ^ 2 + b ^ 2)) ^ 2 +
      (a ^ 2 + b ^ 2 + a * b - (a ^ 2 + b ^ 2)) * (0 - a * b) +
      (0 - a * b) ^ 2 = a ^ 2 * b ^ 2
    ring
  · change (a ^ 2 + b ^ 2 - a ^ 2) ^ 2 +
      (a ^ 2 + b ^ 2 - a ^ 2) * (a * b - a * b) + (a * b - a * b) ^ 2 = b ^ 4
    ring

theorem basic_middle_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (i : Fin 3) :
    (middleTriangle d hd (a ^ 2) (b ^ 2) (a * b) (sq_pos_of_pos ha) (sq_pos_of_pos hb)
      (mul_pos ha hb)).side i ^ 2 = ![c ^ 4, a ^ 2 * c ^ 2, b ^ 2 * c ^ 2] i := by
  rw [side_sq_of_points d he _ (a ^ 2) (a * b) (a ^ 2 + b ^ 2 + a * b) 0 0 0
    (middleTriangle_points d hd (a ^ 2) (b ^ 2) (a * b) (sq_pos_of_pos ha)
      (sq_pos_of_pos hb) (mul_pos ha hb))]
  fin_cases i
  · change (a ^ 2 + b ^ 2 + a * b - 0) ^ 2 +
      (a ^ 2 + b ^ 2 + a * b - 0) * (0 - 0) + (0 - 0) ^ 2 = c ^ 4
    have heq : a ^ 2 + b ^ 2 + a * b = c ^ 2 := by linarith
    rw [heq]
    ring
  · change (0 - a ^ 2) ^ 2 + (0 - a ^ 2) * (0 - a * b) + (0 - a * b) ^ 2 = a ^ 2 * c ^ 2
    linear_combination -(a ^ 2) * hc
  · change (a ^ 2 - (a ^ 2 + b ^ 2 + a * b)) ^ 2 +
      (a ^ 2 - (a ^ 2 + b ^ 2 + a * b)) * (a * b - 0) +
      (a * b - 0) ^ 2 = b ^ 2 * c ^ 2
    linear_combination -(b ^ 2) * hc

theorem basic_left_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (i : Fin 3) :
    (leftTriangle d hd (a ^ 2) (a * b) (sq_pos_of_pos ha) (mul_pos ha hb)).side i =
      a * (groupTwoReference d hd a b ha hb).side i := by
  let S := leftTriangle d hd (a ^ 2) (a * b) (sq_pos_of_pos ha) (mul_pos ha hb)
  let R := groupTwoReference d hd a b ha hb
  have hsq : S.side i ^ 2 = (a * R.side i) ^ 2 := by
    rw [mul_pow, basic_left_side_sq d hd he a b c ha hb hc,
      groupTwoReference_side_sq d hd he a b c ha hb hc]
    fin_cases i
    · change a ^ 2 * c ^ 2 = a ^ 2 * c ^ 2
      rfl
    · change a ^ 4 = a ^ 2 * a ^ 2
      ring
    · change a ^ 2 * b ^ 2 = a ^ 2 * b ^ 2
      rfl
  nlinarith [S.side_pos i, mul_pos ha (R.side_pos i)]

theorem basic_right_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (i : Fin 3) :
    (rightTriangle d hd (a ^ 2) (b ^ 2) (a * b) (sq_pos_of_pos hb) (mul_pos ha hb)).side i =
      b * (groupTwoReference d hd a b ha hb).side i := by
  let S := rightTriangle d hd (a ^ 2) (b ^ 2) (a * b) (sq_pos_of_pos hb) (mul_pos ha hb)
  let R := groupTwoReference d hd a b ha hb
  have hsq : S.side i ^ 2 = (b * R.side i) ^ 2 := by
    rw [mul_pow, basic_right_side_sq d hd he a b c ha hb hc,
      groupTwoReference_side_sq d hd he a b c ha hb hc]
    fin_cases i
    · change b ^ 2 * c ^ 2 = b ^ 2 * c ^ 2
      rfl
    · change a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2
      ring
    · change b ^ 4 = b ^ 2 * b ^ 2
      ring
  nlinarith [S.side_pos i, mul_pos hb (R.side_pos i)]

theorem basic_middle_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 3) :
    (middleTriangle d hd (a ^ 2) (b ^ 2) (a * b) (sq_pos_of_pos ha) (sq_pos_of_pos hb)
      (mul_pos ha hb)).side i = c * (groupTwoReference d hd a b ha hb).side i := by
  let S := middleTriangle d hd (a ^ 2) (b ^ 2) (a * b) (sq_pos_of_pos ha) (sq_pos_of_pos hb)
    (mul_pos ha hb)
  let R := groupTwoReference d hd a b ha hb
  have hsq : S.side i ^ 2 = (c * R.side i) ^ 2 := by
    rw [mul_pow, basic_middle_side_sq d hd he a b c ha hb hrel,
      groupTwoReference_side_sq d hd he a b c ha hb hrel]
    fin_cases i
    · change c ^ 4 = c ^ 2 * c ^ 2
      ring
    · change a ^ 2 * c ^ 2 = c ^ 2 * a ^ 2
      ring
    · change b ^ 2 * c ^ 2 = c ^ 2 * b ^ 2
      ring
  nlinarith [S.side_pos i, mul_pos hc (R.side_pos i)]

end Erdos633b.Sixty
