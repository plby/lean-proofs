import ErdosProblems.Erdos633b.GroupTwoNormalization

/-! A genuine triangle crossing the second oblique axis, split exactly at the origin. -/

namespace Erdos633b.Sixty

noncomputable def bisectedTriangle (d : ℝ) (hd : 0 < d) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : Triangle :=
  triangle d hd 0 (-z) 0 y x 0 (by
    simp only [sub_zero, zero_mul, zero_sub, sub_neg_eq_add]
    exact neg_ne_zero.mpr (mul_pos hx (add_pos hy hz)).ne')

theorem bisectedTriangle_points (d : ℝ) (hd : 0 < d) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (bisectedTriangle d hd x y z hx hy hz).points =
      ![point d 0 (-z), point d 0 y, point d x 0] := rfl

theorem bisected_weight_bounds (y z : ℝ) (hy : 0 < y) (hz : 0 < z) :
    0 < z / (y + z) ∧ z / (y + z) < 1 :=
  ⟨div_pos hz (add_pos hy hz), (div_lt_one (add_pos hy hz)).mpr (by linarith)⟩

theorem bisected_edgePoint (d : ℝ) (hd : 0 < d) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (bisectedTriangle d hd x y z hx hy hz).edgePoint (z / (y + z)) = point d 0 0 := by
  rw [Triangle.edgePoint_eq]
  change (1 - z / (y + z)) • point d 0 (-z) + (z / (y + z)) • point d 0 y = _
  rw [← point_smul, ← point_smul, ← point_add]
  congr 1
  · ring
  · field_simp
    ring

theorem bisected_first_swap_points (d : ℝ) (hd : 0 < d) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (((bisectedTriangle d hd x y z hx hy hz).edgeFirst (z / (y + z))
      (bisected_weight_bounds y z hy hz).1).reindex (Equiv.swap 0 2)).points =
      ![point d 0 0, point d 0 (-z), point d x 0] := by
  funext i
  change ((bisectedTriangle d hd x y z hx hy hz).edgeFirst (z / (y + z))
    (bisected_weight_bounds y z hy hz).1).points ((Equiv.swap 0 2).symm i) = _
  rw [Triangle.edgeFirst_points, bisected_edgePoint]
  fin_cases i <;> simp
  all_goals rfl

theorem bisected_second_points (d : ℝ) (hd : 0 < d) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((bisectedTriangle d hd x y z hx hy hz).edgeSecond (z / (y + z))
      (bisected_weight_bounds y z hy hz).2).points =
      ![point d x 0, point d 0 y, point d 0 0] := by
  rw [Triangle.edgeSecond_points, bisected_edgePoint]
  rfl

theorem bisected_second_support (d : ℝ) (hd : 0 < d) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((bisectedTriangle d hd x y z hx hy hz).edgeSecond (z / (y + z))
      (bisected_weight_bounds y z hy hz).2).support =
      (cornerTriangle d hd x y hx hy).support := by
  let e : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  have ht : (bisectedTriangle d hd x y z hx hy hz).edgeSecond (z / (y + z))
      (bisected_weight_bounds y z hy hz).2 = (cornerTriangle d hd x y hx hy).reindex e := by
    apply Affine.Simplex.ext
    intro i
    rw [bisected_second_points]
    change ![point d x 0, point d 0 y, point d 0 0] i =
      (cornerTriangle d hd x y hx hy).points (e.symm i)
    rw [cornerTriangle_points]
    fin_cases i <;> rfl
  rw [ht, Triangle.support_reindex]

theorem bisected_first_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c k y : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hy : 0 < y)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 3) :
    Triangle.side (((bisectedTriangle d hd (k * a) y (k * b) (mul_pos hk ha) hy
      (mul_pos hk hb)).edgeFirst (k * b / (y + k * b))
        (bisected_weight_bounds y (k * b) hy (mul_pos hk hb)).1).reindex (Equiv.swap 0 2)) i =
      k * (groupTwoReference d hd a b ha hb).side i := by
  let x := k * a
  let z := k * b
  let S : Triangle := ((bisectedTriangle d hd x y z (mul_pos hk ha) hy (mul_pos hk hb)).edgeFirst
    (z / (y + z)) (bisected_weight_bounds y z hy (mul_pos hk hb)).1).reindex
      (Equiv.swap 0 2)
  let R := groupTwoReference d hd a b ha hb
  have hsq : S.side i ^ 2 = (k * R.side i) ^ 2 := by
    rw [mul_pow, side_sq_of_points d he S 0 0 0 (-z) x 0
      (bisected_first_swap_points d hd x y z (mul_pos hk ha) hy (mul_pos hk hb)),
      groupTwoReference_side_sq d hd he a b c ha hb hrel]
    fin_cases i
    · change (0 - x) ^ 2 + (0 - x) * (-z - 0) + (-z - 0) ^ 2 = k ^ 2 * c ^ 2
      dsimp only [x, z]
      linear_combination -(k ^ 2) * hrel
    · change (x - 0) ^ 2 + (x - 0) * (0 - 0) + (0 - 0) ^ 2 = k ^ 2 * a ^ 2
      dsimp only [x]
      ring
    · change (0 - 0) ^ 2 + (0 - 0) * (0 - -z) + (0 - -z) ^ 2 = k ^ 2 * b ^ 2
      dsimp only [z]
      ring
  nlinarith [S.side_pos i, mul_pos hk (R.side_pos i)]

end Erdos633b.Sixty
