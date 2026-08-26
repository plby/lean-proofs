import ErdosProblems.Erdos633b.CaseFourConstruction
import ErdosProblems.Erdos633b.TriangleCosine

/-! Metric and angle certificates for the sixty-degree corner constructions. -/

namespace Erdos633b.Sixty

theorem point_sub (d s t u v : ℝ) : point d s t - point d u v = point d (s - u) (t - v) := by
  ext i
  fin_cases i <;> simp [point] <;> ring

theorem corner_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (i : Fin 3) :
    (cornerTriangle d hd x y hx hy).side i ^ 2 = ![x ^ 2 - x * y + y ^ 2, y ^ 2, x ^ 2] i := by
  rw [side_sq_of_points d he _ 0 0 x 0 0 y (cornerTriangle_points d hd x y hx hy)]
  fin_cases i
  · change (x - 0) ^ 2 + (x - 0) * (0 - y) + (0 - y) ^ 2 = x ^ 2 - x * y + y ^ 2
    ring
  · change (0 - 0) ^ 2 + (0 - 0) * (y - 0) + (y - 0) ^ 2 = y ^ 2
    ring
  · change (0 - x) ^ 2 + (0 - x) * (0 - 0) + (0 - 0) ^ 2 = x ^ 2
    ring

theorem corner_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 3) :
    (cornerTriangle d hd (k * (a + b)) (k * a) (mul_pos hk (add_pos ha hb))
      (mul_pos hk ha)).side i = k * ![c, a, a + b] i := by
  let T := cornerTriangle d hd (k * (a + b)) (k * a) (mul_pos hk (add_pos ha hb)) (mul_pos hk ha)
  have hsq : T.side i ^ 2 = (k * ![c, a, a + b] i) ^ 2 := by
    rw [corner_side_sq d hd he]
    fin_cases i
    · change (k * (a + b)) ^ 2 - k * (a + b) * (k * a) + (k * a) ^ 2 = (k * c) ^ 2
      linear_combination -(k ^ 2) * hrel
    · change (k * a) ^ 2 = (k * a) ^ 2
      rfl
    · change (k * (a + b)) ^ 2 = (k * (a + b)) ^ 2
      rfl
  have hpos : 0 < k * ![c, a, a + b] i := by
    apply mul_pos hk
    fin_cases i
    · exact hc
    · exact ha
    · exact add_pos ha hb
  nlinarith [T.side_pos i]

theorem corner_angle_zero (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (cornerTriangle d hd x y hx hy).angle 0 = Real.pi / 3 := by
  let T := cornerTriangle d hd x y hx hy
  have h1 : T.side 1 = y := by
    have h := corner_side_sq d hd he x y hx hy 1
    change T.side 1 ^ 2 = y ^ 2 at h
    nlinarith [T.side_pos 1]
  have h2 : T.side 2 = x := by
    have h := corner_side_sq d hd he x y hx hy 2
    change T.side 2 ^ 2 = x ^ 2 at h
    nlinarith [T.side_pos 2]
  have h0 := corner_side_sq d hd he x y hx hy 0
  change T.side 0 ^ 2 = x ^ 2 - x * y + y ^ 2 at h0
  have hlaw := T.cosine_law 0
  change T.side 0 ^ 2 = T.side 1 ^ 2 + T.side 2 ^ 2 -
    2 * T.side 1 * T.side 2 * Real.cos (T.angle 0) at hlaw
  rw [h1, h2, h0] at hlaw
  have hcos : Real.cos (T.angle 0) = 1 / 2 := by nlinarith [mul_pos hx hy]
  exact Real.injOn_cos ⟨(T.angle_pos 0).le, (T.angle_lt_pi 0).le⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ (hcos.trans Real.cos_pi_div_three.symm)

theorem corner_angle_one (d : ℝ) (hd : 0 < d) (a b k : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    (cornerTriangle d hd (k * (a + b)) (k * a) (mul_pos hk (add_pos ha hb))
      (mul_pos hk ha)).angle 1 = (groupTwoReference d hd a b ha hb).angle 1 := by
  change InnerProductGeometry.angle (point d 0 (k * a) - point d (k * (a + b)) 0)
    (point d 0 0 - point d (k * (a + b)) 0) =
    InnerProductGeometry.angle (point d (-a) a - point d b 0) (point d 0 0 - point d b 0)
  have hv : point d 0 (k * a) - point d (k * (a + b)) 0 = k • point d (-a - b) a := by
    rw [point_sub, ← point_smul]
    congr 1 <;> ring
  have hu : point d 0 0 - point d (k * (a + b)) 0 = (k * (a + b)) • point d (-1) 0 := by
    rw [point_sub, ← point_smul]
    congr 1 <;> ring
  have hr : point d 0 0 - point d b 0 = b • point d (-1) 0 := by
    rw [point_sub, ← point_smul]
    congr 1 <;> ring
  rw [hv, hu, hr, point_sub]
  simp only [sub_zero]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hk,
    InnerProductGeometry.angle_smul_right_of_pos _ _ (mul_pos hk (add_pos ha hb)),
    InnerProductGeometry.angle_smul_right_of_pos _ _ hb]

theorem caseFourOuter_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 3) :
    (caseFourOuter d hd a b ha hb).side i =
      (commonScale a b * b : ℕ) * ![(c : ℝ), a, (a : ℝ) + b] i := by
  exact corner_sides d hd he a b c (commonScale a b * b : ℕ)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
    (by exact_mod_cast mul_pos (commonScale_pos a b) hb) (by exact_mod_cast hrel) i

end Erdos633b.Sixty
