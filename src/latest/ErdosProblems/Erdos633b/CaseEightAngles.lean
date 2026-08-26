import ErdosProblems.Erdos633b.CaseEightConstruction

/-! Exact angle identification for the case-(8) coordinate construction. -/

namespace Erdos633b.Sixty

theorem point_inner (d : ℝ) (he : d ^ 2 = 3) (s t u v : ℝ) :
    inner ℝ (point d s t) (point d u v) = s * u + (s * v + t * u) / 2 + t * v := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, point]
  linear_combination (t * v / 4) * he

theorem bisected_angle_zero (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c k y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k) (hy : 0 < y)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (bisectedTriangle d hd (k * a) y (k * b) (mul_pos hk ha) hy (mul_pos hk hb)).angle 0 =
      (groupTwoReference d hd a b ha hb).angle 1 := by
  let T := bisectedTriangle d hd (k * a) y (k * b) (mul_pos hk ha) hy (mul_pos hk hb)
  let R := groupTwoReference d hd a b ha hb
  have hf : ‖point d 0 1‖ = 1 := by nlinarith [point_norm_sq d he 0 1, norm_nonneg (point d 0 1)]
  have hv : ‖point d a b‖ = c := by nlinarith [point_norm_sq d he a b, norm_nonneg (point d a b)]
  have hY : point d 0 y - point d 0 (-(k * b)) = (y + k * b) • point d 0 1 := by
    rw [point_sub, ← point_smul]
    congr 1 <;> ring
  have hX : point d (k * a) 0 - point d 0 (-(k * b)) = k • point d a b := by
    rw [point_sub, ← point_smul]
    congr 1 <;> ring
  have hcos : Real.cos (T.angle 0) = (a + 2 * b) / (2 * c) := by
    change Real.cos (InnerProductGeometry.angle (point d 0 y - point d 0 (-(k * b)))
      (point d (k * a) 0 - point d 0 (-(k * b)))) = _
    rw [hY, hX, InnerProductGeometry.angle_smul_left_of_pos _ _ (add_pos hy (mul_pos hk hb)),
      InnerProductGeometry.angle_smul_right_of_pos _ _ hk, InnerProductGeometry.cos_angle,
      hf, hv, point_inner d he]
    field_simp
    ring
  exact Real.injOn_cos ⟨(T.angle_pos 0).le, (T.angle_lt_pi 0).le⟩
    ⟨(R.angle_pos 1).le, (R.angle_lt_pi 1).le⟩
    (hcos.trans (reference_cos_one d hd he a b c ha hb hc hrel).symm)

theorem bisected_angle_one (d : ℝ) (hd : 0 < d) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (bisectedTriangle d hd x y z hx hy hz).angle 1 =
      (cornerTriangle d hd x y hx hy).angle 2 := by
  change InnerProductGeometry.angle (point d x 0 - point d 0 y)
    (point d 0 (-z) - point d 0 y) =
    InnerProductGeometry.angle (point d 0 0 - point d 0 y) (point d x 0 - point d 0 y)
  have hQ : point d 0 (-z) - point d 0 y = (y + z) • point d 0 (-1) := by
    rw [point_sub, ← point_smul]
    congr 1 <;> ring
  have hO : point d 0 0 - point d 0 y = y • point d 0 (-1) := by
    rw [point_sub, ← point_smul]
    congr 1 <;> ring
  rw [hQ, hO, InnerProductGeometry.angle_smul_right_of_pos _ _ (add_pos hy hz),
    InnerProductGeometry.angle_smul_left_of_pos _ _ hy, InnerProductGeometry.angle_comm]

theorem reference_angle_swap (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (groupTwoReference d hd b a hb ha).angle 1 = (groupTwoReference d hd a b ha hb).angle 2 := by
  let R := groupTwoReference d hd a b ha hb
  let R0 := groupTwoReference d hd b a hb ha
  let V : Triangle := R0.reindex (Equiv.swap 1 2)
  have hrel' : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by nlinarith
  have hs (i : Fin 3) : R.side i = V.side i := by
    rw [Triangle.side_reindex, reference_sides d hd he a b c ha hb hc hrel,
      reference_sides d hd he b a c hb ha hc hrel']
    fin_cases i <;> rfl
  have hdist := R.distances_of_sides V hs
  have hh := congrArg (fun U : Triangle => U.angle 2) (R.move_vertexIsometry V hdist)
  rw [Triangle.angle_move, Triangle.angle_reindex] at hh
  exact hh.symm

theorem caseEightOuter_angles (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let R := groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb)
    (caseEightOuter d hd a b ha hb).angle 0 = R.angle 1 ∧
      (caseEightOuter d hd a b ha hb).angle 1 = R.angle 1 + Real.pi / 3 := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hrelr : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + a * b + (b : ℝ) ^ 2 := by exact_mod_cast hrel
  let k := commonScale a b * (a + b)
  have hkr : (0 : ℝ) < k := by exact_mod_cast mul_pos (commonScale_pos a b) (add_pos ha hb)
  let x : ℝ := k * (a : ℝ)
  let y : ℝ := (commonScale a b * a * b : ℕ)
  let z : ℝ := k * (b : ℝ)
  have hx : 0 < x := mul_pos hkr har
  have hy : 0 < y := by
    dsimp only [y]
    exact_mod_cast mul_pos (mul_pos (commonScale_pos a b) ha) hb
  have hz : 0 < z := mul_pos hkr hbr
  let T := bisectedTriangle d hd x y z hx hy hz
  let R := groupTwoReference d hd a b har hbr
  let C := cornerTriangle d hd x y hx hy
  let U := caseFourOuter d hd b a hb ha
  have hCU : C = U := by
    dsimp only [C, U, caseFourOuter]
    congr 1 <;> dsimp only [x, y, k] <;> push_cast
    all_goals simp only [commonScale_comm b a]
    all_goals ring
  constructor
  · exact bisected_angle_zero d hd he a b c k y har hbr hcr hkr hy hrelr
  · have hT1 : T.angle 1 = U.angle 2 :=
      (bisected_angle_one d hd x y z hx hy hz).trans (congrArg (fun S : Triangle => S.angle 2) hCU)
    have hU0 : U.angle 0 = Real.pi / 3 := corner_angle_zero d hd he _ _ _ _
    have hU1 : U.angle 1 = R.angle 2 :=
      (corner_angle_one d hd b a (commonScale b a * a : ℕ) hbr har
        (by exact_mod_cast mul_pos (commonScale_pos b a) ha)).trans
        (reference_angle_swap d hd he a b c har hbr hcr hrelr)
    have hR0 : R.angle 0 = 2 * Real.pi / 3 := reference_angle_zero d hd he a b c har hbr hcr hrelr
    change T.angle 1 = R.angle 1 + Real.pi / 3
    linarith [U.angle_sum, R.angle_sum]

end Erdos633b.Sixty
