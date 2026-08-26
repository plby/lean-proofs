import ErdosProblems.Erdos633.VAssembly
import ErdosProblems.Erdos633.Congruence

/-!
# Euclidean geometry of the exceptional V family

`VShape` records a point on the upper unit circle with `2 re(t) = 1 + b`.
Every `0 < b < 1` gives such a point explicitly. The reference triangle is
`(0,1,b*t)` and the outer triangle is `(0,1,b*t²)`.
-/

namespace Erdos633

structure VShape where
  b : ℝ
  b_pos : 0 < b
  b_lt_one : b < 1
  t : ℂ
  normSq_t : Complex.normSq t = 1
  re_t : 2 * t.re = 1 + b
  im_t : 0 < t.im

noncomputable def VShape.ofParameter (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : VShape where
  b := b
  b_pos := hb0
  b_lt_one := hb1
  t := ⟨(1 + b) / 2, Real.sqrt (1 - ((1 + b) / 2) ^ 2)⟩
  normSq_t := by
    have h : 0 < 1 - ((1 + b) / 2) ^ 2 := by nlinarith
    have hs := Real.sq_sqrt h.le
    simp only [Complex.normSq_apply]
    nlinarith
  re_t := by dsimp; ring
  im_t := by
    apply Real.sqrt_pos.mpr
    nlinarith

theorem VShape.re_t_pos (v : VShape) : 0 < v.t.re := by
  linarith [v.re_t, v.b_pos]

theorem VShape.t_sq (v : VShape) : v.t ^ 2 = (1 + (v.b : ℂ)) * v.t - 1 := by
  have hn := v.normSq_t
  simp only [Complex.normSq_apply] at hn
  have hr := congrArg (fun r : ℝ => r * v.t.re) v.re_t
  have hi := congrArg (fun r : ℝ => r * v.t.im) v.re_t
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith
  · simp only [pow_two, Complex.mul_im, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith

noncomputable def VShape.s (v : VShape) : ℝ := Real.sqrt (1 - v.b)

theorem VShape.s_pos (v : VShape) : 0 < v.s :=
  Real.sqrt_pos.mpr (sub_pos.mpr v.b_lt_one)

theorem VShape.s_sq (v : VShape) : v.s ^ 2 = 1 - v.b :=
  Real.sq_sqrt (sub_nonneg.mpr v.b_lt_one.le)

def VShape.reference (v : VShape) : Triangle where
  a := 0
  b := 1
  c := (v.b : ℂ) * v.t
  nondegenerate := by
    change orientedDoubleArea 0 1 ((v.b : ℂ) * v.t) ≠ 0
    simpa [orientedDoubleArea] using ne_of_gt (mul_pos v.b_pos v.im_t)

def VShape.outer (v : VShape) : Triangle where
  a := 0
  b := 1
  c := (v.b : ℂ) * v.t ^ 2
  nondegenerate := by
    change orientedDoubleArea 0 1 ((v.b : ℂ) * v.t ^ 2) ≠ 0
    rw [v.t_sq]
    simpa [orientedDoubleArea, mul_assoc] using
      ne_of_gt (mul_pos v.b_pos (mul_pos (show 0 < 1 + v.b by linarith [v.b_pos]) v.im_t))

theorem VShape.coordinateEquiv_apply (v : VShape) (z : ℂ) :
    v.outer.coordinateEquiv z = (z.re : ℂ) + (z.im : ℂ) * (v.b : ℂ) * v.t ^ 2 := by
  simp [Triangle.coordinateEquiv_apply, VShape.outer, Complex.real_smul, mul_assoc]

theorem VShape.coordinateEquiv_base (v : VShape) (r : ℝ) :
    v.outer.coordinateEquiv (r : ℂ) = (r : ℂ) := by
  simp [VShape.coordinateEquiv_apply]

theorem VShape.coordinateEquiv_Q (v : VShape) :
    v.outer.coordinateEquiv (vQ v.b) = (v.b : ℂ) ^ 2 * v.t := by
  have hd : 1 + (v.b : ℂ) ≠ 0 := by
    exact_mod_cast (show 1 + v.b ≠ 0 by linarith [v.b_pos])
  rw [VShape.coordinateEquiv_apply, v.t_sq]
  dsimp [vQ]
  push_cast
  field_simp
  ring

theorem VShape.coordinateEquiv_E (v : VShape) :
    v.outer.coordinateEquiv (vE v.b) = (v.b : ℂ) ^ 2 * v.t + (1 - (v.b : ℂ)) := by
  have hd : 1 + (v.b : ℂ) ≠ 0 := by
    exact_mod_cast (show 1 + v.b ≠ 0 by linarith [v.b_pos])
  rw [VShape.coordinateEquiv_apply, v.t_sq]
  dsimp [vE]
  push_cast
  field_simp
  ring

theorem VShape.lower_eq (v : VShape) :
    (vLowerTriangle v.b v.b_pos).mapAffineEquiv v.outer.coordinateEquiv =
      v.reference.mapSimilarity 0 (v.b : ℂ) (by exact_mod_cast ne_of_gt v.b_pos) := by
  apply Triangle.ext
  · change v.outer.coordinateEquiv 0 = 0 + (v.b : ℂ) * 0
    simp [VShape.outer]
  · change v.outer.coordinateEquiv (v.b : ℂ) = 0 + (v.b : ℂ) * 1
    simp [VShape.coordinateEquiv_base]
  · change v.outer.coordinateEquiv (vQ v.b) = 0 + (v.b : ℂ) * ((v.b : ℂ) * v.t)
    rw [v.coordinateEquiv_Q]
    ring

theorem VShape.normSq_t_sub_b (v : VShape) :
    Complex.normSq (v.t - (v.b : ℂ)) = v.s ^ 2 := by
  have hn := v.normSq_t
  have hr := congrArg (fun r : ℝ => r * v.b) v.re_t
  simp only [Complex.normSq_apply] at hn
  rw [v.s_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  nlinarith

theorem VShape.normSq_bt_sub_one (v : VShape) :
    Complex.normSq ((v.b : ℂ) * v.t - 1) = v.s ^ 2 := by
  have hn := v.normSq_t
  have hr := congrArg (fun r : ℝ => r * v.b) v.re_t
  simp only [Complex.normSq_apply] at hn
  rw [v.s_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  nlinarith [congrArg (fun r : ℝ => v.b ^ 2 * r) hn]

theorem VShape.normSq_Q_sub_C (v : VShape) :
    Complex.normSq ((v.b : ℂ) ^ 2 * v.t - (v.b : ℂ) * v.t ^ 2) = v.b ^ 2 * v.s ^ 2 := by
  have h : (v.b : ℂ) ^ 2 * v.t - (v.b : ℂ) * v.t ^ 2 =
      -((v.b : ℂ) * v.t * (v.t - (v.b : ℂ))) := by ring
  rw [h, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_mul,
    v.normSq_t_sub_b, v.normSq_t, Complex.normSq_ofReal]
  ring

theorem VShape.E_sub_C (v : VShape) :
    (v.b : ℂ) ^ 2 * v.t + (1 - (v.b : ℂ)) - (v.b : ℂ) * v.t ^ 2 =
      -((v.b : ℂ) * v.t - 1) := by
  rw [v.t_sq]
  ring

/-- The left piece is congruent to the same `b`-scaled reference as the lower piece. -/
theorem VShape.left_congruent (v : VShape) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.reference.mapSimilarity 0 (v.b : ℂ)
        (by exact_mod_cast ne_of_gt v.b_pos)).carrier =
      ((vLeftTriangle v.b v.b_pos).mapAffineEquiv v.outer.coordinateEquiv).carrier := by
  let L := (vLeftTriangle v.b v.b_pos).mapAffineEquiv v.outer.coordinateEquiv
  suffices h : ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.reference.mapSimilarity 0 (v.b : ℂ)
        (by exact_mod_cast ne_of_gt v.b_pos)).carrier = L.swapBC.carrier by
    simpa only [Triangle.swapBC_carrier] using h
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (v.b : ℂ) * 1) - (0 + (v.b : ℂ) * 0)) =
      Complex.normSq (v.outer.coordinateEquiv Complex.I - v.outer.coordinateEquiv 0)
    simp only [zero_add, mul_one, mul_zero, sub_zero,
      Triangle.coordinateEquiv_I, Triangle.coordinateEquiv_zero]
    change Complex.normSq (v.b : ℂ) = Complex.normSq ((v.b : ℂ) * v.t ^ 2 - 0)
    rw [sub_zero, Complex.normSq_mul, map_pow, v.normSq_t]
    ring
  · change Complex.normSq ((0 + (v.b : ℂ) * ((v.b : ℂ) * v.t)) -
      (0 + (v.b : ℂ) * 0)) =
      Complex.normSq (v.outer.coordinateEquiv (vQ v.b) - v.outer.coordinateEquiv 0)
    simp only [zero_add, mul_zero, sub_zero, v.coordinateEquiv_Q,
      Triangle.coordinateEquiv_zero]
    change Complex.normSq ((v.b : ℂ) * ((v.b : ℂ) * v.t)) =
      Complex.normSq ((v.b : ℂ) ^ 2 * v.t - 0)
    congr 1
    ring
  · change Complex.normSq ((0 + (v.b : ℂ) * ((v.b : ℂ) * v.t)) -
      (0 + (v.b : ℂ) * 1)) =
      Complex.normSq (v.outer.coordinateEquiv (vQ v.b) - v.outer.coordinateEquiv Complex.I)
    simp only [zero_add, mul_one, v.coordinateEquiv_Q, Triangle.coordinateEquiv_I]
    change Complex.normSq ((v.b : ℂ) * ((v.b : ℂ) * v.t) - (v.b : ℂ)) =
      Complex.normSq ((v.b : ℂ) ^ 2 * v.t - (v.b : ℂ) * v.t ^ 2)
    have h : (v.b : ℂ) * ((v.b : ℂ) * v.t) - (v.b : ℂ) =
        (v.b : ℂ) * ((v.b : ℂ) * v.t - 1) := by ring
    rw [h, Complex.normSq_mul, v.normSq_bt_sub_one, v.normSq_Q_sub_C,
      Complex.normSq_ofReal]
    ring

/-- The upper piece is congruent to `sqrt(1-b)` times the reference tile. -/
theorem VShape.upper_congruent (v : VShape) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.reference.mapSimilarity 0 (v.s : ℂ)
        (by exact_mod_cast ne_of_gt v.s_pos)).carrier =
      ((vUpperTriangle v.b v.b_pos v.b_lt_one).mapAffineEquiv v.outer.coordinateEquiv).carrier := by
  let U := (vUpperTriangle v.b v.b_pos v.b_lt_one).mapAffineEquiv v.outer.coordinateEquiv
  suffices h : ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.reference.mapSimilarity 0 (v.s : ℂ)
        (by exact_mod_cast ne_of_gt v.s_pos)).carrier = U.swapBC.carrier by
    simpa only [Triangle.swapBC_carrier] using h
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (v.s : ℂ) * 1) - (0 + (v.s : ℂ) * 0)) =
      Complex.normSq (v.outer.coordinateEquiv (vE v.b) - v.outer.coordinateEquiv Complex.I)
    simp only [zero_add, mul_one, mul_zero, sub_zero, v.coordinateEquiv_E,
      Triangle.coordinateEquiv_I]
    change Complex.normSq (v.s : ℂ) =
      Complex.normSq ((v.b : ℂ) ^ 2 * v.t + (1 - (v.b : ℂ)) - (v.b : ℂ) * v.t ^ 2)
    rw [v.E_sub_C, Complex.normSq_neg, v.normSq_bt_sub_one, Complex.normSq_ofReal]
    ring
  · change Complex.normSq ((0 + (v.s : ℂ) * ((v.b : ℂ) * v.t)) -
      (0 + (v.s : ℂ) * 0)) =
      Complex.normSq (v.outer.coordinateEquiv (vQ v.b) - v.outer.coordinateEquiv Complex.I)
    simp only [zero_add, mul_zero, sub_zero, v.coordinateEquiv_Q,
      Triangle.coordinateEquiv_I]
    change Complex.normSq ((v.s : ℂ) * ((v.b : ℂ) * v.t)) =
      Complex.normSq ((v.b : ℂ) ^ 2 * v.t - (v.b : ℂ) * v.t ^ 2)
    rw [v.normSq_Q_sub_C, Complex.normSq_mul, Complex.normSq_mul, v.normSq_t,
      Complex.normSq_ofReal, Complex.normSq_ofReal]
    ring
  · change Complex.normSq ((0 + (v.s : ℂ) * ((v.b : ℂ) * v.t)) -
      (0 + (v.s : ℂ) * 1)) =
      Complex.normSq (v.outer.coordinateEquiv (vQ v.b) - v.outer.coordinateEquiv (vE v.b))
    simp only [zero_add, mul_one, v.coordinateEquiv_Q, v.coordinateEquiv_E]
    have h₁ : (v.s : ℂ) * ((v.b : ℂ) * v.t) - (v.s : ℂ) =
        (v.s : ℂ) * ((v.b : ℂ) * v.t - 1) := by ring
    have h₂ : (v.b : ℂ) ^ 2 * v.t - ((v.b : ℂ) ^ 2 * v.t + (1 - (v.b : ℂ))) =
        -((1 - v.b : ℝ) : ℂ) := by push_cast; ring
    rw [h₁, h₂, Complex.normSq_mul, v.normSq_bt_sub_one, Complex.normSq_neg,
      Complex.normSq_ofReal, Complex.normSq_ofReal, ← v.s_sq]
    ring

theorem VShape.coordinateEquiv_grid_vertex (v : VShape) (ε : ℝ) :
    v.outer.coordinateEquiv (⟨1 - ε / (1 + v.b), ε / (1 + v.b)⟩ : ℂ) =
      1 - (ε : ℂ) + (ε : ℂ) * (v.b : ℂ) * v.t := by
  have hd : 1 + (v.b : ℂ) ≠ 0 := by
    exact_mod_cast (show 1 + v.b ≠ 0 by linarith [v.b_pos])
  rw [VShape.coordinateEquiv_apply, v.t_sq]
  dsimp
  push_cast
  field_simp
  ring

/-- The affine grid reference is a translated, relabelled copy of `ε R`. -/
theorem VShape.grid_congruent (v : VShape) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.reference.mapSimilarity 0 (ε : ℂ)
        (by exact_mod_cast ne_of_gt hε)).carrier =
      ((vGridTriangle v.b ε v.b_pos hε).mapAffineEquiv v.outer.coordinateEquiv).carrier := by
  let R := v.reference.mapSimilarity 0 (ε : ℂ) (by exact_mod_cast ne_of_gt hε)
  let G := (vGridTriangle v.b ε v.b_pos hε).mapAffineEquiv v.outer.coordinateEquiv
  let e := IsometryEquiv.vaddConst (1 - (ε : ℂ))
  have h : R.mapIsometry e = G.swapAB := by
    apply Triangle.ext
    · change (0 + (ε : ℂ) * 0) + (1 - (ε : ℂ)) =
        v.outer.coordinateEquiv ((1 - ε : ℝ) : ℂ)
      rw [v.coordinateEquiv_base]
      push_cast
      ring
    · change (0 + (ε : ℂ) * 1) + (1 - (ε : ℂ)) = v.outer.coordinateEquiv 1
      rw [Triangle.coordinateEquiv_one]
      change (0 + (ε : ℂ) * 1) + (1 - (ε : ℂ)) = 1
      ring
    · change (0 + (ε : ℂ) * ((v.b : ℂ) * v.t)) + (1 - (ε : ℂ)) =
        v.outer.coordinateEquiv (⟨1 - ε / (1 + v.b), ε / (1 + v.b)⟩ : ℂ)
      rw [v.coordinateEquiv_grid_vertex]
      ring
  refine ⟨e, ?_⟩
  change e '' R.carrier = G.carrier
  rw [← Triangle.mapIsometry_carrier, h, Triangle.swapAB_carrier]

/-- The outer family has side lengths `1`, `b`, and `s*(1+b)`.
Squared norms avoid introducing any angle or square-root side conventions. -/
theorem VShape.outer_side_squares (v : VShape) :
    Complex.normSq (v.outer.b - v.outer.a) = 1 ∧
    Complex.normSq (v.outer.c - v.outer.a) = v.b ^ 2 ∧
    Complex.normSq (v.outer.c - v.outer.b) = (v.s * (1 + v.b)) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [VShape.outer]
  · change Complex.normSq ((v.b : ℂ) * v.t ^ 2 - 0) = v.b ^ 2
    rw [sub_zero, Complex.normSq_mul, map_pow, v.normSq_t, Complex.normSq_ofReal]
    ring
  · change Complex.normSq ((v.b : ℂ) * v.t ^ 2 - 1) = (v.s * (1 + v.b)) ^ 2
    have h : (v.b : ℂ) * v.t ^ 2 - 1 =
        ((1 + v.b : ℝ) : ℂ) * ((v.b : ℂ) * v.t - 1) := by
      rw [v.t_sq]
      push_cast
      ring
    rw [h, Complex.normSq_mul, v.normSq_bt_sub_one, Complex.normSq_ofReal]
    ring

end Erdos633
