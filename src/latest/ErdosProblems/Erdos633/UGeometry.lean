import ErdosProblems.Erdos633.VGeometry
import ErdosProblems.Erdos633.Split

/-!
# Attaching a scaled reference triangle to V

With `C = b*t²`, the companion outer triangle has vertices `0,1,(2+b)*C`.
The segment from `1` to `C` splits it into the V triangle and a triangle
congruent to `(1+b)` times the same reference tile.
-/

namespace Erdos633

def VShape.uOuter (v : VShape) : Triangle where
  a := 0
  b := 1
  c := ((2 + v.b : ℝ) : ℂ) * v.outer.c
  nondegenerate := by
    have h : orientedDoubleArea 0 1 (((2 + v.b : ℝ) : ℂ) * v.outer.c) =
        (2 + v.b) * orientedDoubleArea 0 1 v.outer.c := by
      simp [orientedDoubleArea]
    change orientedDoubleArea 0 1 (((2 + v.b : ℝ) : ℂ) * v.outer.c) ≠ 0
    rw [h]
    exact mul_ne_zero (by linarith [v.b_pos]) v.outer.nondegenerate

noncomputable def VShape.uSplitRatio (v : VShape) : ℝ := 1 / (2 + v.b)

theorem VShape.uSplitRatio_pos (v : VShape) : 0 < v.uSplitRatio := by
  apply one_div_pos.mpr
  linarith [v.b_pos]

theorem VShape.uSplitRatio_lt_one (v : VShape) : v.uSplitRatio < 1 := by
  apply (div_lt_one (by linarith [v.b_pos] : 0 < 2 + v.b)).mpr
  linarith [v.b_pos]

theorem VShape.uSplitPoint (v : VShape) :
    v.uOuter.coordinateEquiv (⟨0, v.uSplitRatio⟩ : ℂ) = v.outer.c := by
  have hd : (2 : ℂ) + (v.b : ℂ) ≠ 0 := by
    exact_mod_cast (show 2 + v.b ≠ 0 by linarith [v.b_pos])
  simp only [Triangle.coordinateEquiv_apply, VShape.uOuter, VShape.uSplitRatio,
    zero_smul, zero_add, sub_zero, add_zero, Complex.real_smul]
  push_cast
  field_simp

theorem VShape.uSplitFirst_eq (v : VShape) :
    v.uOuter.splitFirst v.uSplitRatio v.uSplitRatio_pos = v.outer := by
  apply Triangle.ext
  · change v.uOuter.coordinateEquiv 0 = 0
    exact v.uOuter.coordinateEquiv_zero
  · change v.uOuter.coordinateEquiv 1 = 1
    exact v.uOuter.coordinateEquiv_one
  · exact v.uSplitPoint

noncomputable def VShape.uAttached (v : VShape) : Triangle :=
  v.uOuter.splitSecond v.uSplitRatio v.uSplitRatio_lt_one

theorem VShape.uAttached_a (v : VShape) : v.uAttached.a = v.outer.c := v.uSplitPoint

theorem VShape.uAttached_b (v : VShape) : v.uAttached.b = 1 :=
  v.uOuter.coordinateEquiv_one

theorem VShape.uAttached_c (v : VShape) : v.uAttached.c = v.uOuter.c :=
  v.uOuter.coordinateEquiv_I

theorem VShape.uTop_sub_one (v : VShape) :
    v.uOuter.c - 1 = ((1 + v.b : ℝ) : ℂ) * v.t ^ 3 := by
  change ((2 + v.b : ℝ) : ℂ) * ((v.b : ℂ) * v.t ^ 2) - 1 = _
  push_cast
  linear_combination -((1 + (v.b : ℂ)) * v.t + 1) * v.t_sq

theorem VShape.uTop_sub_C (v : VShape) :
    v.uOuter.c - v.outer.c = ((1 + v.b : ℝ) : ℂ) * v.outer.c := by
  change ((2 + v.b : ℝ) : ℂ) * v.outer.c - v.outer.c = _
  push_cast
  ring

theorem VShape.uOuter_side_squares (v : VShape) :
    Complex.normSq (v.uOuter.b - v.uOuter.a) = 1 ∧
    Complex.normSq (v.uOuter.c - v.uOuter.a) = (v.b * (2 + v.b)) ^ 2 ∧
    Complex.normSq (v.uOuter.c - v.uOuter.b) = (1 + v.b) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [VShape.uOuter]
  · change Complex.normSq (((2 + v.b : ℝ) : ℂ) * ((v.b : ℂ) * v.t ^ 2) - 0) = _
    rw [sub_zero, Complex.normSq_mul, Complex.normSq_mul, map_pow,
      v.normSq_t, Complex.normSq_ofReal, Complex.normSq_ofReal]
    ring
  · change Complex.normSq (v.uOuter.c - 1) = _
    rw [v.uTop_sub_one, Complex.normSq_mul, map_pow, v.normSq_t, Complex.normSq_ofReal]
    ring

/-- The attached piece is an actual ambient-isometric image of `(1+b) R`. -/
theorem VShape.uAttached_congruent (v : VShape) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.reference.mapSimilarity 0 ((1 + v.b : ℝ) : ℂ)
        (by exact_mod_cast (show 1 + v.b ≠ 0 by linarith [v.b_pos]))).carrier =
      v.uAttached.carrier := by
  suffices h : ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.reference.mapSimilarity 0 ((1 + v.b : ℝ) : ℂ)
        (by exact_mod_cast (show 1 + v.b ≠ 0 by linarith [v.b_pos]))).carrier =
      v.uAttached.swapAC.carrier by
    simpa only [Triangle.swapAC_carrier] using h
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + ((1 + v.b : ℝ) : ℂ) * 1) -
        (0 + ((1 + v.b : ℝ) : ℂ) * 0)) =
      Complex.normSq (v.uAttached.b - v.uAttached.c)
    rw [v.uAttached_b, v.uAttached_c]
    simp only [zero_add, mul_one, mul_zero, sub_zero]
    rw [show 1 - v.uOuter.c = -(v.uOuter.c - 1) by ring,
      Complex.normSq_neg, v.uTop_sub_one, Complex.normSq_mul, map_pow, v.normSq_t]
    ring
  · change Complex.normSq ((0 + ((1 + v.b : ℝ) : ℂ) * ((v.b : ℂ) * v.t)) -
        (0 + ((1 + v.b : ℝ) : ℂ) * 0)) =
      Complex.normSq (v.uAttached.a - v.uAttached.c)
    rw [v.uAttached_a, v.uAttached_c]
    simp only [zero_add, mul_zero, sub_zero]
    rw [show v.outer.c - v.uOuter.c = -(v.uOuter.c - v.outer.c) by ring,
      Complex.normSq_neg, v.uTop_sub_C, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_mul, v.normSq_t]
    change Complex.normSq (((1 + v.b : ℝ) : ℂ)) * (Complex.normSq (v.b : ℂ) * 1) =
      Complex.normSq (((1 + v.b : ℝ) : ℂ)) * Complex.normSq ((v.b : ℂ) * v.t ^ 2)
    rw [Complex.normSq_mul, map_pow, v.normSq_t]
    ring
  · change Complex.normSq ((0 + ((1 + v.b : ℝ) : ℂ) * ((v.b : ℂ) * v.t)) -
        (0 + ((1 + v.b : ℝ) : ℂ) * 1)) =
      Complex.normSq (v.uAttached.a - v.uAttached.b)
    rw [v.uAttached_a, v.uAttached_b]
    simp only [zero_add, mul_one]
    rw [show ((1 + v.b : ℝ) : ℂ) * ((v.b : ℂ) * v.t) - ((1 + v.b : ℝ) : ℂ) =
        ((1 + v.b : ℝ) : ℂ) * ((v.b : ℂ) * v.t - 1) by ring,
      Complex.normSq_mul, v.normSq_bt_sub_one, Complex.normSq_ofReal]
    change (1 + v.b) * (1 + v.b) * v.s ^ 2 = Complex.normSq (v.outer.c - v.outer.b)
    rw [v.outer_side_squares.2.2]
    ring

end Erdos633
