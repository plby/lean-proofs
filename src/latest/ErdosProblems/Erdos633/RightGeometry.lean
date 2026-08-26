import ErdosProblems.Erdos633.Split
import ErdosProblems.Erdos633.Congruence

/-!
# The altitude split of a right triangle

The right vertex is the second vertex. Both altitude pieces are proved
congruent to the appropriate positive scales of the original triangle.
-/

namespace Erdos633

structure RightShape where
  x : ℝ
  y : ℝ
  x_pos : 0 < x
  y_pos : 0 < y

def RightShape.triangle (v : RightShape) : Triangle where
  a := (v.x : ℂ)
  b := 0
  c := ⟨0, v.y⟩
  nondegenerate := by
    change orientedDoubleArea (v.x : ℂ) 0 ⟨0, v.y⟩ ≠ 0
    simpa [orientedDoubleArea] using neg_ne_zero.mpr (ne_of_gt (mul_pos v.x_pos v.y_pos))

theorem RightShape.sum_sq_pos (v : RightShape) : 0 < v.x ^ 2 + v.y ^ 2 := by
  exact add_pos (sq_pos_of_pos v.x_pos) (sq_pos_of_pos v.y_pos)

noncomputable def RightShape.c (v : RightShape) : ℝ := Real.sqrt (v.x ^ 2 + v.y ^ 2)

theorem RightShape.c_pos (v : RightShape) : 0 < v.c := Real.sqrt_pos.mpr v.sum_sq_pos

theorem RightShape.c_sq (v : RightShape) : v.c ^ 2 = v.x ^ 2 + v.y ^ 2 :=
  Real.sq_sqrt v.sum_sq_pos.le

noncomputable def RightShape.r (v : RightShape) : ℝ := v.x ^ 2 / (v.x ^ 2 + v.y ^ 2)

theorem RightShape.r_pos (v : RightShape) : 0 < v.r :=
  div_pos (sq_pos_of_pos v.x_pos) v.sum_sq_pos

theorem RightShape.r_lt_one (v : RightShape) : v.r < 1 := by
  apply (div_lt_one v.sum_sq_pos).mpr
  linarith [sq_pos_of_pos v.y_pos]

theorem RightShape.splitPoint (v : RightShape) :
    v.triangle.coordinateEquiv (⟨0, v.r⟩ : ℂ) =
      (⟨v.x * v.y ^ 2 / (v.x ^ 2 + v.y ^ 2),
        v.x ^ 2 * v.y / (v.x ^ 2 + v.y ^ 2)⟩ : ℂ) := by
  have hd := ne_of_gt v.sum_sq_pos
  apply Complex.ext
  all_goals simp only [Triangle.coordinateEquiv_apply, RightShape.triangle, RightShape.r,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.smul_re,
    Complex.smul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
    Complex.zero_im, smul_eq_mul]
  all_goals field_simp
  all_goals ring

theorem RightShape.side_squares (v : RightShape) :
    Complex.normSq (v.triangle.b - v.triangle.a) = v.x ^ 2 ∧
    Complex.normSq (v.triangle.c - v.triangle.a) = v.x ^ 2 + v.y ^ 2 ∧
    Complex.normSq (v.triangle.c - v.triangle.b) = v.y ^ 2 := by
  simp only [RightShape.triangle, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im]
  constructor
  · ring
  constructor <;> ring

theorem RightShape.normSq_splitPoint (v : RightShape) :
    Complex.normSq (v.triangle.coordinateEquiv (⟨0, v.r⟩ : ℂ)) =
      v.x ^ 2 * v.y ^ 2 / (v.x ^ 2 + v.y ^ 2) := by
  have hd := ne_of_gt v.sum_sq_pos
  rw [v.splitPoint]
  simp only [Complex.normSq_apply]
  field_simp
  ring

theorem RightShape.normSq_splitPoint_sub_a (v : RightShape) :
    Complex.normSq (v.triangle.coordinateEquiv (⟨0, v.r⟩ : ℂ) - v.triangle.a) =
      v.x ^ 4 / (v.x ^ 2 + v.y ^ 2) := by
  have hd := ne_of_gt v.sum_sq_pos
  rw [v.splitPoint]
  simp only [RightShape.triangle, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

theorem RightShape.normSq_c_sub_splitPoint (v : RightShape) :
    Complex.normSq (v.triangle.c - v.triangle.coordinateEquiv (⟨0, v.r⟩ : ℂ)) =
      v.y ^ 4 / (v.x ^ 2 + v.y ^ 2) := by
  have hd := ne_of_gt v.sum_sq_pos
  rw [v.splitPoint]
  simp only [RightShape.triangle, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  field_simp
  ring

theorem RightShape.first_congruent (v : RightShape) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.triangle.mapSimilarity 0 ((v.x / v.c : ℝ) : ℂ)
        (by exact_mod_cast ne_of_gt (div_pos v.x_pos v.c_pos))).carrier =
      (v.triangle.splitFirst v.r v.r_pos).carrier := by
  have hd := ne_of_gt v.sum_sq_pos
  suffices h : ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.triangle.mapSimilarity 0 ((v.x / v.c : ℝ) : ℂ)
        (by exact_mod_cast ne_of_gt (div_pos v.x_pos v.c_pos))).carrier =
      (v.triangle.splitFirst v.r v.r_pos).swapBC.carrier by
    simpa only [Triangle.swapBC_carrier] using h
  apply Triangle.congruent_of_normSq
  all_goals simp only [Triangle.mapSimilarity, Triangle.swapBC, Triangle.splitFirst_a,
    Triangle.splitFirst_b, Triangle.splitFirst_c, normSq_similarity_sub,
    Complex.normSq_ofReal, ← pow_two (v.x / v.c), div_pow, v.c_sq]
  · rw [v.side_squares.1, v.normSq_splitPoint_sub_a]
    field_simp
  · rw [v.side_squares.2.1, v.side_squares.1]
    field_simp
  · rw [v.side_squares.2.2]
    change v.x ^ 2 / (v.x ^ 2 + v.y ^ 2) * v.y ^ 2 =
      Complex.normSq (0 - v.triangle.coordinateEquiv (⟨0, v.r⟩ : ℂ))
    rw [zero_sub, Complex.normSq_neg, v.normSq_splitPoint]
    ring

theorem RightShape.second_congruent (v : RightShape) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.triangle.mapSimilarity 0 ((v.y / v.c : ℝ) : ℂ)
        (by exact_mod_cast ne_of_gt (div_pos v.y_pos v.c_pos))).carrier =
      (v.triangle.splitSecond v.r v.r_lt_one).carrier := by
  have hd := ne_of_gt v.sum_sq_pos
  suffices h : ∃ e : ℂ ≃ᵢ ℂ,
      e '' (v.triangle.mapSimilarity 0 ((v.y / v.c : ℝ) : ℂ)
        (by exact_mod_cast ne_of_gt (div_pos v.y_pos v.c_pos))).carrier =
      (v.triangle.splitSecond v.r v.r_lt_one).swapAB.carrier by
    simpa only [Triangle.swapAB_carrier] using h
  apply Triangle.congruent_of_normSq
  all_goals simp only [Triangle.mapSimilarity, Triangle.swapAB, Triangle.splitSecond_a,
    Triangle.splitSecond_b, Triangle.splitSecond_c, normSq_similarity_sub,
    Complex.normSq_ofReal, ← pow_two (v.y / v.c), div_pow, v.c_sq]
  · rw [v.side_squares.1]
    change v.y ^ 2 / (v.x ^ 2 + v.y ^ 2) * v.x ^ 2 =
      Complex.normSq (v.triangle.coordinateEquiv (⟨0, v.r⟩ : ℂ) - 0)
    rw [sub_zero, v.normSq_splitPoint]
    ring
  · rw [v.side_squares.2.1, v.side_squares.2.2]
    field_simp
  · rw [v.side_squares.2.2, v.normSq_c_sub_splitPoint]
    field_simp

end Erdos633
