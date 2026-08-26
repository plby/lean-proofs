import ErdosProblems.Erdos633.OneTwentyCriteria
import ErdosProblems.Erdos633.Split

/-!
# The W outer triangle

The triangle with sides `a,a+b,c` and a 60-degree angle splits into an
equilateral triangle of side `a` and a triangle congruent to the reference.
-/

namespace Erdos633

theorem normSq_hex_linear (x y : ℝ) :
    Complex.normSq ((x : ℂ) + (y : ℂ) * hexUnit) = x ^ 2 + x * y + y ^ 2 := by
  simpa [hexCoordinates_apply] using hexCoordinates_normSq_sub (⟨x, y⟩ : ℂ) 0

def OneTwentyShape.wNormalized (S : OneTwentyShape) : Triangle where
  a := 0
  b := ⟨0, S.a⟩
  c := ((S.a + S.b : ℝ) : ℂ)
  nondegenerate := by
    simpa using neg_ne_zero.mpr
      (mul_ne_zero (ne_of_gt S.a_pos) (ne_of_gt (add_pos S.a_pos S.b_pos)))

noncomputable def OneTwentyShape.wOuter (S : OneTwentyShape) : Triangle :=
  S.wNormalized.mapAffineEquiv hexCoordinates

@[simp] theorem OneTwentyShape.wOuter_a (S : OneTwentyShape) : S.wOuter.a = 0 := by
  change hexCoordinates 0 = 0
  simp [hexCoordinates_apply]

@[simp] theorem OneTwentyShape.wOuter_b (S : OneTwentyShape) :
    S.wOuter.b = (S.a : ℂ) * hexUnit := by
  change hexCoordinates ⟨0, S.a⟩ = _
  simp [hexCoordinates_apply]

@[simp] theorem OneTwentyShape.wOuter_c (S : OneTwentyShape) :
    S.wOuter.c = ((S.a + S.b : ℝ) : ℂ) := by
  change hexCoordinates ((S.a + S.b : ℝ) : ℂ) = _
  simp [hexCoordinates_apply]

noncomputable def OneTwentyShape.wSplitRatio (S : OneTwentyShape) : ℝ := S.a / (S.a + S.b)

theorem OneTwentyShape.wSplitRatio_pos (S : OneTwentyShape) : 0 < S.wSplitRatio :=
  div_pos S.a_pos (add_pos S.a_pos S.b_pos)

theorem OneTwentyShape.wSplitRatio_lt_one (S : OneTwentyShape) : S.wSplitRatio < 1 := by
  apply (div_lt_one (add_pos S.a_pos S.b_pos)).mpr
  linarith [S.b_pos]

theorem OneTwentyShape.wSplitPoint (S : OneTwentyShape) :
    S.wOuter.coordinateEquiv (⟨0, S.wSplitRatio⟩ : ℂ) = (S.a : ℂ) := by
  have h : ((S.a + S.b : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos S.a_pos S.b_pos)
  push_cast at h
  simp only [Triangle.coordinateEquiv_apply, wOuter_a, wOuter_c,
    zero_smul, zero_add, sub_zero, add_zero, Complex.real_smul, wSplitRatio]
  push_cast
  field_simp

noncomputable def OneTwentyShape.wEquilateral (S : OneTwentyShape) : Triangle :=
  S.wOuter.splitFirst S.wSplitRatio S.wSplitRatio_pos

noncomputable def OneTwentyShape.wAttached (S : OneTwentyShape) : Triangle :=
  S.wOuter.splitSecond S.wSplitRatio S.wSplitRatio_lt_one

theorem OneTwentyShape.wEquilateral_vertices (S : OneTwentyShape) :
    S.wEquilateral.a = 0 ∧ S.wEquilateral.b = (S.a : ℂ) * hexUnit ∧
      S.wEquilateral.c = (S.a : ℂ) := by
  simp [wEquilateral, S.wSplitPoint]

theorem OneTwentyShape.wAttached_vertices (S : OneTwentyShape) :
    S.wAttached.a = (S.a : ℂ) ∧ S.wAttached.b = (S.a : ℂ) * hexUnit ∧
      S.wAttached.c = ((S.a + S.b : ℝ) : ℂ) := by
  simp [wAttached, S.wSplitPoint]

theorem OneTwentyShape.wEquilateral_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.wEquilateral.b - S.wEquilateral.a) = S.a ^ 2 ∧
    Complex.normSq (S.wEquilateral.c - S.wEquilateral.a) = S.a ^ 2 ∧
    Complex.normSq (S.wEquilateral.c - S.wEquilateral.b) = S.a ^ 2 := by
  rw [S.wEquilateral_vertices.1, S.wEquilateral_vertices.2.1,
    S.wEquilateral_vertices.2.2]
  simp only [sub_zero, Complex.normSq_mul, Complex.normSq_ofReal,
    hexUnit_normSq, mul_one]
  refine ⟨by ring, by ring, ?_⟩
  rw [show (S.a : ℂ) - (S.a : ℂ) * hexUnit = -((S.a : ℂ) * (hexUnit - 1)) by ring,
    Complex.normSq_neg, Complex.normSq_mul, hexUnit_sub_one_normSq,
    Complex.normSq_ofReal]
  ring

theorem OneTwentyShape.wAttached_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.wAttached.b - S.wAttached.a) = S.a ^ 2 ∧
    Complex.normSq (S.wAttached.c - S.wAttached.a) = S.b ^ 2 ∧
    Complex.normSq (S.wAttached.c - S.wAttached.b) = S.c ^ 2 := by
  rw [S.wAttached_vertices.1, S.wAttached_vertices.2.1, S.wAttached_vertices.2.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [show (S.a : ℂ) * hexUnit - (S.a : ℂ) = (S.a : ℂ) * (hexUnit - 1) by ring,
      Complex.normSq_mul, hexUnit_sub_one_normSq, Complex.normSq_ofReal]
    ring
  · rw [show ((S.a + S.b : ℝ) : ℂ) - (S.a : ℂ) = (S.b : ℂ) by push_cast; ring,
      Complex.normSq_ofReal]
    ring
  · rw [show ((S.a + S.b : ℝ) : ℂ) - (S.a : ℂ) * hexUnit =
      ((S.a + S.b : ℝ) : ℂ) + ((-S.a : ℝ) : ℂ) * hexUnit by push_cast; ring,
      normSq_hex_linear, S.conic]
    ring

theorem OneTwentyShape.wAttached_congruent (S : OneTwentyShape) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' S.reference.carrier = S.wAttached.carrier := by
  apply Triangle.congruent_of_normSq
  · rw [S.reference_side_squares.1, S.wAttached_side_squares.1]
  · rw [S.reference_side_squares.2.1, S.wAttached_side_squares.2.1]
  · rw [S.reference_side_squares.2.2, S.wAttached_side_squares.2.2]

theorem OneTwentyShape.wOuter_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.wOuter.b - S.wOuter.a) = S.a ^ 2 ∧
    Complex.normSq (S.wOuter.c - S.wOuter.a) = (S.a + S.b) ^ 2 ∧
    Complex.normSq (S.wOuter.c - S.wOuter.b) = S.c ^ 2 := by
  rw [S.wOuter_a, S.wOuter_b, S.wOuter_c]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_zero, Complex.normSq_mul, Complex.normSq_ofReal,
      hexUnit_normSq]
    ring
  · rw [sub_zero, Complex.normSq_ofReal]
    ring
  · simpa only [S.wAttached_vertices.2.1, S.wAttached_vertices.2.2] using
      S.wAttached_side_squares.2.2

end Erdos633
