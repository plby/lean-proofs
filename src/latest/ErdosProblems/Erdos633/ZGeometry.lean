import ErdosProblems.Erdos633.YTiling

/-!
# The Z outer triangle

In hexagonal coordinates Z has vertices `0`, `b(2a+b)`, and `a(a+2b) I`.
A vertex-to-side split gives scaled W and Y pieces. All identifications
below concern the actual closed triangular regions.
-/

namespace Erdos633

noncomputable def OneTwentyShape.zBase (S : OneTwentyShape) : ℝ := S.b * (2 * S.a + S.b)
noncomputable def OneTwentyShape.zLeg (S : OneTwentyShape) : ℝ := S.a * (S.a + 2 * S.b)
noncomputable def OneTwentyShape.zWScale (S : OneTwentyShape) : ℝ := S.b * (1 + S.yScale)

theorem OneTwentyShape.zBase_pos (S : OneTwentyShape) : 0 < S.zBase := by
  exact mul_pos S.b_pos (by linarith [S.a_pos, S.b_pos])

theorem OneTwentyShape.zLeg_pos (S : OneTwentyShape) : 0 < S.zLeg := by
  exact mul_pos S.a_pos (by linarith [S.a_pos, S.b_pos])

theorem OneTwentyShape.zWScale_pos (S : OneTwentyShape) : 0 < S.zWScale := by
  exact mul_pos S.b_pos (by linarith [S.yScale_pos])

theorem OneTwentyShape.zBase_eq (S : OneTwentyShape) :
    S.zWScale * (S.a + S.b) = S.zBase := by
  have hsum : (1 + S.yScale) * (S.a + S.b) = 2 * S.a + S.b := by
    nlinarith [S.yScale_mul_sum]
  change (S.b * (1 + S.yScale)) * (S.a + S.b) = S.b * (2 * S.a + S.b)
  rw [mul_assoc, hsum]

theorem OneTwentyShape.zLeg_eq (S : OneTwentyShape) :
    S.zLeg = S.a * S.zWScale + S.yScale * S.c ^ 2 := by
  have hab0 := ne_of_gt (add_pos S.a_pos S.b_pos)
  dsimp [zLeg, zWScale, yScale]
  rw [S.conic]
  field_simp
  ring

noncomputable def OneTwentyShape.zNormalized (S : OneTwentyShape) : Triangle where
  a := 0
  b := (S.zBase : ℂ)
  c := ⟨0, S.zLeg⟩
  nondegenerate := by
    simpa using mul_ne_zero (ne_of_gt S.zBase_pos) (ne_of_gt S.zLeg_pos)

noncomputable def OneTwentyShape.zOuter (S : OneTwentyShape) : Triangle :=
  S.zNormalized.mapAffineEquiv hexCoordinates

@[simp] theorem OneTwentyShape.zOuter_a (S : OneTwentyShape) : S.zOuter.a = 0 := by
  change hexCoordinates 0 = 0
  simp [hexCoordinates_apply]

@[simp] theorem OneTwentyShape.zOuter_b (S : OneTwentyShape) :
    S.zOuter.b = (S.zBase : ℂ) := by
  change hexCoordinates (S.zBase : ℂ) = _
  simp [hexCoordinates_apply]

@[simp] theorem OneTwentyShape.zOuter_c (S : OneTwentyShape) :
    S.zOuter.c = (S.zLeg : ℂ) * hexUnit := by
  change hexCoordinates ⟨0, S.zLeg⟩ = _
  simp [hexCoordinates_apply]

theorem OneTwentyShape.zOuter_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.zOuter.b - S.zOuter.a) = S.zBase ^ 2 ∧
    Complex.normSq (S.zOuter.c - S.zOuter.a) = S.zLeg ^ 2 ∧
    Complex.normSq (S.zOuter.c - S.zOuter.b) = (S.c ^ 2) ^ 2 := by
  rw [S.zOuter_a, S.zOuter_b, S.zOuter_c]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_zero, Complex.normSq_ofReal]
    ring
  · rw [sub_zero, Complex.normSq_mul, hexUnit_normSq, Complex.normSq_ofReal]
    ring
  · rw [show (S.zLeg : ℂ) * hexUnit - (S.zBase : ℂ) =
      ((-S.zBase : ℝ) : ℂ) + (S.zLeg : ℂ) * hexUnit by push_cast; ring,
      normSq_hex_linear, S.conic]
    dsimp [zBase, zLeg]
    ring

noncomputable def OneTwentyShape.zSplitRatio (S : OneTwentyShape) : ℝ :=
  S.a * S.zWScale / S.zLeg

theorem OneTwentyShape.zSplitRatio_pos (S : OneTwentyShape) : 0 < S.zSplitRatio :=
  div_pos (mul_pos S.a_pos S.zWScale_pos) S.zLeg_pos

theorem OneTwentyShape.zSplitRatio_lt_one (S : OneTwentyShape) : S.zSplitRatio < 1 := by
  apply (div_lt_one S.zLeg_pos).mpr
  rw [S.zLeg_eq]
  have h := mul_pos S.yScale_pos (sq_pos_of_pos S.c_pos)
  linarith

theorem OneTwentyShape.zSplitPoint (S : OneTwentyShape) :
    S.zOuter.coordinateEquiv (⟨0, S.zSplitRatio⟩ : ℂ) =
      ((S.a * S.zWScale : ℝ) : ℂ) * hexUnit := by
  have h : (S.zLeg : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt S.zLeg_pos
  simp only [Triangle.coordinateEquiv_apply, zOuter_a, zOuter_c, zSplitRatio,
    zero_smul, zero_add, sub_zero, add_zero, Complex.real_smul]
  push_cast
  field_simp

noncomputable def OneTwentyShape.zW (S : OneTwentyShape) : Triangle :=
  S.zOuter.splitFirst S.zSplitRatio S.zSplitRatio_pos

noncomputable def OneTwentyShape.zY (S : OneTwentyShape) : Triangle :=
  S.zOuter.splitSecond S.zSplitRatio S.zSplitRatio_lt_one

theorem OneTwentyShape.zW_eq (S : OneTwentyShape) :
    S.zW = (S.wOuter.mapSimilarity 0 (S.zWScale : ℂ)
      (by exact_mod_cast ne_of_gt S.zWScale_pos)).swapBC := by
  apply Triangle.ext
  · change (S.zOuter.splitFirst S.zSplitRatio S.zSplitRatio_pos).a =
      0 + (S.zWScale : ℂ) * S.wOuter.a
    simp
  · change (S.zOuter.splitFirst S.zSplitRatio S.zSplitRatio_pos).b =
      0 + (S.zWScale : ℂ) * S.wOuter.c
    rw [Triangle.splitFirst_b, S.zOuter_b, S.wOuter_c, zero_add]
    exact_mod_cast S.zBase_eq.symm
  · change S.zOuter.coordinateEquiv (⟨0, S.zSplitRatio⟩ : ℂ) =
      0 + (S.zWScale : ℂ) * S.wOuter.b
    rw [S.zSplitPoint, S.wOuter_b]
    push_cast
    ring

theorem OneTwentyShape.zY_vertices (S : OneTwentyShape) :
    S.zY.a = ((S.a * S.zWScale : ℝ) : ℂ) * hexUnit ∧
    S.zY.b = (S.zBase : ℂ) ∧ S.zY.c = (S.zLeg : ℂ) * hexUnit := by
  simp [zY, S.zSplitPoint]

theorem OneTwentyShape.zY_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.zY.b - S.zY.a) = (S.zWScale * S.c) ^ 2 ∧
    Complex.normSq (S.zY.c - S.zY.a) = (S.yScale * S.c ^ 2) ^ 2 ∧
    Complex.normSq (S.zY.c - S.zY.b) = (S.c ^ 2) ^ 2 := by
  rw [S.zY_vertices.1, S.zY_vertices.2.1, S.zY_vertices.2.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [← S.zBase_eq]
    have heq : ((S.zWScale * (S.a + S.b) : ℝ) : ℂ) -
        ((S.a * S.zWScale : ℝ) : ℂ) * hexUnit =
          (S.zWScale : ℂ) * (S.wOuter.c - S.wOuter.b) := by
      rw [S.wOuter_b, S.wOuter_c]
      push_cast
      ring
    rw [heq, Complex.normSq_mul, S.wOuter_side_squares.2.2, Complex.normSq_ofReal]
    ring
  · have heq : (S.zLeg : ℂ) * hexUnit - ((S.a * S.zWScale : ℝ) : ℂ) * hexUnit =
        ((S.yScale * S.c ^ 2 : ℝ) : ℂ) * hexUnit := by
      rw [S.zLeg_eq]
      push_cast
      ring
    rw [heq, Complex.normSq_mul, hexUnit_normSq, Complex.normSq_ofReal]
    ring
  · simpa only [S.zOuter_b, S.zOuter_c] using S.zOuter_side_squares.2.2

theorem OneTwentyShape.zY_congruent (S : OneTwentyShape) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' (S.yOuter.mapSimilarity 0 (S.c : ℂ)
      (by exact_mod_cast ne_of_gt S.c_pos)).carrier = S.zY.carrier := by
  suffices h : ∃ e : ℂ ≃ᵢ ℂ, e '' (S.yOuter.mapSimilarity 0 (S.c : ℂ)
      (by exact_mod_cast ne_of_gt S.c_pos)).carrier = S.zY.rotate.carrier by
    simpa only [Triangle.rotate_carrier] using h
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (S.c : ℂ) * S.yOuter.b) -
      (0 + (S.c : ℂ) * S.yOuter.a)) = Complex.normSq (S.zY.c - S.zY.b)
    rw [normSq_similarity_sub, S.yOuter_side_squares.1,
      Complex.normSq_ofReal, S.zY_side_squares.2.2]
    ring
  · change Complex.normSq ((0 + (S.c : ℂ) * S.yOuter.c) -
      (0 + (S.c : ℂ) * S.yOuter.a)) = Complex.normSq (S.zY.a - S.zY.b)
    rw [normSq_similarity_sub, S.yOuter_side_squares.2.1,
      Complex.normSq_ofReal, show S.zY.a - S.zY.b = -(S.zY.b - S.zY.a) by ring,
      Complex.normSq_neg, S.zY_side_squares.1]
    dsimp [zWScale]
    ring
  · change Complex.normSq ((0 + (S.c : ℂ) * S.yOuter.c) -
      (0 + (S.c : ℂ) * S.yOuter.b)) = Complex.normSq (S.zY.a - S.zY.c)
    rw [normSq_similarity_sub, S.yOuter_side_squares.2.2,
      Complex.normSq_ofReal, show S.zY.a - S.zY.c = -(S.zY.c - S.zY.a) by ring,
      Complex.normSq_neg, S.zY_side_squares.2.1]
    ring

end Erdos633
