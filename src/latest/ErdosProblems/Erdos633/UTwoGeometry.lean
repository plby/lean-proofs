import ErdosProblems.Erdos633.ZTiling

/-!
# The second U family

Extending the reference edge by `(2a+b)/(a+2b)` gives the U₂ outer triangle.
Its two pieces are the reference and a copy of Z scaled by `1/(a+2b)`.
-/

namespace Erdos633

noncomputable def OneTwentyShape.uTwoScale (S : OneTwentyShape) : ℝ :=
  (2 * S.a + S.b) / (S.a + 2 * S.b)

noncomputable def OneTwentyShape.uTwoZScale (S : OneTwentyShape) : ℝ :=
  1 / (S.a + 2 * S.b)

theorem OneTwentyShape.uTwoScale_pos (S : OneTwentyShape) : 0 < S.uTwoScale := by
  apply div_pos <;> linarith [S.a_pos, S.b_pos]

theorem OneTwentyShape.uTwoZScale_pos (S : OneTwentyShape) : 0 < S.uTwoZScale :=
  one_div_pos.mpr (by linarith [S.a_pos, S.b_pos])

theorem OneTwentyShape.uTwoZScale_base (S : OneTwentyShape) :
    S.uTwoZScale * S.zBase = S.uTwoScale * S.b := by
  dsimp [uTwoZScale, uTwoScale, zBase]
  ring

theorem OneTwentyShape.uTwoZScale_leg (S : OneTwentyShape) :
    S.uTwoZScale * S.zLeg = S.a := by
  have h : S.a + 2 * S.b ≠ 0 := by linarith [S.a_pos, S.b_pos]
  dsimp [uTwoZScale, zLeg]
  field_simp

noncomputable def OneTwentyShape.uTwoNormalized (S : OneTwentyShape) : Triangle where
  a := ⟨-S.b, S.b⟩
  b := (S.a : ℂ)
  c := ⟨S.uTwoScale * S.b, -S.uTwoScale * S.b⟩
  nondegenerate := by
    have heq : (S.a - -S.b) * (-S.uTwoScale * S.b - S.b) -
        (0 - S.b) * (S.uTwoScale * S.b - -S.b) = -(S.a * S.b * (1 + S.uTwoScale)) := by ring
    change (S.a - -S.b) * (-S.uTwoScale * S.b - S.b) -
      (0 - S.b) * (S.uTwoScale * S.b - -S.b) ≠ 0
    rw [heq]
    exact neg_ne_zero.mpr (ne_of_gt (mul_pos (mul_pos S.a_pos S.b_pos)
      (by linarith [S.uTwoScale_pos])))

noncomputable def OneTwentyShape.uTwoOuter (S : OneTwentyShape) : Triangle :=
  S.uTwoNormalized.mapAffineEquiv hexCoordinates

@[simp] theorem OneTwentyShape.uTwoOuter_a (S : OneTwentyShape) :
    S.uTwoOuter.a = S.reference.c := rfl

@[simp] theorem OneTwentyShape.uTwoOuter_b (S : OneTwentyShape) :
    S.uTwoOuter.b = S.reference.b := rfl

@[simp] theorem OneTwentyShape.uTwoOuter_c (S : OneTwentyShape) :
    S.uTwoOuter.c = -(S.uTwoScale : ℂ) * S.reference.c := by
  change hexCoordinates ⟨S.uTwoScale * S.b, -S.uTwoScale * S.b⟩ = _
  rw [hexCoordinates_apply, S.reference_c]
  push_cast
  ring

noncomputable def OneTwentyShape.uTwoSplitRatio (S : OneTwentyShape) : ℝ :=
  1 / (1 + S.uTwoScale)

theorem OneTwentyShape.uTwoSplitRatio_pos (S : OneTwentyShape) : 0 < S.uTwoSplitRatio :=
  one_div_pos.mpr (by linarith [S.uTwoScale_pos])

theorem OneTwentyShape.uTwoSplitRatio_lt_one (S : OneTwentyShape) : S.uTwoSplitRatio < 1 := by
  apply (div_lt_one (by linarith [S.uTwoScale_pos] : 0 < 1 + S.uTwoScale)).mpr
  linarith [S.uTwoScale_pos]

theorem OneTwentyShape.uTwoSplitPoint (S : OneTwentyShape) :
    S.uTwoOuter.coordinateEquiv (⟨0, S.uTwoSplitRatio⟩ : ℂ) = 0 := by
  have h : (1 : ℂ) + (S.uTwoScale : ℂ) ≠ 0 := by
    exact_mod_cast (show 1 + S.uTwoScale ≠ 0 by linarith [S.uTwoScale_pos])
  simp only [Triangle.coordinateEquiv_apply, uTwoOuter_a, uTwoOuter_c,
    zero_smul, zero_add, Complex.real_smul, uTwoSplitRatio]
  push_cast
  field_simp
  ring

noncomputable def OneTwentyShape.uTwoReference (S : OneTwentyShape) : Triangle :=
  S.uTwoOuter.splitFirst S.uTwoSplitRatio S.uTwoSplitRatio_pos

noncomputable def OneTwentyShape.uTwoAttached (S : OneTwentyShape) : Triangle :=
  S.uTwoOuter.splitSecond S.uTwoSplitRatio S.uTwoSplitRatio_lt_one

theorem OneTwentyShape.uTwoReference_eq (S : OneTwentyShape) :
    S.uTwoReference = S.reference.swapAC := by
  apply Triangle.ext
  · change (S.uTwoOuter.splitFirst S.uTwoSplitRatio S.uTwoSplitRatio_pos).a = S.reference.c
    rw [Triangle.splitFirst_a, S.uTwoOuter_a]
  · change (S.uTwoOuter.splitFirst S.uTwoSplitRatio S.uTwoSplitRatio_pos).b = S.reference.b
    rw [Triangle.splitFirst_b, S.uTwoOuter_b]
  · change S.uTwoOuter.coordinateEquiv (⟨0, S.uTwoSplitRatio⟩ : ℂ) = S.reference.a
    rw [S.uTwoSplitPoint, S.reference_a]

theorem OneTwentyShape.uTwoAttached_vertices (S : OneTwentyShape) :
    S.uTwoAttached.a = 0 ∧ S.uTwoAttached.b = (S.a : ℂ) ∧
      S.uTwoAttached.c = -(S.uTwoScale : ℂ) * S.reference.c := by
  simp [uTwoAttached, S.uTwoSplitPoint]

theorem OneTwentyShape.uTwoAttached_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.uTwoAttached.b - S.uTwoAttached.a) = S.a ^ 2 ∧
    Complex.normSq (S.uTwoAttached.c - S.uTwoAttached.a) = (S.uTwoScale * S.b) ^ 2 ∧
    Complex.normSq (S.uTwoAttached.c - S.uTwoAttached.b) = (S.uTwoZScale * S.c ^ 2) ^ 2 := by
  have hd : S.a + 2 * S.b ≠ 0 := by linarith [S.a_pos, S.b_pos]
  have href : Complex.normSq S.reference.c = S.b ^ 2 := by
    simpa only [S.reference_a, sub_zero] using S.reference_side_squares.2.1
  rw [S.uTwoAttached_vertices.1, S.uTwoAttached_vertices.2.1, S.uTwoAttached_vertices.2.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_zero, Complex.normSq_ofReal]
    ring
  · rw [sub_zero, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal, href]
    ring
  · rw [S.reference_c]
    have heq : -(S.uTwoScale : ℂ) * ((S.b : ℂ) * (hexUnit - 1)) - (S.a : ℂ) =
        ((S.uTwoScale * S.b - S.a : ℝ) : ℂ) +
          ((-S.uTwoScale * S.b : ℝ) : ℂ) * hexUnit := by
      push_cast
      ring
    rw [heq, normSq_hex_linear, S.conic]
    dsimp [uTwoScale, uTwoZScale]
    field_simp
    ring

theorem OneTwentyShape.uTwoAttached_congruent_Z (S : OneTwentyShape) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (S.zOuter.mapSimilarity 0 (S.uTwoZScale : ℂ)
        (by exact_mod_cast ne_of_gt S.uTwoZScale_pos)).carrier = S.uTwoAttached.carrier := by
  suffices h : ∃ e : ℂ ≃ᵢ ℂ,
      e '' (S.zOuter.mapSimilarity 0 (S.uTwoZScale : ℂ)
        (by exact_mod_cast ne_of_gt S.uTwoZScale_pos)).carrier =
          S.uTwoAttached.swapBC.carrier by
    simpa only [Triangle.swapBC_carrier] using h
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (S.uTwoZScale : ℂ) * S.zOuter.b) -
      (0 + (S.uTwoZScale : ℂ) * S.zOuter.a)) =
        Complex.normSq (S.uTwoAttached.c - S.uTwoAttached.a)
    rw [normSq_similarity_sub, S.zOuter_side_squares.1, Complex.normSq_ofReal,
      S.uTwoAttached_side_squares.2.1]
    calc
      _ = (S.uTwoZScale * S.zBase) ^ 2 := by ring
      _ = _ := by rw [S.uTwoZScale_base]
  · change Complex.normSq ((0 + (S.uTwoZScale : ℂ) * S.zOuter.c) -
      (0 + (S.uTwoZScale : ℂ) * S.zOuter.a)) =
        Complex.normSq (S.uTwoAttached.b - S.uTwoAttached.a)
    rw [normSq_similarity_sub, S.zOuter_side_squares.2.1, Complex.normSq_ofReal,
      S.uTwoAttached_side_squares.1]
    calc
      _ = (S.uTwoZScale * S.zLeg) ^ 2 := by ring
      _ = _ := by rw [S.uTwoZScale_leg]
  · change Complex.normSq ((0 + (S.uTwoZScale : ℂ) * S.zOuter.c) -
      (0 + (S.uTwoZScale : ℂ) * S.zOuter.b)) =
        Complex.normSq (S.uTwoAttached.b - S.uTwoAttached.c)
    rw [normSq_similarity_sub, S.zOuter_side_squares.2.2, Complex.normSq_ofReal,
      show S.uTwoAttached.b - S.uTwoAttached.c =
        -(S.uTwoAttached.c - S.uTwoAttached.b) by ring, Complex.normSq_neg,
      S.uTwoAttached_side_squares.2.2]
    ring

theorem OneTwentyShape.uTwoOuter_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.uTwoOuter.b - S.uTwoOuter.a) = S.c ^ 2 ∧
    Complex.normSq (S.uTwoOuter.c - S.uTwoOuter.a) = ((1 + S.uTwoScale) * S.b) ^ 2 ∧
    Complex.normSq (S.uTwoOuter.c - S.uTwoOuter.b) = (S.uTwoZScale * S.c ^ 2) ^ 2 := by
  rw [S.uTwoOuter_a, S.uTwoOuter_b, S.uTwoOuter_c]
  refine ⟨?_, ?_, ?_⟩
  · rw [show S.reference.b - S.reference.c = -(S.reference.c - S.reference.b) by ring,
      Complex.normSq_neg, S.reference_side_squares.2.2]
  · have href : Complex.normSq S.reference.c = S.b ^ 2 := by
      simpa only [S.reference_a, sub_zero] using S.reference_side_squares.2.1
    rw [show -(S.uTwoScale : ℂ) * S.reference.c - S.reference.c =
      -(((1 + S.uTwoScale : ℝ) : ℂ) * S.reference.c) by push_cast; ring,
      Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal, href]
    ring
  · simpa only [S.uTwoAttached_vertices.2.1, S.uTwoAttached_vertices.2.2,
      S.reference_b] using S.uTwoAttached_side_squares.2.2

theorem OneTwentyShape.uTwoOuter_scaled_side_squares (S : OneTwentyShape) :
    (S.a + 2 * S.b) ^ 2 * Complex.normSq (S.uTwoOuter.b - S.uTwoOuter.a) =
      (S.c * (S.a + 2 * S.b)) ^ 2 ∧
    (S.a + 2 * S.b) ^ 2 * Complex.normSq (S.uTwoOuter.c - S.uTwoOuter.a) =
      (3 * S.b * (S.a + S.b)) ^ 2 ∧
    (S.a + 2 * S.b) ^ 2 * Complex.normSq (S.uTwoOuter.c - S.uTwoOuter.b) = (S.c ^ 2) ^ 2 := by
  have hd : S.a + 2 * S.b ≠ 0 := by linarith [S.a_pos, S.b_pos]
  have hsum : (1 + S.uTwoScale) * (S.a + 2 * S.b) = 3 * (S.a + S.b) := by
    dsimp [uTwoScale]
    field_simp
    ring
  have hscale : S.uTwoZScale * (S.a + 2 * S.b) = 1 := by
    dsimp [uTwoZScale]
    field_simp
  rw [S.uTwoOuter_side_squares.1, S.uTwoOuter_side_squares.2.1,
    S.uTwoOuter_side_squares.2.2]
  refine ⟨by ring, ?_, ?_⟩
  · calc
      _ = (S.b * ((1 + S.uTwoScale) * (S.a + 2 * S.b))) ^ 2 := by ring
      _ = _ := by rw [hsum]; ring
  · calc
      _ = ((S.uTwoZScale * (S.a + 2 * S.b)) * S.c ^ 2) ^ 2 := by ring
      _ = _ := by rw [hscale, one_mul]

end Erdos633
