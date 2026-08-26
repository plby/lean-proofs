import ErdosProblems.Erdos633.WTiling

/-!
# The Y outer triangle

Extending the reference edge through its 120-degree vertex gives a triangle
whose first piece is the reference itself. The second piece is congruent to
`a/(a+b)` times the W triangle with the two short reference sides exchanged.
-/

namespace Erdos633

theorem OneTwentyShape.reference_swap_congruent (S : OneTwentyShape) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' S.reference.carrier = S.swap.reference.carrier := by
  suffices h : ∃ e : ℂ ≃ᵢ ℂ,
      e '' S.reference.carrier = S.swap.reference.swapBC.carrier by
    simpa only [Triangle.swapBC_carrier] using h
  apply Triangle.congruent_of_normSq
  · change Complex.normSq (S.reference.b - S.reference.a) =
      Complex.normSq (S.swap.reference.c - S.swap.reference.a)
    rw [S.reference_side_squares.1, S.swap.reference_side_squares.2.1]
    rfl
  · change Complex.normSq (S.reference.c - S.reference.a) =
      Complex.normSq (S.swap.reference.b - S.swap.reference.a)
    rw [S.reference_side_squares.2.1, S.swap.reference_side_squares.1]
    rfl
  · change Complex.normSq (S.reference.c - S.reference.b) =
      Complex.normSq (S.swap.reference.b - S.swap.reference.c)
    rw [show S.swap.reference.b - S.swap.reference.c =
      -(S.swap.reference.c - S.swap.reference.b) by ring, Complex.normSq_neg,
      S.reference_side_squares.2.2, S.swap.reference_side_squares.2.2]
    rfl

theorem OneTwentyShape.smallTile_swap_congruent (S : OneTwentyShape)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' (S.smallTile ε hε).carrier =
      (S.swap.smallTile ε hε).carrier :=
  Triangle.congruent_mapSimilarity S.reference_swap_congruent 0 (ε : ℂ)
    (by exact_mod_cast ne_of_gt hε)

noncomputable def OneTwentyShape.yScale (S : OneTwentyShape) : ℝ := S.a / (S.a + S.b)

theorem OneTwentyShape.yScale_pos (S : OneTwentyShape) : 0 < S.yScale :=
  div_pos S.a_pos (add_pos S.a_pos S.b_pos)

theorem OneTwentyShape.yScale_mul_sum (S : OneTwentyShape) :
    S.yScale * (S.a + S.b) = S.a := by
  dsimp [yScale]
  exact div_mul_cancel₀ _ (ne_of_gt (add_pos S.a_pos S.b_pos))

noncomputable def OneTwentyShape.yNormalized (S : OneTwentyShape) : Triangle where
  a := ⟨-S.b, S.b⟩
  b := (S.a : ℂ)
  c := ⟨S.yScale * S.b, -S.yScale * S.b⟩
  nondegenerate := by
    have heq : (S.a - -S.b) * (-S.yScale * S.b - S.b) -
        (0 - S.b) * (S.yScale * S.b - -S.b) = -(S.a * S.b * (1 + S.yScale)) := by ring
    change (S.a - -S.b) * (-S.yScale * S.b - S.b) -
      (0 - S.b) * (S.yScale * S.b - -S.b) ≠ 0
    rw [heq]
    exact neg_ne_zero.mpr (ne_of_gt (mul_pos (mul_pos S.a_pos S.b_pos)
      (by linarith [S.yScale_pos])))

noncomputable def OneTwentyShape.yOuter (S : OneTwentyShape) : Triangle :=
  S.yNormalized.mapAffineEquiv hexCoordinates

@[simp] theorem OneTwentyShape.yOuter_a (S : OneTwentyShape) :
    S.yOuter.a = S.reference.c := rfl

@[simp] theorem OneTwentyShape.yOuter_b (S : OneTwentyShape) :
    S.yOuter.b = S.reference.b := rfl

@[simp] theorem OneTwentyShape.yOuter_c (S : OneTwentyShape) :
    S.yOuter.c = -(S.yScale : ℂ) * S.reference.c := by
  change hexCoordinates ⟨S.yScale * S.b, -S.yScale * S.b⟩ = _
  rw [hexCoordinates_apply, S.reference_c]
  push_cast
  ring

noncomputable def OneTwentyShape.ySplitRatio (S : OneTwentyShape) : ℝ := 1 / (1 + S.yScale)

theorem OneTwentyShape.ySplitRatio_pos (S : OneTwentyShape) : 0 < S.ySplitRatio :=
  one_div_pos.mpr (by linarith [S.yScale_pos])

theorem OneTwentyShape.ySplitRatio_lt_one (S : OneTwentyShape) : S.ySplitRatio < 1 := by
  apply (div_lt_one (by linarith [S.yScale_pos] : 0 < 1 + S.yScale)).mpr
  linarith [S.yScale_pos]

theorem OneTwentyShape.ySplitPoint (S : OneTwentyShape) :
    S.yOuter.coordinateEquiv (⟨0, S.ySplitRatio⟩ : ℂ) = 0 := by
  have h : (1 : ℂ) + (S.yScale : ℂ) ≠ 0 := by
    exact_mod_cast (show 1 + S.yScale ≠ 0 by linarith [S.yScale_pos])
  simp only [Triangle.coordinateEquiv_apply, yOuter_a, yOuter_c,
    zero_smul, zero_add, Complex.real_smul, ySplitRatio]
  push_cast
  field_simp
  ring

noncomputable def OneTwentyShape.yReference (S : OneTwentyShape) : Triangle :=
  S.yOuter.splitFirst S.ySplitRatio S.ySplitRatio_pos

noncomputable def OneTwentyShape.yAttached (S : OneTwentyShape) : Triangle :=
  S.yOuter.splitSecond S.ySplitRatio S.ySplitRatio_lt_one

theorem OneTwentyShape.yReference_eq (S : OneTwentyShape) :
    S.yReference = S.reference.swapAC := by
  apply Triangle.ext
  · change (S.yOuter.splitFirst S.ySplitRatio S.ySplitRatio_pos).a = S.reference.c
    rw [Triangle.splitFirst_a, S.yOuter_a]
  · change (S.yOuter.splitFirst S.ySplitRatio S.ySplitRatio_pos).b = S.reference.b
    rw [Triangle.splitFirst_b, S.yOuter_b]
  · change S.yOuter.coordinateEquiv (⟨0, S.ySplitRatio⟩ : ℂ) = S.reference.a
    rw [S.ySplitPoint, S.reference_a]

theorem OneTwentyShape.yAttached_vertices (S : OneTwentyShape) :
    S.yAttached.a = 0 ∧ S.yAttached.b = (S.a : ℂ) ∧
      S.yAttached.c = -(S.yScale : ℂ) * S.reference.c := by
  simp [yAttached, S.ySplitPoint]

theorem OneTwentyShape.yAttached_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.yAttached.b - S.yAttached.a) = S.a ^ 2 ∧
    Complex.normSq (S.yAttached.c - S.yAttached.a) = (S.yScale * S.b) ^ 2 ∧
    Complex.normSq (S.yAttached.c - S.yAttached.b) = (S.yScale * S.c) ^ 2 := by
  have hab0 := ne_of_gt (add_pos S.a_pos S.b_pos)
  have href : Complex.normSq S.reference.c = S.b ^ 2 := by
    simpa only [S.reference_a, sub_zero] using S.reference_side_squares.2.1
  rw [S.yAttached_vertices.1, S.yAttached_vertices.2.1, S.yAttached_vertices.2.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_zero, Complex.normSq_ofReal]
    ring
  · rw [sub_zero, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal, href]
    ring
  · rw [S.reference_c]
    have heq : -(S.yScale : ℂ) * ((S.b : ℂ) * (hexUnit - 1)) - (S.a : ℂ) =
        ((S.yScale * S.b - S.a : ℝ) : ℂ) + ((-S.yScale * S.b : ℝ) : ℂ) * hexUnit := by
      push_cast
      ring
    rw [heq, normSq_hex_linear]
    dsimp [yScale]
    simp only [mul_pow]
    rw [S.conic]
    field_simp
    ring

theorem OneTwentyShape.yAttached_congruent_W (S : OneTwentyShape) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (S.swap.wOuter.mapSimilarity 0 (S.yScale : ℂ)
        (by exact_mod_cast ne_of_gt S.yScale_pos)).carrier = S.yAttached.carrier := by
  suffices h : ∃ e : ℂ ≃ᵢ ℂ,
      e '' (S.swap.wOuter.mapSimilarity 0 (S.yScale : ℂ)
        (by exact_mod_cast ne_of_gt S.yScale_pos)).carrier = S.yAttached.swapBC.carrier by
    simpa only [Triangle.swapBC_carrier] using h
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (S.yScale : ℂ) * S.swap.wOuter.b) -
      (0 + (S.yScale : ℂ) * S.swap.wOuter.a)) =
        Complex.normSq (S.yAttached.c - S.yAttached.a)
    rw [normSq_similarity_sub, S.swap.wOuter_side_squares.1,
      Complex.normSq_ofReal, S.yAttached_side_squares.2.1]
    change S.yScale * S.yScale * S.b ^ 2 = (S.yScale * S.b) ^ 2
    ring
  · change Complex.normSq ((0 + (S.yScale : ℂ) * S.swap.wOuter.c) -
      (0 + (S.yScale : ℂ) * S.swap.wOuter.a)) =
        Complex.normSq (S.yAttached.b - S.yAttached.a)
    rw [normSq_similarity_sub, S.swap.wOuter_side_squares.2.1,
      Complex.normSq_ofReal, S.yAttached_side_squares.1]
    change S.yScale * S.yScale * (S.b + S.a) ^ 2 = S.a ^ 2
    calc
      _ = (S.yScale * (S.a + S.b)) ^ 2 := by ring
      _ = _ := by rw [S.yScale_mul_sum]
  · change Complex.normSq ((0 + (S.yScale : ℂ) * S.swap.wOuter.c) -
      (0 + (S.yScale : ℂ) * S.swap.wOuter.b)) =
        Complex.normSq (S.yAttached.b - S.yAttached.c)
    rw [normSq_similarity_sub, S.swap.wOuter_side_squares.2.2,
      Complex.normSq_ofReal, show S.yAttached.b - S.yAttached.c =
        -(S.yAttached.c - S.yAttached.b) by ring, Complex.normSq_neg,
      S.yAttached_side_squares.2.2]
    change S.yScale * S.yScale * S.c ^ 2 = (S.yScale * S.c) ^ 2
    ring

theorem OneTwentyShape.yOuter_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.yOuter.b - S.yOuter.a) = S.c ^ 2 ∧
    Complex.normSq (S.yOuter.c - S.yOuter.a) = ((1 + S.yScale) * S.b) ^ 2 ∧
    Complex.normSq (S.yOuter.c - S.yOuter.b) = (S.yScale * S.c) ^ 2 := by
  rw [S.yOuter_a, S.yOuter_b, S.yOuter_c]
  refine ⟨?_, ?_, ?_⟩
  · rw [show S.reference.b - S.reference.c = -(S.reference.c - S.reference.b) by ring,
      Complex.normSq_neg, S.reference_side_squares.2.2]
  · have href : Complex.normSq S.reference.c = S.b ^ 2 := by
      simpa only [S.reference_a, sub_zero] using S.reference_side_squares.2.1
    rw [show -(S.yScale : ℂ) * S.reference.c - S.reference.c =
      -(((1 + S.yScale : ℝ) : ℂ) * S.reference.c) by push_cast; ring,
      Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal, href]
    ring
  · simpa only [S.yAttached_vertices.2.1, S.yAttached_vertices.2.2, S.reference_b] using
      S.yAttached_side_squares.2.2

theorem OneTwentyShape.yOuter_scaled_side_squares (S : OneTwentyShape) :
    (S.a + S.b) ^ 2 * Complex.normSq (S.yOuter.b - S.yOuter.a) =
      (S.c * (S.a + S.b)) ^ 2 ∧
    (S.a + S.b) ^ 2 * Complex.normSq (S.yOuter.c - S.yOuter.a) =
      (S.b * (2 * S.a + S.b)) ^ 2 ∧
    (S.a + S.b) ^ 2 * Complex.normSq (S.yOuter.c - S.yOuter.b) = (S.a * S.c) ^ 2 := by
  have hsum : (1 + S.yScale) * (S.a + S.b) = 2 * S.a + S.b := by
    nlinarith [S.yScale_mul_sum]
  rw [S.yOuter_side_squares.1, S.yOuter_side_squares.2.1, S.yOuter_side_squares.2.2]
  refine ⟨by ring, ?_, ?_⟩
  · calc
      _ = (S.b * ((1 + S.yScale) * (S.a + S.b))) ^ 2 := by ring
      _ = _ := by rw [hsum]
  · calc
      _ = ((S.yScale * (S.a + S.b)) * S.c) ^ 2 := by ring
      _ = _ := by rw [S.yScale_mul_sum]

end Erdos633
