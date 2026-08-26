import ErdosProblems.Erdos633.OneTwentyTemplate
import ErdosProblems.Erdos633.VAssembly

/-!
# Extending the 120-degree template by a congruent parallelogram grid

In hexagonal coordinates, the appended parallelogram has `0 ≤ y ≤ H`
and `L ≤ x+y ≤ L+W`. Its cells use exactly the same reference triangle
as the refined three-piece template.
-/

namespace Erdos633

def slantedTrapezoid (H L : ℝ) : Set ℂ :=
  {z | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.im ≤ H ∧ z.re + z.im ≤ L}

def slantedParallelogram (H L W : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ z.im ≤ H ∧ L ≤ z.re + z.im ∧ z.re + z.im ≤ L + W}

theorem TrapezoidFan.append_parallelogram (F : TrapezoidFan) (W : ℝ) (hW : 0 ≤ W) :
    F.region ∪ slantedParallelogram F.H F.L W = slantedTrapezoid F.H (F.L + W) := by
  ext z
  simp only [Set.mem_union, TrapezoidFan.region, slantedTrapezoid,
    slantedParallelogram, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.1, h.2.2.1, by linarith [h.2.2.2]⟩
    · exact ⟨by linarith [h.2.1, h.2.2.1, F.p_pos, F.top_right_pos],
        h.1, h.2.1, h.2.2.2⟩
  · intro h
    by_cases hs : z.re + z.im ≤ F.L
    · exact Or.inl ⟨h.1, h.2.1, h.2.2.1, hs⟩
    · exact Or.inr ⟨h.2.1, h.2.2.1, le_of_lt (lt_of_not_ge hs), h.2.2.2⟩

theorem TrapezoidFan.append_disjoint (F : TrapezoidFan) (W : ℝ) :
    Disjoint (interior F.region) (interior (slantedParallelogram F.H F.L W)) := by
  apply separated_interiors (linearXPlusY 1) (linearXPlusY_surjective _) F.L
  · intro z hz
    simpa only [linearXPlusY_apply, one_mul, Set.mem_ofPred_eq] using hz.2.2.2
  · intro z hz
    simpa only [linearXPlusY_apply, one_mul, Set.mem_ofPred_eq] using hz.2.2.1

def OneTwentyShape.normalizedGrid (S : OneTwentyShape) (ε L : ℝ) (hε : 0 < ε) :
    Triangle where
  a := (L : ℂ)
  b := ((L + ε * S.a : ℝ) : ℂ)
  c := ⟨L - ε * S.b, ε * S.b⟩
  nondegenerate := by
    have h : (L + ε * S.a - L) * (ε * S.b) = ε * S.a * (ε * S.b) := by ring
    simpa only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, sub_self, zero_mul, h] using
      ne_of_gt (mul_pos (mul_pos hε S.a_pos) (mul_pos hε S.b_pos))

theorem OneTwentyShape.normalizedGrid_coordinates (S : OneTwentyShape)
    (ε L : ℝ) (hε : 0 < ε) (z : ℂ) :
    (S.normalizedGrid ε L hε).coordinateEquiv z =
      ⟨L + ε * S.a * z.re - ε * S.b * z.im, ε * S.b * z.im⟩ := by
  apply Complex.ext
  all_goals simp only [Triangle.coordinateEquiv_apply, normalizedGrid,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.smul_re, Complex.smul_im, Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul]
  all_goals ring

theorem OneTwentyShape.normalizedGrid_rectangle (S : OneTwentyShape)
    (ε H L W : ℝ) (hε : 0 < ε) (m n : ℕ)
    (hm : (m : ℝ) * (ε * S.a) = W) (hn : (n : ℝ) * (ε * S.b) = H) :
    (S.normalizedGrid ε L hε).coordinateEquiv '' closedRectangle m n =
      slantedParallelogram H L W := by
  have hεa := mul_pos hε S.a_pos
  have hεb := mul_pos hε S.b_pos
  have hεa0 := ne_of_gt hεa
  have hεb0 := ne_of_gt hεb
  have hε0 := ne_of_gt hε
  have ha0 := ne_of_gt S.a_pos
  have hb0 := ne_of_gt S.b_pos
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [S.normalizedGrid_coordinates]
    change 0 ≤ ε * S.b * w.im ∧ ε * S.b * w.im ≤ H ∧
      L ≤ L + ε * S.a * w.re - ε * S.b * w.im + ε * S.b * w.im ∧
      L + ε * S.a * w.re - ε * S.b * w.im + ε * S.b * w.im ≤ L + W
    refine ⟨mul_nonneg hεb.le hw.2.2.1, ?_, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hw.2.2.2 hεb.le]
    · nlinarith [mul_nonneg hεa.le hw.1]
    · nlinarith [mul_le_mul_of_nonneg_left hw.2.1 hεa.le]
  · intro hz
    refine ⟨⟨(z.re + z.im - L) / (ε * S.a), z.im / (ε * S.b)⟩, ?_, ?_⟩
    · change 0 ≤ (z.re + z.im - L) / (ε * S.a) ∧
        (z.re + z.im - L) / (ε * S.a) ≤ m ∧
        0 ≤ z.im / (ε * S.b) ∧ z.im / (ε * S.b) ≤ n
      refine ⟨div_nonneg (by linarith [hz.2.2.1]) hεa.le, ?_,
        div_nonneg hz.1 hεb.le, ?_⟩
      · apply (div_le_iff₀ hεa).mpr
        linarith [hz.2.2.2]
      · apply (div_le_iff₀ hεb).mpr
        linarith [hz.2.1]
    · rw [S.normalizedGrid_coordinates]
      apply Complex.ext <;> dsimp
      all_goals field_simp
      all_goals ring

theorem OneTwentyShape.grid_congruent (S : OneTwentyShape)
    (ε L : ℝ) (hε : 0 < ε) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' (S.smallTile ε hε).carrier =
      ((S.normalizedGrid ε L hε).mapAffineEquiv hexCoordinates).carrier := by
  apply S.congruent_of_scaled_sides _ ε hε
  · change Complex.normSq (hexCoordinates ((L + ε * S.a : ℝ) : ℂ) -
      hexCoordinates (L : ℂ)) = _
    rw [hexCoordinates_normSq_sub]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  · change Complex.normSq (hexCoordinates ⟨L - ε * S.b, ε * S.b⟩ -
      hexCoordinates (L : ℂ)) = _
    rw [hexCoordinates_normSq_sub]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  · change Complex.normSq (hexCoordinates ⟨L - ε * S.b, ε * S.b⟩ -
      hexCoordinates ((L + ε * S.a : ℝ) : ℂ)) = _
    rw [hexCoordinates_normSq_sub]
    simp only [Complex.ofReal_re, Complex.ofReal_im, S.conic]
    ring

noncomputable def OneTwentyShape.parallelogramTiling (S : OneTwentyShape)
    (ε H L W : ℝ) (hε : 0 < ε) (m n : ℕ) (hm0 : 0 < m) (hn0 : 0 < n)
    (hm : (m : ℝ) * (ε * S.a) = W) (hn : (n : ℝ) * (ε * S.b) = H) :
    RegionTiling (hexCoordinates '' slantedParallelogram H L W) (S.smallTile ε hε)
      ((Fin m × Fin n) × Bool) := by
  let G := S.normalizedGrid ε L hε
  let T := parallelogramGrid (G.coordinateEquiv.trans hexCoordinates) m n hm0 hn0
  have href : standardTriangle.mapAffineEquiv (G.coordinateEquiv.trans hexCoordinates) =
      G.mapAffineEquiv hexCoordinates := by
    rw [← Triangle.mapAffineEquiv_comp, Triangle.standard_map_coordinateEquiv]
  have hregion : (G.coordinateEquiv.trans hexCoordinates) '' closedRectangle m n =
      hexCoordinates '' slantedParallelogram H L W := by
    change (fun z => hexCoordinates (G.coordinateEquiv z)) '' closedRectangle m n = _
    rw [← Set.image_image, S.normalizedGrid_rectangle ε H L W hε m n hm hn]
  let e := Classical.choose (S.grid_congruent ε L hε)
  have he := Classical.choose_spec (S.grid_congruent ε L hε)
  apply (T.of_region_eq hregion).changeTile e
  rw [href]
  exact he

theorem OneTwentyShape.extendedTemplateTiling (S : OneTwentyShape)
    (ε W : ℝ) (hε : 0 < ε) (hW : 0 ≤ W)
    (na nb nc m n : ℕ) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc)
    (hm0 : 0 < m) (hn0 : 0 < n)
    (ha : (na : ℝ) * ε = S.a) (hb : (nb : ℝ) * ε = S.b)
    (hc : (nc : ℝ) * ε = S.c)
    (hm : (m : ℝ) * (ε * S.a) = W) (hn : (n : ℝ) * (ε * S.b) = S.a * S.b) :
    Nonempty (RegionTiling (hexCoordinates '' slantedTrapezoid
      (S.a * S.b) (S.c ^ 2 + W)) (S.smallTile ε hε)
        (((Fin (nb ^ 2) ⊕ Fin (nc ^ 2)) ⊕ Fin (na ^ 2)) ⊕
          ((Fin m × Fin n) × Bool))) := by
  obtain ⟨T⟩ := S.templateTiling ε hε na nb nc hna hnb hnc ha hb hc
  let U := S.parallelogramTiling ε (S.a * S.b) (S.c ^ 2) W hε m n hm0 hn0 hm hn
  have hdis := disjoint_interiors_affine_image hexCoordinates (S.fan.append_disjoint W)
  refine ⟨(T.union U hdis).of_region_eq ?_⟩
  rw [← Set.image_union]
  exact congrArg (fun X : Set ℂ => hexCoordinates '' X) (S.fan.append_parallelogram W hW)

end Erdos633
