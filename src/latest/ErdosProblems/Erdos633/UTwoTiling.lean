import ErdosProblems.Erdos633.UTwoGeometry

/-!
# Actual congruent tilings of U₂

The scaled Z component and the reference component have a common tile of
scale `1/[3c²ab(a+b)(a+2b)]`. The count has square class `3(a+b)(a+2b)`.
-/

namespace Erdos633

theorem OneTwentyShape.uTwoTiling_from_Z (S : OneTwentyShape) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 0 < k) (hkδ : (k : ℝ) * (S.uTwoZScale * ε) = 1) {N : ℕ}
    (T : CongruentTiling S.zOuter (S.smallTile ε hε) N) :
    Nonempty (CongruentTiling S.uTwoOuter
      (S.smallTile (S.uTwoZScale * ε) (mul_pos S.uTwoZScale_pos hε)) (k ^ 2 + N)) := by
  let U := T.mapSimilarity 0 (S.uTwoZScale : ℂ)
    (by exact_mod_cast ne_of_gt S.uTwoZScale_pos)
  have htile : (S.smallTile ε hε).mapSimilarity 0 (S.uTwoZScale : ℂ)
      (by exact_mod_cast ne_of_gt S.uTwoZScale_pos) =
        S.smallTile (S.uTwoZScale * ε) (mul_pos S.uTwoZScale_pos hε) := by
    rw [smallTile, Triangle.mapSimilarity_comp]
    simp only [mul_zero, zero_add, smallTile, Complex.ofReal_mul]
  rw [htile] at U
  obtain ⟨e, he⟩ := S.uTwoAttached_congruent_Z
  let TZ := (U.mapIsometry e).of_carrier_eq ((Triangle.mapIsometry_carrier _ e).trans he)
  let V := S.reference.scaleTiling (S.uTwoZScale * ε) 1 (mul_pos S.uTwoZScale_pos hε)
    (by norm_num) k hk hkδ
  have hparent : (S.reference.mapSimilarity 0 ((1 : ℝ) : ℂ) (by norm_num)).carrier =
      S.uTwoReference.carrier := by
    rw [S.uTwoReference_eq, Triangle.swapAC_carrier]
    congr 1
    apply Triangle.ext <;> simp [Triangle.mapSimilarity]
  let TR := V.of_carrier_eq hparent
  exact ⟨S.uTwoOuter.glueSplitTilings S.uTwoSplitRatio S.uTwoSplitRatio_pos
    S.uTwoSplitRatio_lt_one TR TZ⟩

theorem oneTwenty_integer_U_two_tiling (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let S := OneTwentyShape.ofIntegers a b c ha hb hc h
    ∃ (δ : ℝ) (hδ : 0 < δ),
      δ = 1 / (3 * c ^ 2 * a * b * (a + b) * (a + 2 * b) : ℕ) ∧
      Nonempty (CongruentTiling S.uTwoOuter (S.smallTile δ hδ)
        (27 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 3 * (a + 2 * b))) := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  obtain ⟨ε, hε, heps, ⟨T⟩⟩ := oneTwenty_integer_Z_tiling a b c ha hb hc h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have ha0 := ne_of_gt haR
  have hb0 := ne_of_gt hbR
  have hc0 := ne_of_gt hcR
  have hab0 := ne_of_gt (add_pos haR hbR)
  have hab2 : (a : ℝ) + 2 * b ≠ 0 := by positivity
  have hkδ : ((3 * c ^ 2 * a * b * (a + b) * (a + 2 * b) : ℕ) : ℝ) *
      (S.uTwoZScale * ε) = 1 := by
    rw [heps]
    dsimp [S, OneTwentyShape.uTwoZScale, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  have U := S.uTwoTiling_from_Z ε hε (3 * c ^ 2 * a * b * (a + b) * (a + 2 * b))
    (by positivity) hkδ T
  refine ⟨S.uTwoZScale * ε, mul_pos S.uTwoZScale_pos hε, ?_, ?_⟩
  · rw [heps]
    dsimp [S, OneTwentyShape.uTwoZScale, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  · have hcount : (3 * c ^ 2 * a * b * (a + b) * (a + 2 * b)) ^ 2 +
        9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (2 * a + b) * (a + 2 * b) =
          27 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 3 * (a + 2 * b) := by ring
    exact hcount ▸ U

theorem oneTwenty_U_two_count_isSquare_iff (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsSquare (27 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 3 * (a + 2 * b)) ↔
      IsSquare (3 * (a + b) * (a + 2 * b)) := by
  have h := count_isSquare_iff
    (27 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 3 * (a + 2 * b))
    (3 * (c : ℚ) ^ 2 * a * b * (a + b)) ((3 * (a + b) * (a + 2 * b) : ℕ) : ℚ)
    (by positivity) (by push_cast; ring)
  exact h.trans Rat.isSquare_natCast_iff

theorem oneTwenty_integer_U_two_nonsquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers a b c ha hb hc h).uTwoOuter := by
  obtain ⟨δ, hδ, _, T⟩ := oneTwenty_integer_U_two_tiling a b c ha hb hc h
  refine ⟨27 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 3 * (a + 2 * b), _, ?_, T⟩
  exact fun hn => oneTwenty_U_two_numerator_not_isSquare a b c ha hb h
    ((oneTwenty_U_two_count_isSquare_iff a b c ha hb hc).mp hn)

theorem Triangle.admitsNonsquareTiling_of_U_two_sides (P : Triangle) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2 * ((c : ℝ) * (a + 2 * b)) ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * (3 * (b : ℝ) * (a + b)) ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * ((c : ℝ) ^ 2) ^ 2) :
    AdmitsNonsquareTiling P := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  have hsum : 0 < (a : ℝ) + 2 * b := by positivity
  have hT := admitsNonsquareTiling_mapSimilarity
    (oneTwenty_integer_U_two_nonsquare a b c ha hb hc h) 0
    ((q * ((a : ℝ) + 2 * b) : ℝ) : ℂ) (by exact_mod_cast ne_of_gt (mul_pos hq hsum))
  apply admitsNonsquareTiling_of_congruent hT
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + ((q * (S.a + 2 * S.b) : ℝ) : ℂ) * S.uTwoOuter.b) -
      (0 + ((q * (S.a + 2 * S.b) : ℝ) : ℂ) * S.uTwoOuter.a)) = _
    rw [normSq_similarity_sub, Complex.normSq_ofReal, hab]
    change (q * (S.a + 2 * S.b)) * (q * (S.a + 2 * S.b)) *
      Complex.normSq (S.uTwoOuter.b - S.uTwoOuter.a) = q ^ 2 * (S.c * (S.a + 2 * S.b)) ^ 2
    calc
      _ = q ^ 2 * ((S.a + 2 * S.b) ^ 2 *
          Complex.normSq (S.uTwoOuter.b - S.uTwoOuter.a)) := by ring
      _ = _ := by rw [S.uTwoOuter_scaled_side_squares.1]
  · change Complex.normSq ((0 + ((q * (S.a + 2 * S.b) : ℝ) : ℂ) * S.uTwoOuter.c) -
      (0 + ((q * (S.a + 2 * S.b) : ℝ) : ℂ) * S.uTwoOuter.a)) = _
    rw [normSq_similarity_sub, Complex.normSq_ofReal, hac]
    change (q * (S.a + 2 * S.b)) * (q * (S.a + 2 * S.b)) *
      Complex.normSq (S.uTwoOuter.c - S.uTwoOuter.a) = q ^ 2 * (3 * S.b * (S.a + S.b)) ^ 2
    calc
      _ = q ^ 2 * ((S.a + 2 * S.b) ^ 2 *
          Complex.normSq (S.uTwoOuter.c - S.uTwoOuter.a)) := by ring
      _ = _ := by rw [S.uTwoOuter_scaled_side_squares.2.1]
  · change Complex.normSq ((0 + ((q * (S.a + 2 * S.b) : ℝ) : ℂ) * S.uTwoOuter.c) -
      (0 + ((q * (S.a + 2 * S.b) : ℝ) : ℂ) * S.uTwoOuter.b)) = _
    rw [normSq_similarity_sub, Complex.normSq_ofReal, hbc]
    change (q * (S.a + 2 * S.b)) * (q * (S.a + 2 * S.b)) *
      Complex.normSq (S.uTwoOuter.c - S.uTwoOuter.b) = q ^ 2 * (S.c ^ 2) ^ 2
    calc
      _ = q ^ 2 * ((S.a + 2 * S.b) ^ 2 *
          Complex.normSq (S.uTwoOuter.c - S.uTwoOuter.b)) := by ring
      _ = _ := by rw [S.uTwoOuter_scaled_side_squares.2.2]

theorem oneTwenty_U_two_three_five_seven_tiling :
    ∃ R : Triangle, Nonempty (CongruentTiling
      (OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).uTwoOuter R 97084915200) := by
  obtain ⟨δ, hδ, _, T⟩ := oneTwenty_integer_U_two_tiling 3 5 7 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at T
  exact ⟨_, T⟩

theorem oneTwenty_U_two_three_five_seven_nonsquare :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).uTwoOuter := by
  exact oneTwenty_integer_U_two_nonsquare 3 5 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Erdos633
