import ErdosProblems.Erdos633.YGeometry
import ErdosProblems.Erdos633.YCubicArithmetic

/-!
# Congruent tilings of the Y outer family

The reference component and the rescaled, reflected W component use one
common congruent tile. Their tile counts add; no area equation is substituted
for the geometric construction.
-/

namespace Erdos633

theorem OneTwentyShape.yTiling_from_W (S : OneTwentyShape) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 0 < k) (hkδ : (k : ℝ) * (S.yScale * ε) = 1) {N : ℕ}
    (T : CongruentTiling S.swap.wOuter (S.swap.smallTile ε hε) N) :
    Nonempty (CongruentTiling S.yOuter
      (S.smallTile (S.yScale * ε) (mul_pos S.yScale_pos hε)) (k ^ 2 + N)) := by
  let U := T.mapSimilarity 0 (S.yScale : ℂ) (by exact_mod_cast ne_of_gt S.yScale_pos)
  have htile : (S.swap.smallTile ε hε).mapSimilarity 0 (S.yScale : ℂ)
      (by exact_mod_cast ne_of_gt S.yScale_pos) =
        S.swap.smallTile (S.yScale * ε) (mul_pos S.yScale_pos hε) := by
    rw [smallTile, Triangle.mapSimilarity_comp]
    simp only [mul_zero, zero_add, smallTile, Complex.ofReal_mul]
  rw [htile] at U
  obtain ⟨et, het⟩ := S.smallTile_swap_congruent (S.yScale * ε) (mul_pos S.yScale_pos hε)
  let U' := U.changeTile et het
  obtain ⟨ew, hew⟩ := S.yAttached_congruent_W
  let TW := (U'.mapIsometry ew).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ ew).trans hew)
  let V := S.reference.scaleTiling (S.yScale * ε) 1 (mul_pos S.yScale_pos hε)
    (by norm_num) k hk hkδ
  have hparent : (S.reference.mapSimilarity 0 ((1 : ℝ) : ℂ) (by norm_num)).carrier =
      S.yReference.carrier := by
    rw [S.yReference_eq, Triangle.swapAC_carrier]
    congr 1
    apply Triangle.ext <;> simp [Triangle.mapSimilarity]
  let TR := V.of_carrier_eq hparent
  exact ⟨S.yOuter.glueSplitTilings S.ySplitRatio S.ySplitRatio_pos
    S.ySplitRatio_lt_one TR TW⟩

theorem oneTwenty_integer_Y_tiling (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let S := OneTwentyShape.ofIntegers a b c ha hb hc h
    ∃ (δ : ℝ) (hδ : 0 < δ), δ = 1 / (3 * c ^ 2 * a * b * (a + b) : ℕ) ∧
      Nonempty (CongruentTiling S.yOuter (S.smallTile δ hδ)
        (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) * (2 * a + b))) := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  have hswap : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by rw [h]; ring
  obtain ⟨ε, hε, heps, ⟨T⟩⟩ := oneTwenty_integer_W_tiling b a c hb ha hc hswap
  change CongruentTiling S.swap.wOuter (S.swap.smallTile ε hε)
    (9 * (c ^ 2) ^ 2 * b ^ 2 * a ^ 3 * (b + a)) at T
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have ha0 := ne_of_gt haR
  have hb0 := ne_of_gt hbR
  have hc0 := ne_of_gt hcR
  have hab0 := ne_of_gt (add_pos haR hbR)
  have hkδ : ((3 * c ^ 2 * a * b * (a + b) : ℕ) : ℝ) * (S.yScale * ε) = 1 := by
    rw [heps]
    dsimp [S, OneTwentyShape.yScale, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  have U := S.yTiling_from_W ε hε (3 * c ^ 2 * a * b * (a + b))
    (by positivity) hkδ T
  refine ⟨S.yScale * ε, mul_pos S.yScale_pos hε, ?_, ?_⟩
  · rw [heps]
    dsimp [S, OneTwentyShape.yScale, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  · have hcount : (3 * c ^ 2 * a * b * (a + b)) ^ 2 +
        9 * (c ^ 2) ^ 2 * b ^ 2 * a ^ 3 * (b + a) =
          9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) * (2 * a + b) := by ring
    exact hcount ▸ U

theorem oneTwenty_Y_count_isSquare_iff (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsSquare (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) * (2 * a + b)) ↔
      IsSquare ((a + b) * (2 * a + b)) := by
  have h := count_isSquare_iff
    (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) * (2 * a + b))
    (3 * (c : ℚ) ^ 2 * a * b) (((a + b) * (2 * a + b) : ℕ) : ℚ)
    (by positivity) (by push_cast; ring)
  exact h.trans Rat.isSquare_natCast_iff

theorem oneTwenty_integer_Y_nonsquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers a b c ha hb hc h).yOuter := by
  obtain ⟨δ, hδ, _, T⟩ := oneTwenty_integer_Y_tiling a b c ha hb hc h
  refine ⟨9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) * (2 * a + b), _, ?_, T⟩
  exact fun hn => oneTwenty_Y_numerator_not_isSquare a b c ha hb h
    ((oneTwenty_Y_count_isSquare_iff a b c ha hb hc).mp hn)

/-- The Y sufficient criterion in integer side ratios, at arbitrary position,
orientation, and positive scale. -/
theorem Triangle.admitsNonsquareTiling_of_Y_sides (P : Triangle) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2 * ((c : ℝ) * (a + b)) ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * ((b : ℝ) * (2 * a + b)) ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * ((a : ℝ) * c) ^ 2) :
    AdmitsNonsquareTiling P := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  have hsum : 0 < (a : ℝ) + b := by positivity
  have hT := admitsNonsquareTiling_mapSimilarity
    (oneTwenty_integer_Y_nonsquare a b c ha hb hc h) 0
    ((q * ((a : ℝ) + b) : ℝ) : ℂ) (by exact_mod_cast ne_of_gt (mul_pos hq hsum))
  apply admitsNonsquareTiling_of_congruent hT
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + ((q * (S.a + S.b) : ℝ) : ℂ) * S.yOuter.b) -
      (0 + ((q * (S.a + S.b) : ℝ) : ℂ) * S.yOuter.a)) = _
    rw [normSq_similarity_sub, Complex.normSq_ofReal, hab]
    change (q * (S.a + S.b)) * (q * (S.a + S.b)) *
      Complex.normSq (S.yOuter.b - S.yOuter.a) = q ^ 2 * (S.c * (S.a + S.b)) ^ 2
    calc
      _ = q ^ 2 * ((S.a + S.b) ^ 2 * Complex.normSq (S.yOuter.b - S.yOuter.a)) := by ring
      _ = _ := by rw [S.yOuter_scaled_side_squares.1]
  · change Complex.normSq ((0 + ((q * (S.a + S.b) : ℝ) : ℂ) * S.yOuter.c) -
      (0 + ((q * (S.a + S.b) : ℝ) : ℂ) * S.yOuter.a)) = _
    rw [normSq_similarity_sub, Complex.normSq_ofReal, hac]
    change (q * (S.a + S.b)) * (q * (S.a + S.b)) *
      Complex.normSq (S.yOuter.c - S.yOuter.a) = q ^ 2 * (S.b * (2 * S.a + S.b)) ^ 2
    calc
      _ = q ^ 2 * ((S.a + S.b) ^ 2 * Complex.normSq (S.yOuter.c - S.yOuter.a)) := by ring
      _ = _ := by rw [S.yOuter_scaled_side_squares.2.1]
  · change Complex.normSq ((0 + ((q * (S.a + S.b) : ℝ) : ℂ) * S.yOuter.c) -
      (0 + ((q * (S.a + S.b) : ℝ) : ℂ) * S.yOuter.b)) = _
    rw [normSq_similarity_sub, Complex.normSq_ofReal, hbc]
    change (q * (S.a + S.b)) * (q * (S.a + S.b)) *
      Complex.normSq (S.yOuter.c - S.yOuter.b) = q ^ 2 * (S.a * S.c) ^ 2
    calc
      _ = q ^ 2 * ((S.a + S.b) ^ 2 * Complex.normSq (S.yOuter.c - S.yOuter.b)) := by ring
      _ = _ := by rw [S.yOuter_scaled_side_squares.2.2]

theorem oneTwenty_Y_three_five_seven_tiling :
    ∃ R : Triangle, Nonempty (CongruentTiling
      (OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).yOuter R 427858200) := by
  obtain ⟨δ, hδ, _, T⟩ := oneTwenty_integer_Y_tiling 3 5 7 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at T
  exact ⟨_, T⟩

theorem oneTwenty_Y_three_five_seven_nonsquare :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).yOuter := by
  exact oneTwenty_integer_Y_nonsquare 3 5 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Erdos633
