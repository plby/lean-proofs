import ErdosProblems.Erdos633.WGeometry
import ErdosProblems.Erdos633.WArithmetic

/-!
# Congruent tilings of the W outer family

The equilateral component is rescaled and the attached reference triangle is
subdivided to exactly the same tile size. For integer sides `a,b,c`, the count
is `9c⁴a²b³(a+b)`, with square class `b(a+b)`.
-/

namespace Erdos633

theorem OneTwentyShape.wEquilateral_congruent_scaled_hex (S : OneTwentyShape)
    (n : ℕ) (hn : 0 < n) (q : ℝ) (hq : 0 < q) (hnq : (n : ℝ) * q = S.a) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' ((hexEquilateral n hn).mapSimilarity 0 (q : ℂ)
        (by exact_mod_cast ne_of_gt hq)).carrier = S.wEquilateral.carrier := by
  have hsq : q ^ 2 * (n : ℝ) ^ 2 = S.a ^ 2 := by
    rw [← hnq]
    ring
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (q : ℂ) * (hexEquilateral n hn).b) -
      (0 + (q : ℂ) * (hexEquilateral n hn).a)) = _
    rw [normSq_similarity_sub, (hexEquilateral_side_squares n hn).1,
      Complex.normSq_ofReal, S.wEquilateral_side_squares.1]
    nlinarith [hsq]
  · change Complex.normSq ((0 + (q : ℂ) * (hexEquilateral n hn).c) -
      (0 + (q : ℂ) * (hexEquilateral n hn).a)) = _
    rw [normSq_similarity_sub, (hexEquilateral_side_squares n hn).2.1,
      Complex.normSq_ofReal, S.wEquilateral_side_squares.2.1]
    nlinarith [hsq]
  · change Complex.normSq ((0 + (q : ℂ) * (hexEquilateral n hn).c) -
      (0 + (q : ℂ) * (hexEquilateral n hn).b)) = _
    rw [normSq_similarity_sub, (hexEquilateral_side_squares n hn).2.2,
      Complex.normSq_ofReal, S.wEquilateral_side_squares.2.2]
    nlinarith [hsq]

theorem OneTwentyShape.wTiling_from_equilateral (S : OneTwentyShape)
    (n : ℕ) (hn : 0 < n) (ε q : ℝ) (hε : 0 < ε) (hq : 0 < q)
    (hnq : (n : ℝ) * q = S.a) (k : ℕ) (hk : 0 < k)
    (hkδ : (k : ℝ) * (q * ε) = 1) {N : ℕ}
    (T : CongruentTiling (hexEquilateral n hn) (S.smallTile ε hε) N) :
    Nonempty (CongruentTiling S.wOuter (S.smallTile (q * ε) (mul_pos hq hε)) (N + k ^ 2)) := by
  let U := T.mapSimilarity 0 (q : ℂ) (by exact_mod_cast ne_of_gt hq)
  have htile : (S.smallTile ε hε).mapSimilarity 0 (q : ℂ)
      (by exact_mod_cast ne_of_gt hq) = S.smallTile (q * ε) (mul_pos hq hε) := by
    rw [smallTile, Triangle.mapSimilarity_comp]
    simp only [mul_zero, zero_add]
    simp only [smallTile, Complex.ofReal_mul]
  rw [htile] at U
  obtain ⟨ee, hee⟩ := S.wEquilateral_congruent_scaled_hex n hn q hq hnq
  let TE := (U.mapIsometry ee).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ ee).trans hee)
  let V := S.reference.scaleTiling (q * ε) 1 (mul_pos hq hε) (by norm_num) k hk hkδ
  have hone : S.reference.mapSimilarity 0 ((1 : ℝ) : ℂ) (by norm_num) = S.reference := by
    apply Triangle.ext <;> simp [Triangle.mapSimilarity]
  obtain ⟨er, her⟩ := S.wAttached_congruent
  let TR : CongruentTiling S.wAttached (S.smallTile (q * ε) (mul_pos hq hε)) (k ^ 2) :=
    (V.mapIsometry er).of_carrier_eq (by
    rw [Triangle.mapIsometry_carrier, hone]
    exact her)
  exact ⟨S.wOuter.glueSplitTilings S.wSplitRatio S.wSplitRatio_pos
    S.wSplitRatio_lt_one TE TR⟩

theorem oneTwenty_integer_W_tiling (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let S := OneTwentyShape.ofIntegers a b c ha hb hc h
    ∃ (δ : ℝ) (hδ : 0 < δ), δ = 1 / (3 * c ^ 2 * a * b ^ 2 : ℕ) ∧
      Nonempty (CongruentTiling S.wOuter (S.smallTile δ hδ)
        (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 3 * (a + b))) := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  let ε : ℝ := 1 / ((a : ℝ) * b)
  let q : ℝ := 1 / (3 * (c : ℝ) ^ 2 * b)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have ha0 := ne_of_gt haR
  have hb0 := ne_of_gt hbR
  have hc0 := ne_of_gt hcR
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hnq : ((3 * (c ^ 2 * (a * b)) : ℕ) : ℝ) * q = S.a := by
    dsimp [q, S, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  have hkδ : ((3 * c ^ 2 * a * b ^ 2 : ℕ) : ℝ) * (q * ε) = 1 := by
    dsimp [q, ε]
    push_cast
    field_simp
  obtain ⟨T⟩ := oneTwenty_integer_equilateral_tiling a b c ha hb hc h
  have U := S.wTiling_from_equilateral (3 * (c ^ 2 * (a * b))) (by positivity)
    ε q hε hq hnq (3 * c ^ 2 * a * b ^ 2) (by positivity) hkδ T
  refine ⟨q * ε, mul_pos hq hε, ?_, ?_⟩
  · dsimp [q, ε]
    push_cast
    field_simp
  · have hcount : 9 * (c ^ 2) ^ 2 * (a * b) ^ 3 + (3 * c ^ 2 * a * b ^ 2) ^ 2 =
        9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 3 * (a + b) := by ring
    exact hcount ▸ U

theorem oneTwenty_W_count_isSquare_iff (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsSquare (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 3 * (a + b)) ↔ IsSquare (b * (a + b)) := by
  have h := count_isSquare_iff (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 3 * (a + b))
    (3 * (c : ℚ) ^ 2 * a * b) ((b * (a + b) : ℕ) : ℚ)
    (by positivity) (by push_cast; ring)
  exact h.trans Rat.isSquare_natCast_iff

theorem oneTwenty_integer_W_nonsquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hns : ¬ IsSquare (b * (a + b))) :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers a b c ha hb hc h).wOuter := by
  obtain ⟨δ, hδ, _, T⟩ := oneTwenty_integer_W_tiling a b c ha hb hc h
  refine ⟨9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 3 * (a + b), _, ?_, T⟩
  exact fun hn => hns ((oneTwenty_W_count_isSquare_iff a b c ha hb hc).mp hn)

/-- Every positive integer 120-degree parameter triple yields a nonsquare W tiling. -/
theorem oneTwenty_integer_W_always_nonsquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers a b c ha hb hc h).wOuter :=
  oneTwenty_integer_W_nonsquare a b c ha hb hc h
    (oneTwenty_W_numerator_not_isSquare a b c ha hb h)

/-- A side criterion for every position, orientation, and positive scale of W. -/
theorem Triangle.admitsNonsquareTiling_of_W_sides (P : Triangle) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hns : ¬ IsSquare (b * (a + b)))
    (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2 * (a : ℝ) ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * ((a : ℝ) + b) ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * (c : ℝ) ^ 2) :
    AdmitsNonsquareTiling P := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  have hT := admitsNonsquareTiling_mapSimilarity
    (oneTwenty_integer_W_nonsquare a b c ha hb hc h hns) 0 (q : ℂ)
    (by exact_mod_cast ne_of_gt hq)
  apply admitsNonsquareTiling_of_congruent hT
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (q : ℂ) * S.wOuter.b) -
      (0 + (q : ℂ) * S.wOuter.a)) = _
    rw [normSq_similarity_sub, S.wOuter_side_squares.1, Complex.normSq_ofReal, hab]
    change q * q * (a : ℝ) ^ 2 = q ^ 2 * (a : ℝ) ^ 2
    ring
  · change Complex.normSq ((0 + (q : ℂ) * S.wOuter.c) -
      (0 + (q : ℂ) * S.wOuter.a)) = _
    rw [normSq_similarity_sub, S.wOuter_side_squares.2.1, Complex.normSq_ofReal, hac]
    change q * q * ((a : ℝ) + b) ^ 2 = q ^ 2 * ((a : ℝ) + b) ^ 2
    ring
  · change Complex.normSq ((0 + (q : ℂ) * S.wOuter.c) -
      (0 + (q : ℂ) * S.wOuter.b)) = _
    rw [normSq_similarity_sub, S.wOuter_side_squares.2.2, Complex.normSq_ofReal, hbc]
    change q * q * (c : ℝ) ^ 2 = q ^ 2 * (c : ℝ) ^ 2
    ring

/-- The W side criterion requires no additional nonsquareness hypothesis. -/
theorem Triangle.admitsNonsquareTiling_of_W_integer_sides (P : Triangle) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2 * (a : ℝ) ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * ((a : ℝ) + b) ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * (c : ℝ) ^ 2) :
    AdmitsNonsquareTiling P :=
  P.admitsNonsquareTiling_of_W_sides a b c ha hb hc h
    (oneTwenty_W_numerator_not_isSquare a b c ha hb h) q hq hab hac hbc

theorem oneTwenty_W_three_five_seven_tiling :
    ∃ R : Triangle, Nonempty (CongruentTiling
      (OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).wOuter R 194481000) := by
  obtain ⟨δ, hδ, _, T⟩ := oneTwenty_integer_W_tiling 3 5 7 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at T
  exact ⟨_, T⟩

/-- The W triangle with sides `3,8,7` has an actual nonsquare congruent tiling. -/
theorem oneTwenty_W_three_five_seven_nonsquare :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).wOuter := by
  exact oneTwenty_integer_W_always_nonsquare 3 5 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Erdos633
