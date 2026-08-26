import ErdosProblems.Erdos633.ZGeometry
import ErdosProblems.Erdos633.ZArithmetic

/-!
# Congruent tilings of the Z outer family

The W and Y tilings are rescaled and refined to one common reference tile.
For integer sides their refinement factors are `2a+b` and `c`, respectively.
-/

namespace Erdos633

/-- Rescale an actual tiling and then refine every tile to the requested size. -/
noncomputable def OneTwentyShape.refineScaledTiling (S : OneTwentyShape)
    {P : Triangle} {N : ℕ} (ε q δ : ℝ) (hε : 0 < ε) (hq : 0 < q) (hδ : 0 < δ)
    (n : ℕ) (hn : 0 < n) (hscale : (n : ℝ) * δ = q * ε)
    (T : CongruentTiling P (S.smallTile ε hε) N) :
    CongruentTiling (P.mapSimilarity 0 (q : ℂ) (by exact_mod_cast ne_of_gt hq))
      (S.smallTile δ hδ) (N * n ^ 2) := by
  let U := T.mapSimilarity 0 (q : ℂ) (by exact_mod_cast ne_of_gt hq)
  have htile : (S.smallTile ε hε).mapSimilarity 0 (q : ℂ)
      (by exact_mod_cast ne_of_gt hq) = S.smallTile (q * ε) (mul_pos hq hε) := by
    rw [smallTile, Triangle.mapSimilarity_comp]
    simp only [mul_zero, zero_add, smallTile, Complex.ofReal_mul]
  rw [htile] at U
  exact U.refine (S.reference.scaleTiling δ (q * ε) hδ (mul_pos hq hε) n hn hscale)

theorem OneTwentyShape.zTiling_from_W_Y (S : OneTwentyShape)
    (εw εy δ : ℝ) (hw : 0 < εw) (hy : 0 < εy) (hδ : 0 < δ)
    (nw ny : ℕ) (hnw : 0 < nw) (hny : 0 < ny)
    (hsw : (nw : ℝ) * δ = S.zWScale * εw) (hsy : (ny : ℝ) * δ = S.c * εy)
    {Nw Ny : ℕ} (TW : CongruentTiling S.wOuter (S.smallTile εw hw) Nw)
    (TY : CongruentTiling S.yOuter (S.smallTile εy hy) Ny) :
    Nonempty (CongruentTiling S.zOuter (S.smallTile δ hδ) (Nw * nw ^ 2 + Ny * ny ^ 2)) := by
  let U := S.refineScaledTiling εw S.zWScale δ hw S.zWScale_pos hδ nw hnw hsw TW
  let UW : CongruentTiling S.zW (S.smallTile δ hδ) (Nw * nw ^ 2) := U.of_carrier_eq (by
    rw [S.zW_eq, Triangle.swapBC_carrier])
  let V := S.refineScaledTiling εy S.c δ hy S.c_pos hδ ny hny hsy TY
  obtain ⟨e, he⟩ := S.zY_congruent
  let UY := (V.mapIsometry e).of_carrier_eq ((Triangle.mapIsometry_carrier _ e).trans he)
  exact ⟨S.zOuter.glueSplitTilings S.zSplitRatio S.zSplitRatio_pos
    S.zSplitRatio_lt_one UW UY⟩

theorem oneTwenty_integer_Z_tiling (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let S := OneTwentyShape.ofIntegers a b c ha hb hc h
    ∃ (δ : ℝ) (hδ : 0 < δ), δ = 1 / (3 * c ^ 2 * a * b * (a + b) : ℕ) ∧
      Nonempty (CongruentTiling S.zOuter (S.smallTile δ hδ)
        (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (2 * a + b) * (a + 2 * b))) := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  obtain ⟨εw, hw, hew, ⟨TW⟩⟩ := oneTwenty_integer_W_tiling a b c ha hb hc h
  obtain ⟨εy, hy, hey, ⟨TY⟩⟩ := oneTwenty_integer_Y_tiling a b c ha hb hc h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have ha0 := ne_of_gt haR
  have hb0 := ne_of_gt hbR
  have hc0 := ne_of_gt hcR
  have hab0 := ne_of_gt (add_pos haR hbR)
  have hsw : ((2 * a + b : ℕ) : ℝ) * εy = S.zWScale * εw := by
    rw [hew, hey]
    dsimp [S, OneTwentyShape.zWScale, OneTwentyShape.yScale, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
    ring
  have U := S.zTiling_from_W_Y εw εy εy hw hy hy (2 * a + b) c (by positivity) hc
    hsw rfl TW TY
  refine ⟨εy, hy, hey, ?_⟩
  have hinner : b * (2 * a + b) + c ^ 2 = (a + b) * (a + 2 * b) := by
    rw [h]
    ring
  have hcount : (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 3 * (a + b)) * (2 * a + b) ^ 2 +
      (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) * (2 * a + b)) * c ^ 2 =
        9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (2 * a + b) * (a + 2 * b) := by
    calc
      _ = (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) * (2 * a + b)) *
          (b * (2 * a + b) + c ^ 2) := by ring
      _ = _ := by rw [hinner]; ring
  exact hcount ▸ U

theorem oneTwenty_Z_count_isSquare_iff (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsSquare (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (2 * a + b) * (a + 2 * b)) ↔
      IsSquare ((2 * a + b) * (a + 2 * b)) := by
  have h := count_isSquare_iff
    (9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (2 * a + b) * (a + 2 * b))
    (3 * (c : ℚ) ^ 2 * a * b * (a + b)) (((2 * a + b) * (a + 2 * b) : ℕ) : ℚ)
    (by positivity) (by push_cast; ring)
  exact h.trans Rat.isSquare_natCast_iff

theorem oneTwenty_integer_Z_nonsquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hns : ¬ IsSquare ((2 * a + b) * (a + 2 * b))) :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers a b c ha hb hc h).zOuter := by
  obtain ⟨δ, hδ, _, T⟩ := oneTwenty_integer_Z_tiling a b c ha hb hc h
  refine ⟨9 * (c ^ 2) ^ 2 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (2 * a + b) * (a + 2 * b),
    _, ?_, T⟩
  exact fun hn => hns ((oneTwenty_Z_count_isSquare_iff a b c ha hb hc).mp hn)

/-- Every integer parameter triple for Z gives a nonsquare tiling. -/
theorem oneTwenty_integer_Z_always_nonsquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers a b c ha hb hc h).zOuter :=
  oneTwenty_integer_Z_nonsquare a b c ha hb hc h
    (oneTwenty_Z_numerator_not_isSquare a b c ha hb h)

theorem Triangle.admitsNonsquareTiling_of_Z_sides (P : Triangle) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hns : ¬ IsSquare ((2 * a + b) * (a + 2 * b)))
    (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2 * ((b : ℝ) * (2 * a + b)) ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * ((a : ℝ) * (a + 2 * b)) ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * ((c : ℝ) ^ 2) ^ 2) :
    AdmitsNonsquareTiling P := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  have hT := admitsNonsquareTiling_mapSimilarity
    (oneTwenty_integer_Z_nonsquare a b c ha hb hc h hns) 0 (q : ℂ)
    (by exact_mod_cast ne_of_gt hq)
  apply admitsNonsquareTiling_of_congruent hT
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (q : ℂ) * S.zOuter.b) -
      (0 + (q : ℂ) * S.zOuter.a)) = _
    rw [normSq_similarity_sub, S.zOuter_side_squares.1, Complex.normSq_ofReal, hab]
    change q * q * ((b : ℝ) * (2 * a + b)) ^ 2 = q ^ 2 * ((b : ℝ) * (2 * a + b)) ^ 2
    ring
  · change Complex.normSq ((0 + (q : ℂ) * S.zOuter.c) -
      (0 + (q : ℂ) * S.zOuter.a)) = _
    rw [normSq_similarity_sub, S.zOuter_side_squares.2.1, Complex.normSq_ofReal, hac]
    change q * q * ((a : ℝ) * (a + 2 * b)) ^ 2 = q ^ 2 * ((a : ℝ) * (a + 2 * b)) ^ 2
    ring
  · change Complex.normSq ((0 + (q : ℂ) * S.zOuter.c) -
      (0 + (q : ℂ) * S.zOuter.b)) = _
    rw [normSq_similarity_sub, S.zOuter_side_squares.2.2, Complex.normSq_ofReal, hbc]
    change q * q * ((c : ℝ) ^ 2) ^ 2 = q ^ 2 * ((c : ℝ) ^ 2) ^ 2
    ring

/-- No additional square hypothesis is needed in the Z side criterion. -/
theorem Triangle.admitsNonsquareTiling_of_Z_integer_sides (P : Triangle) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2 * ((b : ℝ) * (2 * a + b)) ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * ((a : ℝ) * (a + 2 * b)) ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * ((c : ℝ) ^ 2) ^ 2) :
    AdmitsNonsquareTiling P :=
  P.admitsNonsquareTiling_of_Z_sides a b c ha hb hc h
    (oneTwenty_Z_numerator_not_isSquare a b c ha hb h) q hq hab hac hbc

theorem oneTwenty_Z_three_five_seven_tiling :
    ∃ R : Triangle, Nonempty (CongruentTiling
      (OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).zOuter R 44497252800) := by
  obtain ⟨δ, hδ, _, T⟩ := oneTwenty_integer_Z_tiling 3 5 7 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at T
  exact ⟨_, T⟩

theorem oneTwenty_Z_three_five_seven_nonsquare :
    AdmitsNonsquareTiling (OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).zOuter := by
  apply oneTwenty_integer_Z_nonsquare 3 5 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rintro ⟨k, hk⟩
  have hcases : k ≤ 11 ∨ 12 ≤ k := by omega
  rcases hcases with hsmall | hlarge <;> nlinarith

end Erdos633
