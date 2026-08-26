import ErdosProblems.Erdos633.EquilateralTrapezoids

/-!
# Equilateral tilings by integer-sided 120-degree triangles

For positive integers satisfying `c²=a²+ab+b²`, the construction uses
`c²` rows in each of three trapezoids. It gives exactly `9c⁴(ab)³` copies
of the reference triangle scaled by `1/(ab)`.
-/

namespace Erdos633

def trapezoidRowWidth (H m : ℕ) (j : Fin m) : ℕ := (2 * m - j.val) * H - m

theorem trapezoidRowWidth_pos (H m : ℕ) (hH : 0 < H) (j : Fin m) :
    0 < trapezoidRowWidth H m j := by
  have hbase : m < 2 * m - j.val := by omega
  have hmul : 2 * m - j.val ≤ (2 * m - j.val) * H :=
    Nat.le_mul_of_pos_right _ hH
  dsimp [trapezoidRowWidth]
  omega

theorem trapezoidRowWidth_balance (H m : ℕ) (hH : 0 < H) (j : Fin m) :
    trapezoidRowWidth H m j + m + j.val * H = 2 * m * H := by
  have hpos := trapezoidRowWidth_pos H m hH j
  have hsub : m ≤ (2 * m - j.val) * H := by
    dsimp [trapezoidRowWidth] at hpos
    omega
  have hj : j.val ≤ 2 * m := by omega
  calc
    trapezoidRowWidth H m j + m + j.val * H = (2 * m - j.val) * H + j.val * H := by
      rw [trapezoidRowWidth, Nat.sub_add_cancel hsub]
    _ = ((2 * m - j.val) + j.val) * H := by ring
    _ = 2 * m * H := by rw [Nat.sub_add_cancel hj]

def oneTwentyRowIndex (a b c : ℕ) (j : Fin (c ^ 2)) : Type :=
  (((Fin ((b * (a * b)) ^ 2) ⊕ Fin ((c * (a * b)) ^ 2)) ⊕
    Fin ((a * (a * b)) ^ 2)) ⊕
      ((Fin (trapezoidRowWidth (a * b) (c ^ 2) j * b) × Fin ((a * b) * a)) × Bool))

instance (a b c : ℕ) (j : Fin (c ^ 2)) : Fintype (oneTwentyRowIndex a b c j) := by
  unfold oneTwentyRowIndex
  infer_instance

theorem oneTwenty_integer_row (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (j : Fin (c ^ 2)) :
    let S := OneTwentyShape.ofIntegers a b c ha hb hc h
    let ε : ℝ := 1 / ((a : ℝ) * b)
    Nonempty (RegionTiling
      (hexCoordinates '' slantedTrapezoid ((a : ℝ) * b)
        ((2 * (c ^ 2 : ℕ) - (j : ℝ)) * ((a : ℝ) * b)))
      (S.smallTile ε (by dsimp [ε]; positivity)) (oneTwentyRowIndex a b c j)) := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  let ε : ℝ := 1 / ((a : ℝ) * b)
  let W := trapezoidRowWidth (a * b) (c ^ 2) j
  have hW : 0 < W := trapezoidRowWidth_pos _ _ (mul_pos ha hb) j
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have ha0 := ne_of_gt haR
  have hb0 := ne_of_gt hbR
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hna : ((a * (a * b) : ℕ) : ℝ) * ε = S.a := by
    dsimp [S, ε, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  have hnb : ((b * (a * b) : ℕ) : ℝ) * ε = S.b := by
    dsimp [S, ε, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  have hnc : ((c * (a * b) : ℕ) : ℝ) * ε = S.c := by
    dsimp [S, ε, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  have hgridm : ((W * b : ℕ) : ℝ) * (ε * S.a) = W := by
    dsimp [S, ε, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  have hgridn : (((a * b) * a : ℕ) : ℝ) * (ε * S.b) = S.a * S.b := by
    dsimp [S, ε, OneTwentyShape.ofIntegers]
    push_cast
    field_simp
  obtain ⟨T⟩ := S.extendedTemplateTiling ε (W : ℝ) hε (by positivity)
    (a * (a * b)) (b * (a * b)) (c * (a * b)) (W * b) ((a * b) * a)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hna hnb hnc hgridm hgridn
  have hwidth : S.c ^ 2 + (W : ℝ) =
      (2 * (c ^ 2 : ℕ) - (j : ℝ)) * ((a : ℝ) * b) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ))
      (trapezoidRowWidth_balance (a * b) (c ^ 2) (mul_pos ha hb) j)
    push_cast at hh
    change (c : ℝ) ^ 2 + (W : ℝ) = _
    dsimp [W]
    push_cast
    nlinarith [hh]
  exact ⟨T.of_region_eq (by rw [hwidth]; rfl)⟩

theorem oneTwenty_row_card_balance (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (j : Fin (c ^ 2)) :
    Fintype.card (oneTwentyRowIndex a b c j) + (a * b) ^ 3 * (2 * j.val + 1) =
      4 * c ^ 2 * (a * b) ^ 3 := by
  have hwidth := trapezoidRowWidth_balance (a * b) (c ^ 2) (mul_pos ha hb) j
  have hwidthZ := congrArg (fun n : ℕ => (n : ℤ)) hwidth
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) h
  apply Nat.cast_injective (R := ℤ)
  simp only [oneTwentyRowIndex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  push_cast at hwidthZ hZ ⊢
  linear_combination 2 * ((a : ℤ) * b) ^ 2 * hwidthZ - ((a : ℤ) * b) ^ 2 * hZ

theorem two_sum_fin_val (m : ℕ) : 2 * (∑ j : Fin m, j.val) + m = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    nlinarith

theorem oneTwenty_rows_card (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Fintype.card (Sigma (oneTwentyRowIndex a b c)) = 3 * (c ^ 2) ^ 2 * (a * b) ^ 3 := by
  rw [Fintype.card_sigma]
  have hsum : (∑ j : Fin (c ^ 2), Fintype.card (oneTwentyRowIndex a b c j)) +
      (a * b) ^ 3 * (2 * (∑ j : Fin (c ^ 2), j.val) + c ^ 2) =
        4 * (c ^ 2) ^ 2 * (a * b) ^ 3 := by
    calc
      _ = ∑ j : Fin (c ^ 2), (Fintype.card (oneTwentyRowIndex a b c j) +
          (a * b) ^ 3 * (2 * j.val + 1)) := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring
      _ = ∑ _j : Fin (c ^ 2), 4 * c ^ 2 * (a * b) ^ 3 := by
        apply Finset.sum_congr rfl
        intro j _
        exact oneTwenty_row_card_balance a b c ha hb h j
      _ = _ := by simp; ring
  rw [two_sum_fin_val] at hsum
  nlinarith

theorem oneTwenty_ideal_trapezoid (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let S := OneTwentyShape.ofIntegers a b c ha hb hc h
    let ε : ℝ := 1 / ((a : ℝ) * b)
    Nonempty (RegionTiling (hexCoordinates '' slantedTrapezoid
      ((c ^ 2 * (a * b) : ℕ) : ℝ) (2 * (c ^ 2 * (a * b) : ℕ)))
      (S.smallTile ε (by dsimp [ε]; positivity)) (Sigma (oneTwentyRowIndex a b c))) := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  let ε : ℝ := 1 / ((a : ℝ) * b)
  have hε : 0 < ε := by dsimp [ε]; positivity
  let T (j : Fin (c ^ 2)) := Classical.choice (oneTwenty_integer_row a b c ha hb hc h j)
  let U := stackSlantedTrapezoidTilings ((a : ℝ) * b) (by positivity)
    (c ^ 2) (by positivity) T
  refine ⟨U.of_region_eq ?_⟩
  push_cast
  congr 2
  ring

/-- An explicit equilateral triangle is tiled by copies of every positive
integer-sided triangle satisfying the 120-degree cosine-law relation. -/
theorem oneTwenty_integer_equilateral_tiling (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let S := OneTwentyShape.ofIntegers a b c ha hb hc h
    let ε : ℝ := 1 / ((a : ℝ) * b)
    Nonempty (CongruentTiling (hexEquilateral (3 * (c ^ 2 * (a * b))) (by positivity))
      (S.smallTile ε (by dsimp [ε]; positivity)) (9 * (c ^ 2) ^ 2 * (a * b) ^ 3)) := by
  obtain ⟨T⟩ := oneTwenty_ideal_trapezoid a b c ha hb hc h
  have U := equilateralTiling_of_trapezoid (c ^ 2 * (a * b)) (by positivity) T
  rw [oneTwenty_rows_card a b c ha hb h] at U
  have hcount : 3 * (3 * (c ^ 2) ^ 2 * (a * b) ^ 3) =
      9 * (c ^ 2) ^ 2 * (a * b) ^ 3 := by ring
  exact ⟨hcount ▸ U⟩

end Erdos633
