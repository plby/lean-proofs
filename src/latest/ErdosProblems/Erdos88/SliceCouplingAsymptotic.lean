import ErdosProblems.Erdos88.SliceCoupling

open scoped BigOperators

namespace Erdos88.BooleanSlices

lemma eventually_const_le_scale (C p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop, C ≤ scale n p := by
  exact ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop C)

lemma eventually_const_mul_log_le_scale (C p : ℝ)
    (hC : 0 ≤ C) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * Real.log n ≤ scale n p := by
  let q := p / 2
  have hq : 0 < q := div_pos hp (by norm_num)
  have hgrow := eventually_const_le_scale (C / q) q hq
  filter_upwards [Filter.eventually_ge_atTop 1, hgrow] with n hn hnGrow
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog := Real.log_natCast_le_rpow_div n hq
  have hscaleQ : scale n q = (n : ℝ) ^ q := rfl
  rw [← hscaleQ] at hlog
  calc
    C * Real.log n ≤ C * (scale n q / q) :=
      mul_le_mul_of_nonneg_left hlog hC
    _ = (C / q) * scale n q := by ring
    _ ≤ scale n q * scale n q :=
      mul_le_mul_of_nonneg_right hnGrow (scale_nonneg n q)
    _ = scale n p := by
      rw [scale_mul (show 0 < n by omega)]
      congr 1
      dsimp only [q]
      ring

lemma eventually_const_mul_log_sq_le_scale (C p : ℝ)
    (hC : 0 ≤ C) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * Real.log n ^ 2 ≤ scale n p := by
  let D := max 1 C
  have hD0 : 0 ≤ D := le_trans zero_le_one (le_max_left _ _)
  have hCD : C ≤ D := le_max_right _ _
  have hlog := eventually_const_mul_log_le_scale D (p / 2) hD0
    (div_pos hp (by norm_num))
  filter_upwards [Filter.eventually_ge_atTop 1, hlog] with n hn hnLog
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hClog : C * Real.log n ≤ scale n (p / 2) :=
    (mul_le_mul_of_nonneg_right hCD hlog0).trans hnLog
  have hlogD : Real.log n ≤ scale n (p / 2) := by
    calc
      Real.log n ≤ D * Real.log n := by
        nlinarith [le_max_left (1 : ℝ) C]
      _ ≤ scale n (p / 2) := hnLog
  calc
    C * Real.log n ^ 2 = (C * Real.log n) * Real.log n := by ring
    _ ≤ scale n (p / 2) * scale n (p / 2) :=
      mul_le_mul hClog hlogD hlog0 (scale_nonneg n _)
    _ = scale n p := by
      rw [scale_mul (show 0 < n by omega)]
      congr 1
      ring

lemma bucketCount_mul_fiberCard {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (heq : ∀ k h, (P.fiber k).card = (P.fiber h).card)
    (k : Fin m) : m * (P.fiber k).card = n := by
  calc
    m * (P.fiber k).card = ∑ _h : Fin m, (P.fiber k).card := by simp
    _ = ∑ h : Fin m, (P.fiber h).card := by
      apply Finset.sum_congr rfl
      intro h hh
      exact (heq h k).symm
    _ = n := sum_card_bucketPartition_fiber P

lemma scale_one_sub_mul_scale {n : ℕ} (hn : 0 < n) (d : ℝ) :
    scale n d * scale n (1 - d) = (n : ℝ) := by
  rw [scale_mul hn]
  convert Real.rpow_one (n : ℝ) using 1 <;> simp [scale] <;> ring

lemma scale_mul_three {n : ℕ} (hn : 0 < n) (a b c : ℝ) :
    scale n a * scale n b * scale n c = scale n (a + b + c) := by
  rw [scale_mul hn, scale_mul hn]

lemma ksss_fiberCard_lower {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (d : ℝ)
    (hn : 0 < n) (hm : (m : ℝ) ≤ 2 * scale n d)
    (heq : ∀ k h, (P.fiber k).card = (P.fiber h).card)
    (k : Fin m) :
    scale n (1 - d) / 2 ≤ ((P.fiber k).card : ℝ) := by
  have hcard := bucketCount_mul_fiberCard P heq k
  have hcardR : (m : ℝ) * (P.fiber k).card = n := by exact_mod_cast hcard
  have hscale := scale_one_sub_mul_scale hn d
  have hA : 0 < scale n d := scale_pos hn d
  have hs : 0 ≤ ((P.fiber k).card : ℝ) := by positivity
  nlinarith

lemma nat_sub_two_floor_le_margin (s : ℕ) (W : ℝ)
    (hW0 : 0 ≤ W) (hW : W ≤ (s : ℝ) / 2) :
    ((s - 2 * Nat.floor ((s : ℝ) / 2 - W) : ℕ) : ℝ) ≤
      2 * W + 2 := by
  let x : ℝ := (s : ℝ) / 2 - W
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hcUpper : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  have hcNat : 2 * Nat.floor x ≤ s := by
    exact_mod_cast (show (2 : ℝ) * Nat.floor x ≤ s by
      dsimp only [x] at hcUpper
      nlinarith)
  have hcLower : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  rw [Nat.cast_sub hcNat, Nat.cast_mul, Nat.cast_ofNat]
  dsimp only [x] at hcLower
  linarith

lemma two_mul_floor_half_sub_le (s : ℕ) (W : ℝ)
    (hW0 : 0 ≤ W) (hW : W ≤ (s : ℝ) / 2) :
    2 * Nat.floor ((s : ℝ) / 2 - W) ≤ s := by
  let x : ℝ := (s : ℝ) / 2 - W
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hcUpper : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  exact_mod_cast (show (2 : ℝ) * Nat.floor x ≤ s by
    dsimp only [x] at hcUpper
    nlinarith)

lemma nat_sub_two_floor_pos_of_margin_pos (s : ℕ) (W : ℝ)
    (hW0 : 0 ≤ W) (hWpos : 0 < W) (hW : W ≤ (s : ℝ) / 2) :
    0 < s - 2 * Nat.floor ((s : ℝ) / 2 - W) := by
  let x : ℝ := (s : ℝ) / 2 - W
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hcUpper : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  have hcLt : 2 * Nat.floor x < s := by
    exact_mod_cast (show (2 : ℝ) * Nat.floor x < s by
      dsimp only [x] at hcUpper
      nlinarith)
  dsimp only [x] at hcLt ⊢
  omega

lemma nat_floor_half_sub_pos (s : ℕ) (W : ℝ)
    (hfit : W + 1 ≤ (s : ℝ) / 2) :
    0 < Nat.floor ((s : ℝ) / 2 - W) := by
  have hx : (1 : ℝ) ≤ (s : ℝ) / 2 - W := by linarith
  have : (1 : ℕ) ≤ Nat.floor ((s : ℝ) / 2 - W) := by
    apply Nat.le_floor
    norm_num
    exact hx
  omega

lemma eventually_linear_le_exp_scale (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (4 : ℝ) * n + 6 ≤ Real.exp (scale n p) := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ scale n p)
      Filter.atTop Filter.atTop := by
    exact (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have hpolyReal :=
    (isLittleO_rpow_exp_atTop (1 / p)).bound
      (by norm_num : (0 : ℝ) < 1 / 10)
  have hpoly := ht.eventually hpolyReal
  have hexp := (Real.tendsto_exp_atTop.comp ht).eventually
    (Filter.eventually_ge_atTop 10)
  filter_upwards [Filter.eventually_ge_atTop 1, hpoly, hexp] with n hn hpn hen
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (scale_nonneg n p) _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hpn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpne : p ≠ 0 := ne_of_gt hp
  have hpow : scale n p ^ (1 / p) = (n : ℝ) := by
    calc
      scale n p ^ (1 / p) = (n : ℝ) ^ (p * (1 / p)) := by
        exact (Real.rpow_mul hnR.le p (1 / p)).symm
      _ = (n : ℝ) := by
        rw [show p * (1 / p) = 1 by field_simp]
        exact Real.rpow_one _
  rw [hpow] at hpn
  change 10 ≤ Real.exp (scale n p) at hen
  nlinarith

lemma weighted_three_exp_le_exp_neg
    {x A B C N : ℝ}
    (hN0 : 0 ≤ N)
    (hA : 2 * x ≤ A) (hB : 2 * x ≤ B) (hC : 2 * x ≤ C)
    (hN : 4 * N + 6 ≤ Real.exp x) :
    4 * Real.exp (-A) +
        (N * (4 * Real.exp (-B)) + 2 * Real.exp (-C)) ≤
      Real.exp (-x) := by
  have heA : Real.exp (-A) ≤ Real.exp (-2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have heB : Real.exp (-B) ≤ Real.exp (-2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have heC : Real.exp (-C) ≤ Real.exp (-2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    4 * Real.exp (-A) +
        (N * (4 * Real.exp (-B)) + 2 * Real.exp (-C)) ≤
        (4 * N + 6) * Real.exp (-2 * x) := by
      nlinarith [Real.exp_pos (-2 * x),
        mul_le_mul_of_nonneg_left heB hN0]
    _ ≤ Real.exp x * Real.exp (-2 * x) :=
      mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
    _ = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma ksss_threshold_probability_bound {n : ℕ} (d R L H : ℝ)
    (hn : 0 < n) (hR0 : 0 < R) (hL0 : 0 < L) (hH0 : 0 < H)
    (hR : R ≤ scale n (1 / 2 + d)) (hL : L ≤ (n : ℝ))
    (hH : H ≤ 12 * scale n (1 / 2 + 3 * d))
    (hxE : 36864 ≤ scale n (d / 2))
    (hxC : 4096 ≤ scale n (11 * d / 2))
    (hpref : (4 : ℝ) * n + 6 ≤ Real.exp (scale n (d / 2))) :
    4 * Real.exp
        (-(scale n (3 / 4 + 4 * d) / 8) ^ 2 / (2 * R * H ^ 2)) +
      ((n : ℝ) * (4 * Real.exp (-scale n (1 / 4 + d) ^ 2 /
        (2 * R * 8 ^ 2))) +
      2 * Real.exp (-(scale n (3 / 4 + 4 * d) / 4) ^ 2 /
        (2 * L * (8 * scale n (1 / 4 + d)) ^ 2))) ≤
      Real.exp (-scale n (d / 2)) := by
  let x := scale n (d / 2)
  let A := scale n (1 / 2 + d)
  let B := scale n (1 / 2 + 3 * d)
  let S := scale n (1 / 4 + d)
  let T := scale n (3 / 4 + 4 * d)
  have hx0 : 0 < x := scale_pos hn _
  have hA0 : 0 < A := scale_pos hn _
  have hB0 : 0 < B := scale_pos hn _
  have hS0 : 0 < S := scale_pos hn _
  have hT0 : 0 < T := scale_pos hn _
  have hT2 : T ^ 2 = A * B ^ 2 * x ^ 2 := by
    dsimp only [T, A, B, x]
    rw [scale_sq hn.le, scale_sq hn.le, scale_sq hn.le]
    symm
    rw [scale_mul_three hn]
    congr 1
    ring
  have hS2 : S ^ 2 = A * x ^ 2 := by
    dsimp only [S, A, x]
    rw [scale_sq hn.le, scale_sq hn.le, scale_mul hn]
    congr 1
    ring
  have hTcross : T ^ 2 = (n : ℝ) * S ^ 2 * scale n (6 * d) := by
    dsimp only [T, S]
    rw [scale_sq hn.le, scale_sq hn.le]
    rw [show (n : ℝ) = scale n 1 by simp [scale]]
    rw [scale_mul_three hn]
    congr 1
    ring
  have hEden : 2 * R * H ^ 2 ≤ 288 * A * B ^ 2 := by
    have hH0' : 0 ≤ H := hH0.le
    have h12B0 : 0 ≤ 12 * B := by positivity
    have hHsq : H ^ 2 ≤ (12 * B) ^ 2 :=
      (sq_le_sq₀ hH0' h12B0).2 hH
    calc
      2 * R * H ^ 2 ≤ 2 * A * (12 * B) ^ 2 := by
        gcongr
      _ = 288 * A * B ^ 2 := by ring
  have hE : 2 * x ≤ (T / 8) ^ 2 / (2 * R * H ^ 2) := by
    apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hR0) (sq_pos_of_pos hH0))).2
    calc
      2 * x * (2 * R * H ^ 2) ≤ 2 * x * (288 * A * B ^ 2) := by
        gcongr
      _ ≤ (T / 8) ^ 2 := by
        have : 36864 * x ≤ x ^ 2 := by nlinarith
        calc
          2 * x * (288 * A * B ^ 2) =
              (A * B ^ 2) * (36864 * x) / 64 := by ring
          _ ≤ (A * B ^ 2) * x ^ 2 / 64 := by gcongr
          _ = (T / 8) ^ 2 := by rw [← hT2]; ring
  have hRow : 2 * x ≤ S ^ 2 / (2 * R * 8 ^ 2) := by
    apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hR0) (by norm_num))).2
    calc
      2 * x * (2 * R * 8 ^ 2) ≤ 2 * x * (2 * A * 8 ^ 2) := by
        gcongr
      _ ≤ S ^ 2 := by
        have : 256 * x ≤ x ^ 2 := by nlinarith
        calc
          2 * x * (2 * A * 8 ^ 2) = A * (256 * x) := by ring
          _ ≤ A * x ^ 2 := mul_le_mul_of_nonneg_left this hA0.le
          _ = S ^ 2 := hS2.symm
  have hScale6 : scale n (6 * d) = x * scale n (11 * d / 2) := by
    dsimp only [x]
    rw [scale_mul hn]
    congr 1
    ring
  have hCross : 2 * x ≤ (T / 4) ^ 2 / (2 * L * (8 * S) ^ 2) := by
    apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hL0)
      (sq_pos_of_pos (mul_pos (by norm_num) hS0)))).2
    calc
      2 * x * (2 * L * (8 * S) ^ 2) ≤
          2 * x * (2 * (n : ℝ) * (8 * S) ^ 2) := by
        gcongr
      _ ≤ (T / 4) ^ 2 := by
        have : 4096 * x ≤ scale n (6 * d) := by
          rw [hScale6]
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hxC hx0.le
        calc
          2 * x * (2 * (n : ℝ) * (8 * S) ^ 2) =
              ((n : ℝ) * S ^ 2) * (4096 * x) / 16 := by ring
          _ ≤ ((n : ℝ) * S ^ 2) * scale n (6 * d) / 16 := by
            gcongr
          _ = (T / 4) ^ 2 := by rw [← hTcross]; ring
  simpa only [x, S, T, neg_div] using
    weighted_three_exp_le_exp_neg (Nat.cast_nonneg n) hE hRow hCross hpref

lemma ksss_meanGap_le_half_target {n m : ℕ}
    (d : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (hn : 0 < n) (hpart : IsKSSSPartition d P)
    (hscale8 : 8 ≤ scale n (1 - d))
    (hlogSq : 128 * Real.log n ^ 2 ≤ scale n (3 / 4 + 3 * d)) :
    ksssExposedMeanGap d P ≤ scale n (3 / 4 + 4 * d) / 2 := by
  let D := scale n (1 - d) / 4
  have hD0 : 0 < D := by
    dsimp only [D]
    positivity
  have hpred : ∀ k, D ≤ (((P.fiber k).card - 1 : ℕ) : ℝ) := by
    intro k
    have hfiber := ksss_fiberCard_lower P d hn hpart.2.2 hpart.1 k
    have hs4 : (4 : ℝ) ≤ (P.fiber k).card := by
      nlinarith
    have hs4Nat : 4 ≤ (P.fiber k).card := by exact_mod_cast hs4
    have hsNat : 1 ≤ (P.fiber k).card := by omega
    rw [Nat.cast_sub hsNat]
    dsimp only [D]
    nlinarith
  have hgap := ksssExposedMeanGap_le_of_pred_fiber_lower d P D hD0 hpred
  have hWsq : ksssSliceMargin n d ^ 2 =
      scale n (1 - d) * Real.log n ^ 2 := by
    rw [ksssSliceMargin, mul_pow, scale_sq hn.le]
    congr 2
    ring
  have hDform : (8 * ksssSliceMargin n d ^ 2 / D) =
      32 * Real.log n ^ 2 := by
    rw [hWsq]
    dsimp only [D]
    field_simp [ne_of_gt (scale_pos hn (1 - d))]
    <;> ring
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hgap' : ksssExposedMeanGap d P ≤
      64 * scale n d * Real.log n ^ 2 := by
    calc
      ksssExposedMeanGap d P ≤
          (m : ℝ) * (8 * ksssSliceMargin n d ^ 2 / D) := hgap
      _ = (m : ℝ) * (32 * Real.log n ^ 2) := by rw [hDform]
      _ ≤ (2 * scale n d) * (32 * Real.log n ^ 2) := by
        exact mul_le_mul_of_nonneg_right hpart.2.2 (by positivity)
      _ = 64 * scale n d * Real.log n ^ 2 := by ring
  have htarget :
      128 * scale n d * Real.log n ^ 2 ≤ scale n (3 / 4 + 4 * d) := by
    calc
      128 * scale n d * Real.log n ^ 2 =
          scale n d * (128 * Real.log n ^ 2) := by ring
      _ ≤ scale n d * scale n (3 / 4 + 3 * d) :=
        mul_le_mul_of_nonneg_left hlogSq (scale_nonneg n d)
      _ = scale n (3 / 4 + 4 * d) := by
        rw [scale_mul hn]
        congr 1
        ring
  linarith

lemma ksss_aggregate_bounds {n m : ℕ}
    (d : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (hn : 0 < n) (hd : 0 < d) (hpart : IsKSSSPartition d P)
    (hWone : 1 ≤ ksssSliceMargin n d)
    (hWfit : ∀ k, ksssSliceMargin n d + 1 ≤
      ((P.fiber k).card : ℝ) / 2)
    (hlogR : 8 * Real.log n ≤ scale n (d / 2)) :
    let core : Fin m → ℕ := fun k ↦ ksssCoreSize n d (P.fiber k).card
    let r := twoStageExceptionalSize (fun k ↦ (P.fiber k).card) core
    0 < ∑ k, r k ∧
      (∑ k, (r k : ℝ)) ≤ scale n (1 / 2 + d) ∧
      0 < ∑ k, ((P.fiber k).card - r k : ℕ) ∧
      (∑ k, (((P.fiber k).card - r k : ℕ) : ℝ)) ≤ (n : ℝ) ∧
      4 * scale n (1 / 2 + 3 * d) + 8 * (∑ k, (r k : ℝ)) ≤
        12 * scale n (1 / 2 + 3 * d) := by
  dsimp only
  let core : Fin m → ℕ := fun k ↦ ksssCoreSize n d (P.fiber k).card
  let r := twoStageExceptionalSize (fun k ↦ (P.fiber k).card) core
  have hW0 : 0 ≤ ksssSliceMargin n d := le_trans zero_le_one hWone
  have hmargin : ∀ k, ksssSliceMargin n d ≤
      ((P.fiber k).card : ℝ) / 2 := fun k ↦
    (le_add_of_nonneg_right zero_le_one).trans (hWfit k)
  have hcore : ∀ k, 2 * core k ≤ (P.fiber k).card := by
    intro k
    exact two_mul_floor_half_sub_le (P.fiber k).card
      (ksssSliceMargin n d) hW0 (hmargin k)
  have hrPos : ∀ k, 0 < r k := by
    intro k
    exact nat_sub_two_floor_pos_of_margin_pos (P.fiber k).card
      (ksssSliceMargin n d) hW0 (lt_of_lt_of_le zero_lt_one hWone)
      (hmargin k)
  have hmRpos : (0 : ℝ) < m :=
    (div_pos (scale_pos hn d) (by norm_num)).trans_le hpart.2.1
  have hmpos : 0 < m := by exact_mod_cast hmRpos
  let k₀ : Fin m := ⟨0, hmpos⟩
  have hRnat : 0 < ∑ k, r k := by
    apply Finset.sum_pos'
    · exact fun k hk ↦ (hrPos k).le
    · exact ⟨k₀, Finset.mem_univ k₀, hrPos k₀⟩
  have hrBound : ∀ k, (r k : ℝ) ≤ 4 * ksssSliceMargin n d := by
    intro k
    calc
      (r k : ℝ) ≤ 2 * ksssSliceMargin n d + 2 := by
        exact nat_sub_two_floor_le_margin (P.fiber k).card
          (ksssSliceMargin n d) hW0 (hmargin k)
      _ ≤ 4 * ksssSliceMargin n d := by linarith
  have hRreal : (∑ k, (r k : ℝ)) ≤ scale n (1 / 2 + d) := by
    calc
      (∑ k, (r k : ℝ)) ≤
          ∑ _k : Fin m, 4 * ksssSliceMargin n d := by
        exact Finset.sum_le_sum fun k hk ↦ hrBound k
      _ = (m : ℝ) * (4 * ksssSliceMargin n d) := by simp
      _ ≤ (2 * scale n d) * (4 * ksssSliceMargin n d) := by
        exact mul_le_mul_of_nonneg_right hpart.2.2
          (mul_nonneg (by norm_num) hW0)
      _ = scale n d * scale n ((1 - d) / 2) *
          (8 * Real.log n) := by
        rw [ksssSliceMargin]
        ring
      _ ≤ scale n d * scale n ((1 - d) / 2) * scale n (d / 2) := by
        exact mul_le_mul_of_nonneg_left hlogR
          (mul_nonneg (scale_nonneg n d) (scale_nonneg n _))
      _ = scale n (1 / 2 + d) := by
        rw [scale_mul_three hn]
        congr 1
        ring
  have hcorePos : ∀ k, 0 < core k := by
    intro k
    exact nat_floor_half_sub_pos (P.fiber k).card (ksssSliceMargin n d) (hWfit k)
  have hLterm : ∀ k, 0 < (P.fiber k).card - r k := by
    intro k
    rw [twoStageExceptionalSize_complement (fun k ↦ (P.fiber k).card) core hcore k]
    exact Nat.mul_pos (by norm_num) (hcorePos k)
  have hLnat : 0 < ∑ k, ((P.fiber k).card - r k : ℕ) := by
    apply Finset.sum_pos'
    · exact fun k hk ↦ (hLterm k).le
    · exact ⟨k₀, Finset.mem_univ k₀, hLterm k₀⟩
  have hLnatUpper : ∑ k, ((P.fiber k).card - r k : ℕ) ≤ n := by
    calc
      ∑ k, ((P.fiber k).card - r k : ℕ) ≤
          ∑ k, (P.fiber k).card :=
        Finset.sum_le_sum fun k hk ↦ Nat.sub_le _ _
      _ = n := sum_card_bucketPartition_fiber P
  have hLreal : (∑ k, (((P.fiber k).card - r k : ℕ) : ℝ)) ≤
      (n : ℝ) := by
    exact_mod_cast hLnatUpper
  have hAB : scale n (1 / 2 + d) ≤ scale n (1 / 2 + 3 * d) := by
    apply scale_mono_exponent (show 1 ≤ n by omega)
    linarith
  have hH : 4 * scale n (1 / 2 + 3 * d) + 8 * (∑ k, (r k : ℝ)) ≤
      12 * scale n (1 / 2 + 3 * d) := by
    nlinarith
  exact ⟨hRnat, hRreal, hLnat, hLreal, hH⟩

theorem ksssLemma112_of_scale_conditions {n m : ℕ}
    (d : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (ell ell' : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ)
    (hn : 0 < n) (hd : 0 < d) (hpart : IsKSSSPartition d P)
    (hell : IsNearBalanced d P ell) (hell' : IsNearBalanced d P ell')
    (hcoeff : HasKSSSBalancedCoefficients d P f F)
    (hWone : 1 ≤ ksssSliceMargin n d)
    (hWfit : ∀ k, ksssSliceMargin n d + 1 ≤
      ((P.fiber k).card : ℝ) / 2)
    (hlogR : 8 * Real.log n ≤ scale n (d / 2))
    (hscale8 : 8 ≤ scale n (1 - d))
    (hlogSq : 128 * Real.log n ^ 2 ≤ scale n (3 / 4 + 3 * d))
    (hxE : 36864 ≤ scale n (d / 2))
    (hxC : 4096 ≤ scale n (11 * d / 2))
    (hpref : (4 : ℝ) * n + 6 ≤ Real.exp (scale n (d / 2))) :
    HasQuadraticSliceCoupling P ell ell' f₀ f F
      (scale n (3 / 4 + 4 * d)) (Real.exp (-scale n (d / 2))) := by
  let core : Fin m → ℕ := fun k ↦ ksssCoreSize n d (P.fiber k).card
  let r := twoStageExceptionalSize (fun k ↦ (P.fiber k).card) core
  have hagg := ksss_aggregate_bounds d P hn hd hpart hWone hWfit hlogR
  dsimp only at hagg
  have hmargin0 : 0 ≤ ksssSliceMargin n d := le_trans zero_le_one hWone
  have hmargin : ∀ k, ksssSliceMargin n d ≤
      ((P.fiber k).card : ℝ) / 2 := fun k ↦
    (le_add_of_nonneg_right zero_le_one).trans (hWfit k)
  have hcard : ∀ k, 2 ≤ (P.fiber k).card := by
    intro k
    have hs : (4 : ℝ) ≤ (P.fiber k).card := by
      have := hWfit k
      nlinarith
    exact_mod_cast (show (2 : ℝ) ≤ (P.fiber k).card by linarith)
  have hgap := ksss_meanGap_le_half_target d P hn hpart hscale8 hlogSq
  have hdist :
      2 * (scale n (3 / 4 + 4 * d) / 8) +
          scale n (3 / 4 + 4 * d) / 4 + ksssExposedMeanGap d P ≤
        scale n (3 / 4 + 4 * d) := by
    linarith
  have hR0 : 0 < ∑ k : Fin m, (r k : ℝ) := by
    exact_mod_cast hagg.1
  have hL0 : 0 < ∑ k : Fin m,
      (((P.fiber k).card - r k : ℕ) : ℝ) := by
    exact_mod_cast hagg.2.2.1
  have hprob :
      4 * Real.exp
          (-(scale n (3 / 4 + 4 * d) / 8) ^ 2 /
            (2 * (∑ k : Fin m, (r k : ℝ)) *
              (4 * scale n (1 / 2 + 3 * d) +
                8 * (∑ k : Fin m, (r k : ℝ))) ^ 2)) +
        ((n : ℝ) * (4 * Real.exp (-scale n (1 / 4 + d) ^ 2 /
          (2 * (∑ k : Fin m, (r k : ℝ)) * 8 ^ 2))) +
        2 * Real.exp (-(scale n (3 / 4 + 4 * d) / 4) ^ 2 /
          (2 * (∑ k : Fin m,
              (((P.fiber k).card - r k : ℕ) : ℝ)) *
            (8 * scale n (1 / 4 + d)) ^ 2))) ≤
        Real.exp (-scale n (d / 2)) := by
    exact ksss_threshold_probability_bound d
      (∑ k : Fin m, (r k : ℝ))
      (∑ k : Fin m, (((P.fiber k).card - r k : ℕ) : ℝ))
      (4 * scale n (1 / 2 + 3 * d) + 8 * (∑ k : Fin m, (r k : ℝ)))
      hn hR0 hL0 (by
        have := scale_pos hn (1 / 2 + 3 * d)
        nlinarith)
      hagg.2.1 hagg.2.2.2.1
      hagg.2.2.2.2 hxE hxC hpref
  apply ksssLemma112_of_numerical d P ell ell' f₀ f F
    (scale n (3 / 4 + 4 * d) / 8) (scale n (1 / 4 + d))
    (scale n (3 / 4 + 4 * d) / 4)
    hmargin0 hmargin hcard hell hell' hcoeff
  · simpa only [r, core] using hagg.1
  · simpa only [r, core] using hagg.2.2.1
  · exact div_nonneg (scale_nonneg n _) (by norm_num)
  · exact scale_pos hn _
  · exact div_nonneg (scale_nonneg n _) (by norm_num)
  · exact hdist
  · simpa only [r, core] using hprob

/-- Exact source-facing formulation of KSSS Lemma 11.2. -/
def KSSSLemma112 : Prop :=
  ∀ d : ℝ, 0 < d → d < 1 / 4 →
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (m : ℕ) (P : BucketPartition (Fin n) (Fin m))
        (ell ell' : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
        (F : Fin n → Fin n → ℝ),
        IsKSSSPartition d P →
        IsNearBalanced d P ell → IsNearBalanced d P ell' →
        HasKSSSBalancedCoefficients d P f F →
        HasQuadraticSliceCoupling P ell ell' f₀ f F
          (scale n (3 / 4 + 4 * d)) (Real.exp (-scale n (d / 2)))

theorem ksssLemma112 : KSSSLemma112 := by
  intro d hd hd4
  let q := (1 - d) / 2
  have hq : 0 < q := by dsimp only [q]; linarith
  have hOneSub : 0 < 1 - d := by linarith
  have hLogFit := eventually_const_mul_log_le_scale 8 q (by norm_num) hq
  have hLogR := eventually_const_mul_log_le_scale 8 (d / 2)
    (by norm_num) (div_pos hd (by norm_num))
  have hScaleOneSub := eventually_const_le_scale 8 (1 - d) hOneSub
  have hLogSq := eventually_const_mul_log_sq_le_scale 128 (3 / 4 + 3 * d)
    (by norm_num) (by linarith)
  have hXE := eventually_const_le_scale 36864 (d / 2)
    (div_pos hd (by norm_num))
  have hXC := eventually_const_le_scale 4096 (11 * d / 2) (by positivity)
  have hPref := eventually_linear_le_exp_scale (d / 2)
    (div_pos hd (by norm_num))
  have hScaleQ := eventually_const_le_scale 1 q hq
  have hLogOne : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log n := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 1)
  filter_upwards [Filter.eventually_ge_atTop 1, hLogFit, hLogR,
    hScaleOneSub, hLogSq, hXE, hXC, hPref, hScaleQ, hLogOne]
    with n hn hlogFit hlogR hscaleOneSub hlogSq hxE hxC hpref hscaleQ hlogOne
  intro m P ell ell' f₀ f F hpart hell hell' hcoeff
  have hnpos : 0 < n := by omega
  have hWone : 1 ≤ ksssSliceMargin n d := by
    rw [ksssSliceMargin]
    nlinarith [mul_le_mul hscaleQ hlogOne zero_le_one (scale_nonneg n q)]
  have hWfit : ∀ k, ksssSliceMargin n d + 1 ≤
      ((P.fiber k).card : ℝ) / 2 := by
    intro k
    have hfiber := ksss_fiberCard_lower P d hnpos hpart.2.2 hpart.1 k
    have hWsmall : ksssSliceMargin n d ≤ scale n (1 - d) / 8 := by
      rw [ksssSliceMargin]
      have hlogDiv : Real.log n ≤ scale n q / 8 := by linarith
      calc
        scale n ((1 - d) / 2) * Real.log n ≤
            scale n q * (scale n q / 8) := by
          dsimp only [q]
          gcongr
        _ = (scale n q * scale n q) / 8 := by ring
        _ = scale n (q + q) / 8 := by rw [scale_mul hnpos]
        _ = scale n (1 - d) / 8 := by
          congr 2
          dsimp only [q]
          ring
    have hone : (1 : ℝ) ≤ scale n (1 - d) / 8 := by linarith
    nlinarith
  exact ksssLemma112_of_scale_conditions d P ell ell' f₀ f F hnpos hd hpart
    hell hell' hcoeff hWone hWfit hlogR hscaleOneSub hlogSq hxE hxC hpref

end Erdos88.BooleanSlices
