import Arxiv.Arxiv2411_18291.FiniteTypicalityThreshold

/-! # The local typicality threshold when the rank-size product is at least fifteen

The rank in the source is `r + 1`. The polynomial prefactor in the simultaneous
concentration bound is absorbed at the source's threshold `2^(9*(r+1)*h)`.
-/

namespace Arxiv2411_18291

theorem typicality_polynomial_le_three_pow {k : ℕ} (hk : 15 ≤ k) :
    3072 * k ^ 3 ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsquare : 3 * k ≤ k ^ 2 := by nlinarith only [hk]
    have hcube : 3 * k ^ 2 ≤ k ^ 3 := by
      nlinarith only [Nat.mul_le_mul_right (k ^ 2) hk]
    rw [pow_succ (3 : ℕ)]
    nlinarith only [ih, hsquare, hcube, hk]

theorem local_typicality_growth {k n : ℕ} (hk : 15 ≤ k) (hn : 2 ^ (9 * k) ≤ n) :
    (3072 * k ^ 3 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
  have hp : (3 ^ k) ^ 5 ≤ n := by
    calc
      _ = (3 ^ 5) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k 5]
      _ ≤ (2 ^ 9) ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = 2 ^ (9 * k) := (pow_mul _ _ _).symm
      _ ≤ n := hn
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg ((3 ^ k) ^ 5))
    (show (((3 ^ k) ^ 5 : ℕ) : ℝ) ≤ n by exact_mod_cast hp)
    (by norm_num : (0 : ℝ) ≤ 1 / 5)
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg (3 ^ k))] at hh
  norm_num at hh
  exact (show (3072 * k ^ 3 : ℝ) ≤ (3 : ℝ) ^ k by
    exact_mod_cast typicality_polynomial_le_three_pow hk).trans hh

theorem local_typicality_numerics {r h n : ℕ} (hr : 1 ≤ r) (hh : 1 ≤ h)
    (hk : 15 ≤ (r + 1) * h) (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n) :
    1 ≤ n ∧ r + 1 ≤ n ∧ 2 * (h * r) ≤ n ∧
      (4 * (h + 1) * (h * r) : ℝ) ≤ (n : ℝ) ^ (9 / 10 : ℝ) ∧
      192 * (h + 1 : ℝ) ^ 2 * (12 * ((r + 1) * h) + 5) ≤
        (n : ℝ) ^ (1 / 5 : ℝ) := by
  let k := (r + 1) * h
  have hkR : (15 : ℝ) ≤ k := by exact_mod_cast hk
  have hhk : h + 1 ≤ k := by dsimp only [k]; nlinarith only [hr, hh]
  have hrhk : h * r ≤ k := by dsimp only [k]; nlinarith
  have hhkR : (h + 1 : ℝ) ≤ k := by exact_mod_cast hhk
  have hrhkR : (h * r : ℝ) ≤ k := by exact_mod_cast hrhk
  have hnNat : 1 ≤ n := (Nat.one_le_pow _ _ (by norm_num)).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hgrowth := local_typicality_growth hk hn
  change (3072 * k ^ 3 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) at hgrowth
  have hroot : (4 * (h + 1) * (h * r) : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hprod := mul_le_mul hhkR hrhkR (by positivity : (0 : ℝ) ≤ h * r)
      (Nat.cast_nonneg k)
    have hcube := mul_le_mul_of_nonneg_right hkR (sq_nonneg (k : ℝ))
    exact (show (4 * (h + 1) * (h * r) : ℝ) ≤ 3072 * k ^ 3 by
      nlinarith only [hprod, hcube, sq_nonneg (k : ℝ)]).trans hgrowth
  have hrootN := hroot.trans (Real.rpow_le_self_of_one_le hn1 (by norm_num))
  have hsize : 2 * (h * r) ≤ n := by
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hhrr : (0 : ℝ) ≤ h * r := by positivity
    have hh' : (2 * (h * r) : ℝ) ≤ n := by nlinarith only [hrootN, hhR, hhrr]
    exact_mod_cast hh'
  have hrh : r ≤ h * r := by simpa only [one_mul] using Nat.mul_le_mul_right r hh
  refine ⟨hnNat, by omega, hsize, hroot.trans ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  · have hlin : (12 * k + 5 : ℝ) ≤ 16 * k := by linarith only [hkR]
    have hcoeff : 192 * (h + 1 : ℝ) ^ 2 * (12 * k + 5) ≤ 3072 * k ^ 3 := by
      calc
        _ ≤ 192 * (k : ℝ) ^ 2 * (16 * k) := by gcongr
        _ = _ := by ring
    simpa only [k, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcoeff.trans hgrowth

theorem local_typicality_tail {r h n : ℕ} (hr : 1 ≤ r) (hh : 1 ≤ h)
    (hk : 15 ≤ (r + 1) * h) (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n) :
    2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
        Real.exp (-((n : ℝ) ^ (3 / 10 : ℝ) / (192 * (h + 1 : ℝ) ^ 2))) <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  obtain ⟨hnNat, _, _, _, hcoeff⟩ := local_typicality_numerics hr hh hk hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  let k := (r + 1) * h
  let y := (n : ℝ) ^ (1 / 10 : ℝ)
  let A := 2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h)
  have hy0 : 0 < y := Real.rpow_pos_of_pos hn0 _
  have hy1 : 1 ≤ y := Real.one_le_rpow hn1 (by norm_num)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hrhk : (r * h : ℝ) ≤ k := by dsimp only [k]; push_cast; nlinarith
  have hhk : (h : ℝ) ≤ k := by
    exact_mod_cast (show h ≤ (r + 1) * h by nlinarith)
  have hln : Real.log (n : ℝ) ≤ 10 * y := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 10)
    convert hh using 1
    dsimp only [y]
    ring
  have hlogC : Real.log (2 * (h + 2 : ℝ)) ≤ 2 * h + 3 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * (h + 2))
    linarith only [hh]
  have hLA : Real.log A ≤ (12 * k + 3) * y := by
    dsimp only [A]
    rw [Real.log_mul (by positivity) (pow_pos hn0 _).ne', Real.log_pow]
    have hs := mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg (r * h))
    have ht := mul_le_mul_of_nonneg_right hrhk hy0.le
    have hu := mul_le_mul_of_nonneg_right hhk hy0.le
    have hv := mul_le_mul_of_nonneg_left hy1 (by positivity : (0 : ℝ) ≤ 2 * h + 3)
    push_cast at hs ⊢
    nlinarith only [hs, ht, hu, hv, hlogC]
  have hpow : (n : ℝ) ^ (3 / 10 : ℝ) = (n : ℝ) ^ (1 / 5 : ℝ) * y := by
    dsimp only [y]
    rw [← Real.rpow_add hn0]
    norm_num
  have hE : (12 * k + 5) * y ≤
      (n : ℝ) ^ (3 / 10 : ℝ) / (192 * (h + 1 : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 192 * (h + 1 : ℝ) ^ 2)).mpr
    rw [hpow]
    have hc : 192 * (h + 1 : ℝ) ^ 2 * (12 * k + 5) ≤
        (n : ℝ) ^ (1 / 5 : ℝ) := by
      simpa only [k, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcoeff
    have hm := mul_le_mul_of_nonneg_right hc hy0.le
    nlinarith only [hm]
  calc
    _ = Real.exp (Real.log A -
        (n : ℝ) ^ (3 / 10 : ℝ) / (192 * (h + 1 : ℝ) ^ 2)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hA]
    _ < Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
      apply Real.exp_lt_exp.mpr
      change _ < -y
      linarith only [hLA, hE, hy0]

end Arxiv2411_18291
