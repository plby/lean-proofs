import Arxiv.Arxiv2411_18291.PaperAlphaGrowth

/-! # An edge cap with a small power bound at the paper's threshold -/

noncomputable section

namespace Arxiv2411_18291

def modularEdgeCap (q r N : ℕ) (δ : ℝ) : ℕ :=
  ⌈(8 * (q.choose r : ℝ) ^ 2 * N) / δ ^ 2⌉₊

theorem modularEdgeCap_pos {q r N : ℕ} {δ : ℝ} (hqr : r ≤ q)
    (hN : 0 < N) (hδ : 0 < δ) : 0 < modularEdgeCap q r N δ := by
  have hk : (0 : ℝ) < q.choose r := by exact_mod_cast Nat.choose_pos hqr
  unfold modularEdgeCap
  exact Nat.ceil_pos.mpr (by positivity)

theorem modularEdgeCap_budget (q r N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    8 * (q.choose r : ℝ) ^ 2 * N ≤ δ ^ 2 * modularEdgeCap q r N δ := by
  have hh := Nat.le_ceil ((8 * (q.choose r : ℝ) ^ 2 * N) / δ ^ 2)
  exact (div_le_iff₀ (sq_pos_of_pos hδ)).mp hh |>.trans_eq (mul_comm _ _)

theorem edge_cap_coefficient_bound {q r N : ℕ} (hqr : r + 1 < q)
    (hN : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    16 * q.choose (r + 1) ^ 2 * N ≤ (4 * q) ^ (q + 1) := by
  by_cases hq : 4 ≤ q
  · have hNPow : N ≤ q ^ q := by
      calc
        N ≤ (r + 1).factorial * q.choose (r + 1) := hN
        _ = q.descFactorial (r + 1) :=
          (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
        _ ≤ q ^ (r + 1) := Nat.descFactorial_le_pow _ _
        _ ≤ q ^ q := Nat.pow_le_pow_right (by omega) hqr.le
    have hk : q.choose (r + 1) ^ 2 ≤ 4 ^ q := by
      calc
        _ ≤ (2 ^ q) ^ 2 := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) 2
        _ = 4 ^ q := by rw [← pow_mul, mul_comm q 2, pow_mul]; norm_num
    calc
      _ = 16 * (q.choose (r + 1) ^ 2 * N) := by ring
      _ ≤ (4 * q) * (4 ^ q * q ^ q) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul hk hNPow)
      _ = (4 * q) ^ (q + 1) := by rw [← mul_pow, pow_succ]; ring
  · have hqsmall : q = 2 ∨ q = 3 := by omega
    rcases hqsmall with rfl | rfl
    · have hr : r = 0 := by omega
      subst r
      norm_num at hN ⊢
      omega
    · have hr : r = 0 ∨ r = 1 := by omega
      rcases hr with rfl | rfl <;> norm_num at hN ⊢ <;> omega

theorem modularEdgeCap_le_paper_threshold {q r n N : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hN : 0 < N)
    (hNb : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    (modularEdgeCap q (r + 1) N
      ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hk : (1 : ℝ) ≤ q.choose (r + 1) := by
    exact_mod_cast Nat.choose_pos hqr.le
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let α := paperAlpha q (r + 1)
  let δ := (n : ℝ) ^ (-(α / 60))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1
    (by dsimp only [α]; linarith only [paperAlpha_pos hqr])
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith only [hδ, hδ1]
  have hX : (1 : ℝ) ≤ (8 * (q.choose (r + 1) : ℝ) ^ 2 * N) / δ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
    have hh := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ (q.choose (r + 1) : ℝ) ^ 2 by nlinarith only [hk])
      (show (0 : ℝ) ≤ N by positivity)
    nlinarith only [hh, hNR, hδsq]
  have hceil := Nat.ceil_lt_add_one (zero_le_one.trans hX)
  have hround : (modularEdgeCap q (r + 1) N δ : ℝ) ≤
      16 * (q.choose (r + 1) : ℝ) ^ 2 * N / δ ^ 2 := by
    unfold modularEdgeCap
    calc
      _ ≤ 2 * ((8 * (q.choose (r + 1) : ℝ) ^ 2 * N) / δ ^ 2) :=
        by linarith only [hceil, hX]
      _ = _ := by ring
  have hinv : (δ ^ 2)⁻¹ = (n : ℝ) ^ (α / 30) := by
    dsimp only [δ]
    rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_neg hn0.le]
    congr 1
    norm_num
    ring
  have hcoef : (16 * (q.choose (r + 1) : ℝ) ^ 2 * N) ≤
      (4 * q : ℝ) ^ (q + 1) := by exact_mod_cast edge_cap_coefficient_bound hqr hNb
  have hg : (4 * q : ℝ) ^ (q + 1) ≤ (n : ℝ) ^ (α / 60) := by
    have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    convert paper_threshold_alpha_rpow_lower hqr hn (s := q + 1)
      (t := (1 / 60 : ℝ)) (by norm_num) (by push_cast; linarith only [hq]) using 1
    dsimp only [α]
    congr 1
    ring
  calc
    _ ≤ 16 * (q.choose (r + 1) : ℝ) ^ 2 * N / δ ^ 2 := hround
    _ = (16 * (q.choose (r + 1) : ℝ) ^ 2 * N) * (n : ℝ) ^ (α / 30) := by
      rw [div_eq_mul_inv, hinv]
    _ ≤ (n : ℝ) ^ (α / 60) * (n : ℝ) ^ (α / 30) :=
      mul_le_mul_of_nonneg_right (hcoef.trans hg) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; dsimp only [α]; ring

end Arxiv2411_18291
