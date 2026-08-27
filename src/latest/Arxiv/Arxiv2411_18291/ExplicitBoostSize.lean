import Arxiv.Arxiv2411_18291.PaperSizeParameters

/-! # Explicit size inequalities used by regularity boosting -/

namespace Arxiv2411_18291

theorem boost_threshold_le_paper_threshold {q r : ℕ} (hqr : r < q) :
    (4 * q) ^ (90 * q) ≤ paperSizeThreshold q r := by
  have hA : 1 ≤ paperInverseAlpha q r := Nat.succ_le_of_lt (paperInverseAlpha_pos hqr)
  apply Nat.pow_le_pow_right (by omega : 0 < 4 * q)
  simpa only [mul_one] using Nat.mul_le_mul_left (90 * q) hA

theorem boost_threshold_ge_square {q n : ℕ} (hq : 2 ≤ q)
    (hn : (4 * q) ^ (90 * q) ≤ n) : (4 * q) ^ 2 ≤ n :=
  (Nat.pow_le_pow_right (by omega : 0 < 4 * q) (by omega : 2 ≤ 90 * q)).trans hn

theorem paper_small_carrier_completion_size {q r n m : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hm : m ≤ (4 * q) ^ (2 * q)) :
    4 * m ^ 2 ≤ n := by
  calc
    _ ≤ (4 * q) ^ 1 * ((4 * q) ^ (2 * q)) ^ 2 :=
      Nat.mul_le_mul (by simp only [pow_one]; omega) (Nat.pow_le_pow_left hm 2)
    _ = (4 * q) ^ (1 + (2 * q) * 2) := by rw [← pow_mul, ← pow_add]
    _ ≤ (4 * q) ^ (90 * q) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ n := (boost_threshold_le_paper_threshold hqr).trans hn

theorem boost_threshold_root_size_bounds {q n : ℕ} (hq : 2 ≤ q)
    (hn : (4 * q) ^ (90 * q) ≤ n) : q ^ 2 * 2 ^ (3 * q) ≤ n ∧ 8 * q ^ 2 ≤ n ∧ 2 * q ≤ n := by
  have hsq := boost_threshold_ge_square hq hn
  refine ⟨?_, by nlinarith only [hsq], ?_⟩
  · calc
      _ ≤ (4 * q) ^ 2 * (4 * q) ^ (3 * q) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : q ≤ 4 * q) 2)
          (Nat.pow_le_pow_left (by omega : 2 ≤ 4 * q) (3 * q))
      _ = (4 * q) ^ (2 + 3 * q) := (pow_add _ _ _).symm
      _ ≤ (4 * q) ^ (90 * q) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := hn
  · have hh := Nat.mul_le_mul_left (4 * q) (show 1 ≤ 4 * q by omega)
    nlinarith only [hh, hsq]

theorem boost_threshold_rpow_lower {q n s : ℕ} (hq : 2 ≤ q)
    (hn : (4 * q) ^ (90 * q) ≤ n) {t : ℝ} (ht : 0 ≤ t)
    (hst : (s : ℝ) ≤ (90 * q : ℝ) * t) :
    (4 * q : ℝ) ^ s ≤ (n : ℝ) ^ t := by
  have hb : (1 : ℝ) ≤ 4 * q := by exact_mod_cast (show 1 ≤ 4 * q by omega)
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg ((4 * q) ^ (90 * q)))
    (by exact_mod_cast hn : (((4 * q) ^ (90 * q) : ℕ) : ℝ) ≤ n) ht
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)] at hh
  push_cast at hh
  calc
    _ = (4 * q : ℝ) ^ (s : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (4 * q : ℝ) ^ ((90 * q : ℝ) * t) :=
      Real.rpow_le_rpow_of_exponent_le hb hst
    _ ≤ _ := hh

theorem boost_threshold_factorial_le {q n d : ℕ} (hq : 2 ≤ q) (hd : d ≤ q)
    (hn : (4 * q) ^ (90 * q) ≤ n) : (d.factorial : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
  have hnat : d.factorial ≤ (4 * q) ^ q := by
    calc
      _ ≤ q.factorial := Nat.factorial_le hd
      _ ≤ q ^ q := Nat.factorial_le_pow q
      _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  have hpow := boost_threshold_rpow_lower (s := q) hq hn
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
    (by nlinarith only [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
  exact (by exact_mod_cast hnat : (d.factorial : ℝ) ≤ (4 * q : ℝ) ^ q).trans hpow

end Arxiv2411_18291
