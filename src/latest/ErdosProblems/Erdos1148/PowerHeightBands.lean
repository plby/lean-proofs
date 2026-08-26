import ErdosProblems.Erdos1148.CuspBandCover

/-! # A power bound for the number of dyadic cusp bands -/

namespace Erdos1148.DukeArithmetic

theorem exists_power_height_band_count {d : ℝ} (hd : 1 ≤ d) :
    ∃ J : ℕ, d ^ (1 / 4 : ℝ) < (2 : ℝ) ^ J ∧
      (J : ℝ) ≤ 4 * d ^ (1 / 8 : ℝ) := by
  let r : ℝ := d ^ (1 / 8 : ℝ)
  let n : ℕ := ⌈r⌉₊
  have hr : 1 ≤ r := Real.one_le_rpow hd (by norm_num)
  have hrn : r ≤ (n : ℝ) := Nat.le_ceil r
  have hn : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n))
  have hnupper : (n : ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith)
  refine ⟨2 * n, ?_, ?_⟩
  · have hpow : d ^ (1 / 4 : ℝ) = r ^ 2 := by
      dsimp only [r]
      rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ d)]
      norm_num
    rw [hpow, show 2 * n = n * 2 by omega, pow_mul]
    exact (pow_le_pow_left₀ (by linarith : 0 ≤ r) hrn 2).trans_lt
      (pow_lt_pow_left₀ hn (by positivity : (0 : ℝ) ≤ n) (by norm_num : 2 ≠ 0))
  · push_cast
    change 2 * (n : ℝ) ≤ 4 * r
    linarith

end Erdos1148.DukeArithmetic
