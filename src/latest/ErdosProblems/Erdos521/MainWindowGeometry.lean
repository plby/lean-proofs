/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Degrees and endpoint distances for the central coefficient windows.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainBinBulk
import ErdosProblems.Erdos521.WindowCapBounds

namespace Erdos521

def dyadicWindowDegree (k q : ℕ) : ℕ := 2 ^ (k + q) - 2 ^ (k - q)

theorem main_window_exponents {j k : ℕ} (hk : k ∈ mainBinSet j) :
    windowWidthScale j ≤ k ∧ k + windowWidthScale j ≤ j := by
  have hq : windowWidthScale j ≤ Nat.sqrt j := Nat.sqrt_le_self _
  have h := mainBinSet_mem hk
  constructor <;> omega

theorem main_window_upper {j k : ℕ} (hk : k ∈ mainBinSet j) :
    (2 : ℕ) ^ (k + windowWidthScale j) ≤ 2 ^ j :=
  pow_le_pow_right₀ (by norm_num) (main_window_exponents hk).2

theorem dyadic_window_low_le_high (k q : ℕ) : (2 : ℕ) ^ (k - q) ≤ 2 ^ (k + q) :=
  pow_le_pow_right₀ (by norm_num) (by omega)

theorem dyadicWindowDegree_add_low (k q : ℕ) :
    dyadicWindowDegree k q + 2 ^ (k - q) = 2 ^ (k + q) :=
  Nat.sub_add_cancel (dyadic_window_low_le_high k q)

theorem twice_low_le_high (k : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    2 * (2 : ℕ) ^ (k - q) ≤ 2 ^ (k + q) := by
  calc
    2 * (2 : ℕ) ^ (k - q) = 2 ^ (k - q + 1) := by simp [pow_succ, mul_comm]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

theorem high_le_twice_dyadicWindowDegree (k : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    (2 : ℕ) ^ (k + q) ≤ 2 * dyadicWindowDegree k q := by
  have h := twice_low_le_high k hq
  have heq := dyadicWindowDegree_add_low k q
  omega

theorem pow_le_dyadicWindowDegree (k : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    (2 : ℕ) ^ k ≤ dyadicWindowDegree k q := by
  have hpow : 2 * (2 : ℕ) ^ k ≤ 2 ^ (k + q) := by
    calc
      2 * (2 : ℕ) ^ k = 2 ^ (k + 1) := by simp [pow_succ, mul_comm]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have h := high_le_twice_dyadicWindowDegree k hq
  omega

theorem dyadicWindowDegree_endpoint_gap_lower (k : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    (2 : ℝ) ^ q / 4 ≤ (dyadicWindowDegree k q : ℝ) * (1 - dyadicPoint (k + 1)) := by
  have hhalf : ((2 ^ (k + q) : ℕ) : ℝ) / 2 ≤ dyadicWindowDegree k q := by
    have h : ((2 ^ (k + q) : ℕ) : ℝ) ≤ 2 * (dyadicWindowDegree k q : ℝ) := by
      exact_mod_cast high_le_twice_dyadicWindowDegree k hq
    linarith
  have hgap : 1 - dyadicPoint (k + 1) = 1 / (2 : ℝ) ^ (k + 1) := by unfold dyadicPoint; ring
  calc
    (2 : ℝ) ^ q / 4 = (((2 ^ (k + q) : ℕ) : ℝ) / 2) * (1 / (2 : ℝ) ^ (k + 1)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_add, pow_succ]
      field_simp
      norm_num
    _ ≤ (dyadicWindowDegree k q : ℝ) * (1 / (2 : ℝ) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_right hhalf (by positivity)
    _ = _ := by rw [hgap]

theorem main_window_degree_bounds {j k : ℕ} (hj : 1 ≤ j) (hk : k ∈ mainBinSet j) :
    (2 : ℕ) ^ windowWidthScale j ≤ dyadicWindowDegree k (windowWidthScale j) ∧
      dyadicWindowDegree k (windowWidthScale j) ≤ 2 ^ j := by
  constructor
  · exact (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (main_window_exponents hk).1).trans
      (pow_le_dyadicWindowDegree k (windowWidthScale_pos hj))
  · exact (Nat.sub_le _ _).trans (main_window_upper hk)

end Erdos521
