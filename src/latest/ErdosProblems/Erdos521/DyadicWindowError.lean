/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The coefficient-window truncation probability on a dyadic spatial bin.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.DyadicWindowGeometry

namespace Erdos521

theorem dyadic_window_normalized_error_probability (n k q : ℕ) (hqk : q ≤ k)
    (hH : 2 ^ (k + q) ≤ n) {x t : ℝ} (hx₀ : 0 ≤ x)
    (hx : x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1))) (ht : 0 < t)
    (htail : x ^ (2 * (n + 1)) ≤ 1 / 2) :
    sequenceLaw.real {ε | t * Real.sqrt (geometricVariance x (n + 1)) ≤
      |powerSum ε (n + 1) x - windowPowerSum ε (dyadicCoefficientWindow n k q) x|} ≤
      8 * ((2 : ℝ) ^ q)⁻¹ / t ^ 2 := by
  have hLU : 2 ^ (k - q) ≤ 2 ^ (k + q) + 1 := by
    have h : (2 : ℕ) ^ (k - q) ≤ 2 ^ (k + q) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  have hx₁ : x < 1 := hx.2.trans_lt (dyadicPoint_lt_one (k + 1))
  have h := windowPowerSum_normalized_error hx₀ hx₁ ht hLU (by omega : 2 ^ (k + q) + 1 ≤ n + 1) htail
  rw [← dyadicCoefficientWindow_eq_Ico hH] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  have hlow : ((2 ^ (k - q) : ℕ) : ℝ) * (1 - x) ≤ ((2 : ℝ) ^ q)⁻¹ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using dyadic_window_low_bound hqk hx
  have hhigh := dyadic_window_high_bound (q := q) hx₀ hx
  nlinarith

end Erdos521
