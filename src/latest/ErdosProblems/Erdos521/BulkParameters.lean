/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Polynomial scales for simultaneous root comparison in a degree block.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Decay

namespace Erdos521

open Filter

theorem block_repulsion_lower {B : ℝ} (hB : 0 ≤ B) {n k : ℕ}
    (hn : 2 ≤ n) (hnk : n ≤ k) (hkn : k ≤ 2 * n) :
    (n : ℝ) ^ (-2 * B) ≤ (k : ℝ) ^ (-B) := by
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk : (k : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hkn' : (k : ℝ) ≤ 2 * n := by exact_mod_cast hkn
    nlinarith
  calc
    (n : ℝ) ^ (-2 * B) = ((n : ℝ) ^ 2) ^ (-B) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n) 2 (-B)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hk₀ hk (by linarith)

theorem block_cubic_le {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ 2 * n) :
    (k + 1 : ℝ) ^ 3 ≤ 27 * (n : ℝ) ^ 3 := by
  have h : (k + 1 : ℝ) ≤ 3 * n := by exact_mod_cast (show k + 1 ≤ 3 * n by omega)
  calc
    (k + 1 : ℝ) ^ 3 ≤ (3 * (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
    _ = _ := by ring

theorem eventually_bulk_parameters {B : ℝ} (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ≤ 2 * n →
      (k + 1 : ℝ) ^ 3 * (2 * (n : ℝ) ^ (-(2 * B + 4))) ^ 2 ≤ (n : ℝ) ^ (-2 * B) ∧
      (k + 1 : ℝ) ^ 3 * (n : ℝ) ^ (-(2 * B + 4)) ≤ (n : ℝ) ^ (-2 * B) / 2 ∧
      (n : ℝ) ^ (-(4 * B + 6)) < (n : ℝ) ^ (-2 * B) * (n : ℝ) ^ (-(2 * B + 4)) / 2 := by
  filter_upwards [eventually_const_mul_rpow_le_rpow 108
      (by linarith : -4 * B - 5 < -2 * B),
    eventually_const_mul_rpow_le_rpow 54 (by linarith : -2 * B - 1 < -2 * B),
    eventually_const_mul_rpow_le_rpow 4 (by linarith : -(4 * B + 6) < -4 * B - 4),
    eventually_ge_atTop 1] with n hsep hscale hclose hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let ρ := (n : ℝ) ^ (-(2 * B + 4))
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hn₀ _
  have hρsq : ρ ^ 2 = (n : ℝ) ^ (-4 * B - 8) := by
    dsimp [ρ]
    rw [← Real.rpow_mul_natCast hn₀.le]
    congr 1
    ring
  have hsepId : (27 * (n : ℝ) ^ 3) * (2 * ρ) ^ 2 = 108 * (n : ℝ) ^ (-4 * B - 5) := by
    calc
      (27 * (n : ℝ) ^ 3) * (2 * ρ) ^ 2 = 108 * ((n : ℝ) ^ 3 * ρ ^ 2) := by ring
      _ = _ := by
        rw [hρsq, ← Real.rpow_natCast, ← Real.rpow_add hn₀]
        congr 2
        norm_num
        ring
  have hscaleId : 2 * ((27 * (n : ℝ) ^ 3) * ρ) = 54 * (n : ℝ) ^ (-2 * B - 1) := by
    calc
      2 * ((27 * (n : ℝ) ^ 3) * ρ) = 54 * ((n : ℝ) ^ 3 * ρ) := by ring
      _ = _ := by
        dsimp [ρ]
        rw [← Real.rpow_natCast, ← Real.rpow_add hn₀]
        congr 2
        norm_num
        ring
  have hprod : (n : ℝ) ^ (-2 * B) * ρ = (n : ℝ) ^ (-4 * B - 4) := by
    dsimp [ρ]
    rw [← Real.rpow_add hn₀]
    congr 1
    ring
  intro k hk
  have hcube := block_cubic_le hn hk
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hcube (sq_nonneg _)).trans (hsepId.le.trans hsep)
  · have hmul := mul_le_mul_of_nonneg_right hcube hρ.le
    have hh : 2 * ((27 * (n : ℝ) ^ 3) * ρ) ≤ (n : ℝ) ^ (-2 * B) := hscaleId.le.trans hscale
    change (k + 1 : ℝ) ^ 3 * ρ ≤ (n : ℝ) ^ (-2 * B) / 2
    linarith
  · change (n : ℝ) ^ (-(4 * B + 6)) < (n : ℝ) ^ (-2 * B) * ρ / 2
    rw [hprod]
    have hp : 0 < (n : ℝ) ^ (-(4 * B + 6)) := Real.rpow_pos_of_pos hn₀ _
    linarith

end Erdos521
