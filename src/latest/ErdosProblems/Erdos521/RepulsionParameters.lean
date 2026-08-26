/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Explicit mesh sizes and tolerances for the root-repulsion grid argument.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

def repulsionMesh (n j : ℕ) : ℕ := 8 * (n + 1) ^ 2 * 8 ^ j

noncomputable def repulsionThreshold (j : ℕ) : ℝ := (16 * (8 : ℝ) ^ (2 * j))⁻¹

theorem repulsionMesh_pos (n j : ℕ) : 0 < repulsionMesh n j := by
  unfold repulsionMesh
  positivity

theorem repulsionThreshold_pos (j : ℕ) : 0 < repulsionThreshold j := by
  unfold repulsionThreshold
  positivity

theorem grid_error_le {N P : ℝ} (hN : 1 ≤ N) (hP : 1 ≤ P) :
    (16 * P ^ 2)⁻¹ + (8 * N ^ 2 * P)⁻¹ *
      ((16 * P ^ 2)⁻¹ + N ^ 3 * (8 * N ^ 2 * P)⁻¹) ≤ 4 * (16 * P ^ 2)⁻¹ := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hM : 1 ≤ 8 * N ^ 2 * P := by
    have hN₂ : 1 ≤ N ^ 2 := one_le_pow₀ hN
    calc
      1 ≤ 8 * (1 : ℝ) * 1 := by norm_num
      _ ≤ 8 * N ^ 2 * P := by gcongr
  have hρ : (8 * N ^ 2 * P)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_iff₀ (by positivity : 0 < 8 * N ^ 2 * P)]
    simpa only [one_mul] using hM
  have hid : N ^ 3 * ((8 * N ^ 2 * P)⁻¹) ^ 2 = (64 * N * P ^ 2)⁻¹ := by
    field_simp
    ring
  have hsecond : N ^ 3 * ((8 * N ^ 2 * P)⁻¹) ^ 2 ≤ (16 * P ^ 2)⁻¹ := by
    rw [hid]
    apply inv_anti₀ (by positivity : 0 < 16 * P ^ 2)
    have h := mul_le_mul_of_nonneg_right hN (sq_nonneg P)
    nlinarith [sq_nonneg P]
  have hη : 0 ≤ (16 * P ^ 2)⁻¹ := by positivity
  have hproduct := mul_le_mul_of_nonneg_right hρ hη
  nlinarith

theorem repulsion_grid_error_le (n j : ℕ) :
    repulsionThreshold j + (repulsionMesh n j : ℝ)⁻¹ *
      (repulsionThreshold j + (n + 1 : ℝ) ^ 3 * (repulsionMesh n j : ℝ)⁻¹) ≤
        (1 / 4) * (1 / 8 : ℝ) ^ (2 * j) := by
  have hN : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hP : (1 : ℝ) ≤ (8 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have h := grid_error_le hN hP
  have hmesh : (repulsionMesh n j : ℝ) = 8 * (n + 1 : ℝ) ^ 2 * (8 : ℝ) ^ j := by
    simp only [repulsionMesh, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hpower : ((8 : ℝ) ^ j) ^ 2 = (8 : ℝ) ^ (2 * j) := by rw [← pow_mul, Nat.mul_comm]
  rw [hpower] at h
  rw [hmesh]
  change (16 * (8 : ℝ) ^ (2 * j))⁻¹ + (8 * (n + 1 : ℝ) ^ 2 * 8 ^ j)⁻¹ *
    ((16 * (8 : ℝ) ^ (2 * j))⁻¹ + (n + 1 : ℝ) ^ 3 * (8 * (n + 1 : ℝ) ^ 2 * 8 ^ j)⁻¹) ≤ _
  apply h.trans_eq
  rw [one_div_pow]
  ring

end Erdos521
