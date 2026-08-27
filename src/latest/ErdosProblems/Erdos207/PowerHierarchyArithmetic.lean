/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DyadicPowerScale

/-!
# Elementary arithmetic for the power hierarchy

These lemmas turn fixed coefficients and sums of lower powers into one higher
power of a sufficiently large common base.
-/

namespace Erdos207

open scoped NNReal

lemma coeff_mul_pow_le_pow
    {c t a b : ℕ} (ht : 1 ≤ t) (hc : c ≤ t) (hab : a + 1 ≤ b) :
    c * t ^ a ≤ t ^ b := by
  calc
    c * t ^ a ≤ t * t ^ a := Nat.mul_le_mul_right _ hc
    _ = t ^ (a + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ t ^ b := Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le ht) hab

lemma pow_add_coeff_mul_pow_le_pow
    {c t a b E : ℕ} (ht : 1 ≤ t) (hc : 1 + c ≤ t)
    (haE : a + 1 ≤ E) (hbE : b + 1 ≤ E) :
    t ^ a + c * t ^ b ≤ t ^ E := by
  let M := max a b
  have haM : a ≤ M := le_max_left _ _
  have hbM : b ≤ M := le_max_right _ _
  have hME : M + 1 ≤ E := by
    rw [← Nat.add_max_add_right]
    exact max_le haE hbE
  have hpowA : t ^ a ≤ t ^ M :=
    Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le ht) haM
  have hpowB : t ^ b ≤ t ^ M :=
    Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le ht) hbM
  calc
    t ^ a + c * t ^ b ≤ t ^ M + c * t ^ M :=
      Nat.add_le_add hpowA (Nat.mul_le_mul_left c hpowB)
    _ = (1 + c) * t ^ M := by ring
    _ ≤ t * t ^ M := Nat.mul_le_mul_right _ hc
    _ = t ^ (M + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ t ^ E := Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le ht) hME

lemma fixed_le_pow_of_fixed_le_base
    {c t a : ℕ} (hc : c ≤ t) (ha : 1 ≤ a) : c ≤ t ^ a := by
  exact hc.trans (Nat.le_pow ha)

lemma cast_le_inv_mul_of_mul_le
    {t x n : ℕ} (ht : 0 < t) (h : t * x ≤ n) :
    (x : ℝ≥0) ≤ (t : ℝ≥0)⁻¹ * (n : ℝ≥0) := by
  have htNN : (t : ℝ≥0) ≠ 0 := by exact_mod_cast ht.ne'
  calc
    (x : ℝ≥0) = (t : ℝ≥0)⁻¹ * ((t * x : ℕ) : ℝ≥0) := by
      rw [Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ htNN, one_mul]
    _ ≤ (t : ℝ≥0)⁻¹ * (n : ℝ≥0) := by
      gcongr

/-- Power version of `cast_le_inv_mul_of_mul_le`. -/
lemma cast_le_inv_pow_mul_of_pow_mul_le
    {t x n k : ℕ} (ht : 0 < t) (h : t ^ k * x ≤ n) :
    (x : ℝ≥0) ≤ (t : ℝ≥0)⁻¹ ^ k * (n : ℝ≥0) := by
  have htNN : (t : ℝ≥0) ≠ 0 := by exact_mod_cast ht.ne'
  calc
    (x : ℝ≥0) = (t : ℝ≥0)⁻¹ ^ k * ((t ^ k * x : ℕ) : ℝ≥0) := by
      push_cast
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ htNN, one_pow, one_mul]
    _ ≤ (t : ℝ≥0)⁻¹ ^ k * (n : ℝ≥0) := by
      gcongr

lemma inv_mul_cast_pow_eq_cast_pow_pred
    {t r : ℕ} (ht : 0 < t) (hr : 0 < r) :
    (t : ℝ≥0)⁻¹ * ((t ^ r : ℕ) : ℝ≥0) =
      ((t ^ (r - 1) : ℕ) : ℝ≥0) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simp only [Nat.succ_sub_one, pow_succ, Nat.cast_mul, Nat.cast_pow]
  have htNN : (t : ℝ≥0) ≠ 0 := by exact_mod_cast ht.ne'
  calc
    (t : ℝ≥0)⁻¹ * ((t : ℝ≥0) ^ r * (t : ℝ≥0)) =
        (t : ℝ≥0)⁻¹ * (t : ℝ≥0) * (t : ℝ≥0) ^ r := by ac_rfl
    _ = (t : ℝ≥0) ^ r := by rw [inv_mul_cancel₀ htNN, one_mul]

end Erdos207
