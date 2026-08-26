import ErdosProblems.Erdos69.RoughSizeBounds
import ErdosProblems.Erdos69.CompositeTails

/-! # Pointwise logarithmic control of the omitted binary tail -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem omega_affine_le_log_add (n a b h : ℕ) (ha : 0 < a) :
    (omegaCount (n + a * h - b) : ℝ) ≤ Real.log (n + a : ℕ) / Real.log 2 + h := by
  have hna : 0 < n + a := by omega
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog0 : 0 ≤ Real.log (n + a : ℕ) := Real.log_nonneg (by exact_mod_cast hna)
  by_cases hz : n + a * h - b = 0
  · rw [hz, omegaCount_zero, Nat.cast_zero]
    positivity
  have hpos : 0 < n + a * h - b := by omega
  have hpow : h + 1 ≤ 2 ^ h := Nat.lt_two_pow_self
  have hle : n + a * h - b ≤ (n + a) * 2 ^ h := by
    calc
      _ ≤ n + a * h := Nat.sub_le _ _
      _ ≤ (n + a) * (h + 1) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ hpow
  have hlog := Real.log_le_log (by exact_mod_cast hpos : (0 : ℝ) < ((n + a * h - b : ℕ) : ℝ))
    (by exact_mod_cast hle : ((n + a * h - b : ℕ) : ℝ) ≤ (n + a : ℕ) * (2 : ℝ) ^ h)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have hw := omegaCount_mul_log_two_le hpos
  have hfinal : (omegaCount (n + a * h - b) : ℝ) * Real.log 2 ≤
      Real.log (n + a : ℕ) + h * Real.log 2 := hw.trans hlog
  calc
    _ ≤ (Real.log (n + a : ℕ) + h * Real.log 2) / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr hfinal
    _ = _ := by field_simp

theorem hasSum_index_binary_weights :
    HasSum (fun k : ℕ ↦ (k : ℝ) / 2 ^ (k + 1)) 1 := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num)).div_const 2
  convert! h using 1
  · funext k
    simp only [pow_succ, div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow]
    ring
  · norm_num

theorem hasSum_linear_binary_tail (C : ℝ) (L : ℕ) :
    HasSum (fun k : ℕ ↦ (C + L + 1 + k) / 2 ^ (L + 1 + k))
      ((C + L + 2) / 2 ^ L) := by
  have hc : HasSum (fun k : ℕ ↦ (C + L + 1) / 2 ^ (k + 1)) (C + L + 1) := by
    simpa only [tsum_constant_binary_weights] using
      (summable_constant_binary_weights (C + L + 1)).hasSum
  have h := (hc.add hasSum_index_binary_weights).mul_left ((1 : ℝ) / 2 ^ L)
  convert! h using 1
  · funext k
    rw [show L + 1 + k = L + (k + 1) by omega, pow_add]
    ring
  · ring

theorem summable_omega_affine_tail (n a b L : ℕ) (ha : 0 < a) :
    Summable (fun k : ℕ ↦ (omegaCount (n + a * (L + 1 + k) - b) : ℝ) /
      2 ^ (L + 1 + k)) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _
    (hasSum_linear_binary_tail (Real.log (n + a : ℕ) / Real.log 2) L).summable
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := omega_affine_le_log_add n a b (L + 1 + k) ha
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h

theorem omega_affine_tail_le (n a b L : ℕ) (ha : 0 < a) :
    (∑' k : ℕ, (omegaCount (n + a * (L + 1 + k) - b) : ℝ) / 2 ^ (L + 1 + k)) ≤
      (Real.log (n + a : ℕ) / Real.log 2 + L + 2) / 2 ^ L := by
  rw [← (hasSum_linear_binary_tail (Real.log (n + a : ℕ) / Real.log 2) L).tsum_eq]
  apply Summable.tsum_le_tsum _ (summable_omega_affine_tail n a b L ha)
    (hasSum_linear_binary_tail _ _).summable
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := omega_affine_le_log_add n a b (L + 1 + k) ha
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h

end Erdos69.Elementary
