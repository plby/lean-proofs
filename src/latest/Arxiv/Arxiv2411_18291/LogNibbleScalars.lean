import Arxiv.Arxiv2411_18291.LogNibbleComparisons

/-! # Small-clique margins for logarithmic tracking above five halves of the leave -/

namespace Arxiv2411_18291

theorem log_nibble_coefficient_bounds {k : ℕ} (hk : 3 ≤ k) (hk5 : k ≤ 5) :
    27 * (2 / 5 : ℝ) ^ (k * 2) ≤ 1 / 8 ∧
      12 * k * (2 / 5 : ℝ) ^ k ≤ 5 / 2 ∧
      12 * k * (2 / 5 : ℝ) ^ (k * 3) ≤ 1 / 64 ∧
      3 * k * (2 / 5 : ℝ) ^ k ≤ 3 / 4 ∧
      12 * k * (2 / 5 : ℝ) ^ (k * 2) ≤ 1 / 4 := by
  have hcases : k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hcases with rfl | rfl | rfl <;> norm_num

structure LogNibbleScalarConditions (k : ℕ) (a p : ℝ) : Prop where
  degree : 3 * nibbleLogFactor k p * a ^ 2 ≤ p ^ (k - 1) / 8
  degree_sq : 9 * (nibbleLogFactor k p) ^ 2 * a ^ 2 ≤ p ^ (k - 1) / 8
  count : 4 * k * (nibbleLogFactor k p) ^ 2 * a ^ 3 ≤ p ^ k / 64
  coupling : 4 * k * (nibbleLogFactor k p) ^ 2 * a ≤ 5 / 2 * p
  face_degree : 3 * nibbleLogFactor k p * a ≤ 3 / 4 * p ^ (k - 1)
  face_count : 4 * k * (nibbleLogFactor k p) ^ 2 * a ^ 2 ≤ p ^ k / 4

theorem log_nibble_scalar_conditions {k : ℕ} (hk : 3 ≤ k) (hk5 : k ≤ 5)
    {a p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ a)
    (hac : a ≤ ((2 / 5 : ℝ) * p) ^ k) : LogNibbleScalarConditions k a p := by
  have hac' : a ≤ (2 / 5 : ℝ) ^ k * p ^ k := by simpa only [mul_pow] using hac
  have hL := nibbleLogFactor_one_le k hp hp1
  have hL0 : 0 ≤ nibbleLogFactor k p := by linarith only [hL]
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  obtain ⟨hc2, hc1, hc3, hcfE, hcfC⟩ := log_nibble_coefficient_bounds hk hk5
  have hb2 := nibbleLogFactor_weighted_power (j := 2) (t := k - 1) hk
    (by omega) hp hp1 ha (by norm_num : (0 : ℝ) ≤ 2 / 5) hac'
  have hb2' := mul_le_mul_of_nonneg_left hb2 (by norm_num : (0 : ℝ) ≤ 9)
  have hc2' := mul_le_mul_of_nonneg_right hc2 (pow_nonneg hp.le (k - 1))
  have hsq : 9 * (nibbleLogFactor k p) ^ 2 * a ^ 2 ≤ p ^ (k - 1) / 8 := by
    nlinarith only [hb2', hc2']
  refine ⟨?_, hsq, ?_, ?_, ?_, ?_⟩
  · have hh : 3 * nibbleLogFactor k p ≤ 9 * (nibbleLogFactor k p) ^ 2 := by
      nlinarith only [hL]
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg a)
    exact hh'.trans hsq
  · have hb := nibbleLogFactor_weighted_power (j := 3) (t := k) hk
      (by omega) hp hp1 ha (by norm_num : (0 : ℝ) ≤ 2 / 5) hac'
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * (k : ℝ) by positivity)
    have hc' := mul_le_mul_of_nonneg_right hc3 (pow_nonneg hp.le k)
    nlinarith only [hb', hc']
  · have hb := nibbleLogFactor_weighted_power (j := 1) (t := 1) hk
      (by omega) hp hp1 ha (by norm_num : (0 : ℝ) ≤ 2 / 5) hac'
    simp only [pow_one, mul_one] at hb
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * (k : ℝ) by positivity)
    have hc' := mul_le_mul_of_nonneg_right hc1 hp.le
    nlinarith only [hb', hc']
  · have hLp := nibbleLogFactor_mul_le_rank (by omega : 1 ≤ k) hp
    have hpow : p ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
    calc
      _ ≤ 3 * nibbleLogFactor k p * ((2 / 5 : ℝ) ^ k * p ^ k) :=
        mul_le_mul_of_nonneg_left hac' (by positivity)
      _ = 3 * (2 / 5 : ℝ) ^ k *
          (nibbleLogFactor k p * p) * p ^ (k - 1) := by rw [hpow]; ring
      _ ≤ 3 * (2 / 5 : ℝ) ^ k * k * p ^ (k - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLp (by positivity)) (pow_nonneg hp.le _)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hcfE (pow_nonneg hp.le (k - 1))
        nlinarith only [hh]
  · have hb := nibbleLogFactor_weighted_power (j := 2) (t := k) hk
      (by omega) hp hp1 ha (by norm_num : (0 : ℝ) ≤ 2 / 5) hac'
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * (k : ℝ) by positivity)
    have hc' := mul_le_mul_of_nonneg_right hcfC (pow_nonneg hp.le k)
    nlinarith only [hb', hc']

end Arxiv2411_18291
