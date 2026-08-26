import ErdosProblems.Erdos856b.UpperFiber

/-! # Exponential bounds for the upper divisor fibers -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

/-- The cosunflower pressure, defined by its proved uniform-layer formula. -/
noncomputable def cosPressure (k : ℕ) (z : ℝ) : ℝ := exp (logPressure k z)

/-- The complementary (sunflower) pressure from the weighted duality. -/
noncomputable def sunflowerPressure (k : ℕ) (z : ℝ) : ℝ :=
  z * cosPressure k (1 / z)

theorem sunflowerPressure_pos (k : ℕ) {z : ℝ} (hz : 0 < z) :
    0 < sunflowerPressure k z := mul_pos hz (exp_pos _)

theorem uniformLog_zero {k : ℕ} (hk : 3 ≤ k) (z : ℝ) : uniformLog k 0 z = 0 := by
  simp [uniformLog, M_rank_zero hk]

theorem C_le_pressure {k : ℕ} (hk : 3 ≤ k) (n : ℕ) {z : ℝ} (hz : 0 < z) :
    C k n z ≤ (n + 1) * cosPressure k z ^ n := by
  have hU : uniformLog k n z ≤ n * logPressure k z := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [uniformLog_zero hk]
    · exact uniformLog_le_mul_logPressure hk hn hz
  apply (C_le_exp_uniformLog hk hz).trans
  dsimp [cosPressure]
  rw [← exp_nat_mul]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hU) (by positivity)

theorem dual_C_le_pressure {k : ℕ} (hk : 3 ≤ k) (n : ℕ) {z : ℝ} (hz : 0 < z) :
    z ^ n * C k n (1 / z) ≤ (n + 1) * sunflowerPressure k z ^ n := by
  have h := mul_le_mul_of_nonneg_left (C_le_pressure hk n (one_div_pos.mpr hz))
    (pow_nonneg hz.le n)
  simpa only [sunflowerPressure, mul_pow, mul_left_comm] using h

theorem polynomial_mul_pow_bound {B u : ℝ} (hB : 0 < B) (hu : B < u) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, (n + 1) * B ^ n ≤ K * u ^ n := by
  let d := (u - B) / B
  have hd : 0 < d := div_pos (sub_pos.mpr hu) hB
  let K := max 1 d⁻¹
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKd : 1 ≤ K * d := by
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 d⁻¹) hd.le
    simpa only [inv_mul_cancel₀ hd.ne'] using h
  have hid : (1 + d) * B = u := by
    dsimp [d]
    field_simp
    ring
  refine ⟨K, zero_lt_one.trans_le hK1, ?_⟩
  intro n
  have hbern := one_add_mul_le_pow (by linarith : -2 ≤ d) n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlin : (n : ℝ) + 1 ≤ K * (1 + n * d) := by
    nlinarith [mul_le_mul_of_nonneg_left hKd hn]
  calc
    (n + 1) * B ^ n ≤ (K * (1 + d) ^ n) * B ^ n := by
      exact mul_le_mul_of_nonneg_right
        (hlin.trans (mul_le_mul_of_nonneg_left hbern (zero_le_one.trans hK1)))
        (pow_nonneg hB.le _)
    _ = K * u ^ n := by rw [mul_assoc, ← mul_pow, hid]

theorem dual_C_le_pow {k : ℕ} (hk : 3 ≤ k) {z u : ℝ} (hz : 0 < z)
    (hu : sunflowerPressure k z < u) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, z ^ n * C k n (1 / z) ≤ K * u ^ n := by
  obtain ⟨K, hK, hbound⟩ := polynomial_mul_pow_bound (sunflowerPressure_pos k hz) hu
  exact ⟨K, hK, fun n => (dual_C_le_pressure hk n hz).trans (hbound n)⟩

theorem f_mul_kernel_le_exp {k : ℕ} (hk : 3 ≤ k) {z u : ℝ} (hz : 0 < z)
    (hu : sunflowerPressure k z < u) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      f k N * squarefreeKernel z N ≤ K * exp (u * (primeHarmonic (N ^ 2 : ℕ) + 1)) := by
  obtain ⟨K, hK, hbound⟩ := dual_C_le_pow hk hz hu
  refine ⟨K, hK, fun N => (f_mul_kernel_le hk N hz).trans ?_⟩
  have hu0 : 0 ≤ u := (sunflowerPressure_pos k hz).le.trans hu.le
  calc
    (∑ m ∈ Finset.Icc 1 (N ^ 2),
        (z ^ m.primeFactors.card * C k m.primeFactors.card (1 / z)) / m) ≤
        K * omegaSum u (N ^ 2) := by
      rw [omegaSum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m _
      simpa only [omegaWeight, mul_div_assoc] using
        div_le_div_of_nonneg_right (hbound m.primeFactors.card) (Nat.cast_nonneg m)
    _ ≤ K * exp (u * (primeHarmonic (N ^ 2 : ℕ) + 1)) :=
      mul_le_mul_of_nonneg_left (omegaSum_le_exp hu0 _) hK.le

end Erdos856b
