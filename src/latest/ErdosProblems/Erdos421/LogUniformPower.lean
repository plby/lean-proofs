import ErdosProblems.Erdos421.LogFrequencyCover
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Uniform power savings for logarithmic exponential sums -/

namespace Erdos421

/-- Choosing the integer shift cutoff as the floor of a small power of the
block length gives a uniform saving, including all shorter prefixes. -/
theorem logarithmicSum_uniform_power_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (R K : ℕ) (hK : 2 * R + 4 ≤ K) {τ : ℝ}
    (hlo : (M : ℝ) ^ (2 / (K : ℝ)) ≤ τ) (hhi : τ ≤ (M : ℝ) ^ (R + 1)) :
    (‖logarithmicSum M N τ‖ / (4 * M)) ^ (2 ^ R) ≤
      2 * logarithmicDifferenceConstant R / (M : ℝ) ^ ((K : ℝ)⁻¹) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hKn : K ≠ 0 := by omega
  have hKp : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hKn
  let q := (M : ℝ) ^ ((K : ℝ)⁻¹)
  have hq1 : 1 ≤ q := Real.one_le_rpow hM1 (by positivity)
  have hqp : 0 < q := by linarith
  let Q := ⌊q⌋₊
  have hQ : 0 < Q := (Nat.one_le_floor_iff _).mpr hq1
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQq : (Q : ℝ) ≤ q := Nat.floor_le hqp.le
  have hqQ : q ≤ 2 * Q := by
    have ht := Nat.lt_floor_add_one q
    change q < (Q : ℝ) + 1 at ht
    linarith
  have hpow : q ^ K = M := Real.rpow_inv_natCast_pow hMp.le hKn
  have hscale : (Q : ℝ) ^ (2 * R + 4) ≤ M := by
    calc
      _ ≤ (Q : ℝ) ^ K := pow_le_pow_right₀ hQ1 hK
      _ ≤ q ^ K := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQq _
      _ = _ := hpow
  have hlo' : (Q : ℝ) ^ 2 ≤ τ := by
    have hqeq : q ^ 2 = (M : ℝ) ^ (2 / (K : ℝ)) := by
      dsimp only [q]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hMp.le]
      congr 1
      simp only [Nat.cast_ofNat]
      ring
    exact (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQq 2).trans (hqeq ▸ hlo)
  have hhi' : τ ≤ (M : ℝ) ^ (R + 1) * (Q : ℝ) ^ 2 := by
    apply hhi.trans
    have hp := one_le_pow₀ hQ1 (n := 2)
    nlinarith [pow_pos hMp (R + 1)]
  have hb := logarithmicSum_frequency_cover_bound hM hN hQ R hscale hlo' hhi'
  apply hb.trans
  apply (div_le_div_iff₀ (by exact_mod_cast hQ) hqp).mpr
  have hc := logarithmicDifferenceConstant_pos R
  nlinarith

theorem logarithmicSum_norm_abs (M N : ℕ) (τ : ℝ) :
    ‖logarithmicSum M N |τ|‖ = ‖logarithmicSum M N τ‖ := by
  rcases le_or_gt 0 τ with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht, logarithmicSum_neg, Complex.norm_conj]

/-- The same estimate for either sign of the frequency. -/
theorem logarithmicSum_uniform_abs_power_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (R K : ℕ) (hK : 2 * R + 4 ≤ K) {τ : ℝ}
    (hlo : (M : ℝ) ^ (2 / (K : ℝ)) ≤ |τ|) (hhi : |τ| ≤ (M : ℝ) ^ (R + 1)) :
    (‖logarithmicSum M N τ‖ / (4 * M)) ^ (2 ^ R) ≤
      2 * logarithmicDifferenceConstant R / (M : ℝ) ^ ((K : ℝ)⁻¹) := by
  have h := logarithmicSum_uniform_power_bound hM hN R K hK hlo hhi
  rwa [logarithmicSum_norm_abs] at h

end Erdos421
