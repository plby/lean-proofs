import ErdosProblems.Erdos380.PrimeCounts

/-! # A fixed-factor comparison between dyadic prime pools -/

namespace Erdos380

theorem exists_dyadicPrimes_card_dilation_le : ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
    ∀ c : ℕ, 1 ≤ c → c ≤ N → (dyadicPrimes N).card ≤ 60 * (dyadicPrimes (c * N)).card := by
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp eventually_dyadicPrimes_card_bounds
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN c hc hcN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNN₁ : N₁ ≤ N := (le_max_right _ _).trans hN
  have hNc : N ≤ c * N := Nat.le_mul_of_pos_left _ (by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcR : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLc : 0 < Real.log (c * N : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c * N))
  have hlog : Real.log (c * N : ℕ) ≤ 2 * Real.log N := by
    rw [Nat.cast_mul, Real.log_mul hcR.ne' hNR.ne']
    have h := Real.log_le_log hcR (show (c : ℝ) ≤ N by exact_mod_cast hcN)
    linarith
  have hupper := (hN₁ N hNN₁).2
  have hlower := (hN₁ (c * N) (hNN₁.trans hNc)).1
  have hupper' : ((dyadicPrimes N).card : ℝ) * Real.log N ≤ 3 * N := by
    apply (le_div_iff₀ hL).mp
    simpa only [mul_div_assoc] using hupper
  have hlower' : (N : ℝ) ≤ 20 * ((dyadicPrimes (c * N)).card : ℝ) * Real.log N := by
    have h := (div_le_iff₀ hLc).mp
      (show ((c * N : ℕ) : ℝ) / Real.log (c * N : ℕ) ≤ 10 * (dyadicPrimes (c * N)).card by
        linarith)
    have hm := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ 10 * (dyadicPrimes (c * N)).card by positivity)
    have hNcR : (N : ℝ) ≤ (c * N : ℕ) := by exact_mod_cast hNc
    nlinarith
  have hcard : ((dyadicPrimes N).card : ℝ) ≤ 60 * (dyadicPrimes (c * N)).card := by
    apply le_of_mul_le_mul_right _ hL
    nlinarith
  exact_mod_cast hcard

theorem exists_dyadic_power_pool_comparison : ∃ d₀ : ℕ, ∀ d ≥ d₀,
    (dyadicPrimes (2 ^ d)).card ≤ 60 * (dyadicPrimes (2 ^ (d + 1))).card ∧
      (dyadicPrimes (2 ^ d)).card ≤ 60 * (dyadicPrimes (2 ^ (d + 2))).card := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_dyadicPrimes_card_dilation_le
  refine ⟨N₀, ?_⟩
  intro d hd
  have hdN : N₀ ≤ 2 ^ d := hd.trans (Nat.le_of_lt (show d < 2 ^ d from Nat.lt_two_pow_self))
  have hfour : 4 ≤ 2 ^ d := hN₀.trans hdN
  constructor
  · simpa only [pow_succ'] using hbound (2 ^ d) hdN 2 (by norm_num) (by omega)
  · have h := hbound (2 ^ d) hdN 4 (by norm_num) hfour
    convert h using 1
    rw [pow_add]
    norm_num
    ring

end Erdos380
