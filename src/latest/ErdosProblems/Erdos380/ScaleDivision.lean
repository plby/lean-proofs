import ErdosProblems.Erdos380.SmoothScaleUpper

/-! # Uniform smooth counts after integer division -/

open Filter
open scoped Topology

namespace Erdos380

lemma le_div_mul_scale_pow {N S d c : ℕ} (hS : 2 ≤ S) (hd : 0 < d)
    (hdS : d ≤ S ^ c) (hSN : S ^ c ≤ N) : N ≤ N / d * S ^ (c + 1) := by
  have hquot : 1 ≤ N / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdS.trans hSN)
  have hrem := Nat.mod_lt N hd
  have hdiv := Nat.div_add_mod N d
  have hfloor : N < (N / d + 1) * d := by nlinarith
  calc
    N ≤ (N / d + 1) * d := hfloor.le
    _ ≤ (2 * (N / d)) * d := by gcongr; omega
    _ ≤ (2 * (N / d)) * S ^ c := Nat.mul_le_mul_left _ hdS
    _ ≤ (S * (N / d)) * S ^ c := by gcongr
    _ = N / d * S ^ (c + 1) := by rw [pow_succ]; ring

theorem eventually_smoothCount_div_scale_upper {k r : ℕ} (hk : 0 < k)
    (hkr : k * r < 1000000) (c : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, 0 < d → d ≤ scaleBase N ^ c →
      (smoothCount (N / d) (scaleBase N ^ k) : ℝ) ≤
        (N : ℝ) / d / (scaleBase N : ℝ) ^ r := by
  filter_upwards [eventually_smoothCount_scale_upper hk hkr (c + 1),
    eventually_scaleBase_pow_le c, scaleBase_tendsto_atTop.eventually (eventually_ge_atTop 2)]
      with N hbound hSN hS
  intro d hd hdS
  have h := hbound (N / d) (Nat.div_le_self N d) (le_div_mul_scale_pow hS hd hdS hSN)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  exact h.trans (div_le_div_of_nonneg_right hdiv (by positivity))

lemma smoothCount_mono_cutoff {N a b : ℕ} (hab : a ≤ b) : smoothCount N a ≤ smoothCount N b := by
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnN, hn⟩ := Nat.mem_smoothNumbersUpTo.mp hn
  apply Nat.mem_smoothNumbersUpTo.mpr ⟨hnN, ?_⟩
  exact Nat.smoothNumbers_mono (by omega : a + 1 ≤ b + 1) hn

end Erdos380
