import ErdosProblems.Erdos964.LogPowerAbel
import BoundedGaps.Maynard.CoprimeHarmonicGlobalBound

/-!
# Logarithmic moments at arbitrary real endpoints

The floor correction is bounded by the density, since the logarithmic
gap between a real endpoint and its natural floor is at most `log 2 < 1`.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem log_power_weighted_abel_real_error (c : ℕ → ℝ) (hc : c 0 = 0)
    (S E : ℝ) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (happrox : ∀ t : ℝ, 1 ≤ t → |abelCumulative c t - S * Real.log t| ≤ E)
    (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    |(∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log x - Real.log n) ^ k * c n) -
      S / (k + 1) * (Real.log x) ^ (k + 1)| ≤ (E + S) * (1 + Real.log x) ^ k := by
  let Q := ⌊x⌋₊
  let L := Real.log x
  let q := Real.log (Q : ℝ)
  have hQ : 1 ≤ Q := (Nat.one_le_floor_iff x).mpr hx
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hqL : q ≤ L := Real.log_le_log hQpos (Nat.floor_le hxpos.le)
  have hL : 0 ≤ L := Real.log_nonneg hx
  have hgap : 0 ≤ L - q ∧ L - q ≤ 1 := by
    have hfloor := abs_log_natFloor_sub_log_le_log_two_global hx
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hdiff : |q - L| = L - q := by rw [abs_of_nonpos (sub_nonpos.mpr hqL)]; ring
    change |q - L| ≤ Real.log 2 at hfloor
    rw [hdiff] at hfloor
    exact ⟨sub_nonneg.mpr hqL, hfloor.trans hlog2⟩
  have hAbel := log_power_weighted_abel_error Q hQ c hc S E L hE hqL k
    (fun t ht => happrox t ht.1)
  have hkn : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hden : 0 ≤ S / ((k : ℝ) + 1) := by positivity
  have htail : |S / ((k : ℝ) + 1) * (L ^ (k + 1) - (L - q) ^ (k + 1)) -
      S / ((k : ℝ) + 1) * L ^ (k + 1)| ≤ S := by
    rw [show S / ((k : ℝ) + 1) * (L ^ (k + 1) - (L - q) ^ (k + 1)) -
        S / ((k : ℝ) + 1) * L ^ (k + 1) =
        -(S / ((k : ℝ) + 1) * (L - q) ^ (k + 1)) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg hden (pow_nonneg hgap.1 _))]
    calc
      _ ≤ S / ((k : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hgap.1 hgap.2) hden
      _ ≤ S := by rw [mul_one]; exact div_le_self hS hkn
  have htotal := (abs_sub_le
    (∑ n ∈ Finset.Icc 0 Q, (L - Real.log n) ^ k * c n)
    (S / ((k : ℝ) + 1) * (L ^ (k + 1) - (L - q) ^ (k + 1)))
    (S / ((k : ℝ) + 1) * L ^ (k + 1))).trans (add_le_add hAbel htail)
  have hpow : L ^ k ≤ (1 + L) ^ k := pow_le_pow_left₀ hL (by linarith) k
  have hone : 1 ≤ (1 + L) ^ k := one_le_pow₀ (by linarith : 1 ≤ 1 + L)
  calc
    _ ≤ E * L ^ k + S := htotal
    _ ≤ (E + S) * (1 + L) ^ k := by
      nlinarith [mul_le_mul_of_nonneg_left hpow hE, mul_le_mul_of_nonneg_left hone hS]
    _ = _ := rfl

end Erdos964
