/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DyadicStageScale
import ErdosProblems.Erdos207.CrossScaleRegularizationScalars

/-! # Noncircular local analytic parameters on the common physical vortex scale -/

namespace Erdos207

open scoped NNReal

theorem source_stage_scaled_crude_cutoff
    (q z k c : ℕ) (hc : 1 ≤ c) (hk : 2 * z + 26 * q + 2 ≤ k) :
    2 * (z * c) + 2 * q * (5 * (2 * c) + 3) + 2 ≤ k * c := by
  have hm := Nat.mul_le_mul_right c hk
  have hconst := Nat.mul_le_mul_left (6 * q + 2) hc
  nlinarith only [hm, hconst]

theorem source_stage_density_scalars
    (t u p tau n C : ℝ≥0) (physical c d : ℕ)
    (ht : 8 ≤ t) (hu : 1 ≤ u) (hut : u ≤ t) (hb : 2 ≤ physical)
    (hd : physical + 1 ≤ d) (hpower : t ^ d ≤ u ^ c)
    (hpLo : 1 / t ^ physical ≤ p) (hpHi : p ≤ 2 / t ^ physical)
    (h24 : 24 ≤ tau * t) (hC : 2 * C ≤ tau * t) :
    1 / u ^ (2 * c) ≤ p ∧ p ≤ 1 / u ∧
      n / u ^ (2 * c) ≤ p ^ 2 * tau * n / 24 ∧
      n ^ 2 / u ^ (2 * c) ≤ p * n ^ 2 / 8 ∧
      C * u * p ≤ tau ∧ 2 / u ^ c ≤ 2 / t ^ d := by
  have ht1 : 1 ≤ t := (by norm_num : (1 : ℝ≥0) ≤ 8).trans ht
  have ht2 : 2 ≤ t := (by norm_num : (2 : ℝ≥0) ≤ 8).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hpower2 : t ^ (2 * d) ≤ u ^ (2 * c) := by
    simpa only [← pow_mul, Nat.mul_comm d 2, Nat.mul_comm c 2] using pow_le_pow_left' hpower 2
  have hpLower : 1 / u ^ (2 * c) ≤ p := by
    calc
      _ ≤ 1 / t ^ (2 * d) := one_div_le_one_div_of_le (pow_pos ht0 _) hpower2
      _ ≤ 1 / t ^ physical := one_div_le_one_div_of_le (pow_pos ht0 _)
        (pow_le_pow_right₀ ht1 (by omega))
      _ ≤ _ := hpLo
  have hpUpper : p ≤ 1 / u := by
    calc
      p ≤ 2 / t ^ physical := hpHi
      _ ≤ 2 / t ^ 2 := div_le_div_of_nonneg_left zero_le (pow_pos ht0 _)
        (pow_le_pow_right₀ ht1 hb)
      _ ≤ 1 / t := by
        apply (div_le_div_iff₀ (pow_pos ht0 2) ht0).mpr
        simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right ht2 zero_le
      _ ≤ _ := one_div_le_one_div_of_le hu0 hut
  refine ⟨hpLower, hpUpper, ?_, ?_, ?_, ?_⟩
  · exact crossScale_density_ratio_lower t u p tau n 24 physical (2 * c) (2 * d) 2
      ht1 (by norm_num) hpLo hpower2 (by omega) h24
  · have h := crossScale_density_ratio_lower t u p 1 (n ^ 2) 8 physical (2 * c) (2 * d) 1
      ht1 (by norm_num) hpLo hpower2 (by omega) (by simpa only [one_mul] using ht)
    simpa only [pow_one, mul_one] using h
  · exact crossScale_uniform_coefficient_small t u p C tau physical ht1 hb hut hpHi hC
  · exact div_le_div_of_nonneg_left zero_le (pow_pos ht0 _) hpower

theorem exists_source_stage_scale
    (q B z k Rmin D d : ℕ) (hmin : 1 ≤ Rmin) (hd : 1 ≤ d)
    (hk : 2 * z + 26 * q + 2 ≤ k)
    (hgap : ksssPowerDenominatorExponent q 2 B k Rmin * (d + 1) ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧
      2 * (z * c) + 2 * q * (5 * (2 * c) + 3) + 2 ≤ k * c ∧
      ∀ t n : ℕ, 1 ≤ t → t ^ D ≤ n → n ≤ t ^ (D + 1) → 2 ^ c ≤ t →
        let den := ksssPowerDenominatorExponent q (2 * c) B (k * c) (Rmin * c)
        let u := dyadicPowerScale den n
        u ^ den ≤ n ∧ 1 ≤ u ∧ u ≤ t ∧ t ^ d ≤ u ^ c ∧
          (∀ N R : ℕ, N ≤ t ^ R → N ≤ u ^ (c * R)) ∧
          (∀ T : ℕ, T ^ c ≤ t → T ≤ u) := by
  obtain ⟨c, hc, hdenLower, hdenGap⟩ := exists_scaled_ksss_stage_exponents q 2 B k Rmin D d hmin hgap
  refine ⟨c, hc, source_stage_scaled_crude_cutoff q z k c hc hk, ?_⟩
  intro t n ht hnLower hnUpper hround
  dsimp only
  let den := ksssPowerDenominatorExponent q (2 * c) B (k * c) (Rmin * c)
  let u := dyadicPowerScale den n
  have ht0 : 0 < t := Nat.zero_lt_one.trans_le ht
  have hn0 : n ≠ 0 := Nat.ne_of_gt ((pow_pos ht0 D).trans_le hnLower)
  have hdenPos : 0 < den := by dsimp only [den]; omega
  have hlow : t ^ d ≤ u ^ c := dyadicStageScale_cutoff_power_lower t n D den c d
    ht0 hdenPos hnLower hdenGap hround
  have htuc : t ≤ u ^ c := by
    calc
      t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ d := Nat.pow_le_pow_right ht0 hd
      _ ≤ _ := hlow
  refine ⟨dyadicPowerScale_pow_le hn0, one_le_dyadicPowerScale _ _,
    dyadicStageScale_le_base t n D den ht hn0 hdenLower hnUpper, hlow, ?_, ?_⟩
  · intro N R hN
    calc
      N ≤ t ^ R := hN
      _ ≤ (u ^ c) ^ R := Nat.pow_le_pow_left htuc R
      _ = _ := (pow_mul u c R).symm
  · intro T hT
    exact (Nat.pow_le_pow_iff_left (by omega : c ≠ 0)).mp (hT.trans htuc)

end Erdos207
