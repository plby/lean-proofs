import ErdosProblems.Erdos587.HooleyWeightedSieve
import ErdosProblems.Erdos587.HooleyGrowth
import ErdosProblems.Erdos587.HooleyHarmonicMean

/-!
# Delta means on the uniformly rough-cofactor range

Factor covers are converted to the signed quotient fibers of the sieve.
The uniformly rough range is then bounded with no logarithmic loss beyond
the totient ratio and the fifth log-log power in the harmonic mean.
-/

open scoped BigOperators

namespace Erdos587

theorem delta_weighted_factor_sieve_le {A B : ℤ} (hB : B ≠ 0)
    (hAB : IsCoprime A B) {Q Y : ℕ} (hQ : 0 < Q) (S D : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Y) (hD : ∀ d ∈ D, 0 < d)
    (hcut : ∀ d ∈ D, d * Q ^ 2 ≤ Y) {K : ℝ} (hK : 0 ≤ K)
    (hcover : ∀ n ∈ S, ∃ d ∈ D, ∃ b : ℕ, 0 < b ∧ (A + B * n).natAbs = d * b ∧
      (∀ p ∈ b.primeFactors, Q < p) ∧ (b.divisors.card : ℝ) ≤ K) :
    (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
      3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) *
        K * ∑ d ∈ D, (hooleyDelta d : ℝ) / d := by
  apply delta_weighted_divisor_sieve_le hB hAB hQ S D hS hD hcut hK
  intro n hn
  obtain ⟨d, hd, b, hb, hfactor, hrough, hweight⟩ := hcover n hn
  have hdiv : (d : ℤ) ∣ A + B * n :=
    Int.natCast_dvd.mpr ⟨b, hfactor⟩
  have hquot : ((A + B * n) / d).natAbs = b := by
    apply Nat.eq_of_mul_eq_mul_left (hD d hd)
    rw [← delta_natAbs_divisor_factor hdiv, hfactor]
  refine ⟨d, hd, hdiv, ?_, ?_⟩
  · intro p hp hpQ hpdiv
    have hpdivb : p ∣ b := by
      rw [← hquot]
      exact Int.natCast_dvd.mp hpdiv
    have hpbin := Nat.mem_primeFactors.mpr ⟨hp, hpdivb, hb.ne'⟩
    exact (not_le_of_gt (hrough p hpbin)) hpQ
  · apply delta_affine_cofactor_bound hdiv
    rwa [hquot]

theorem delta_main_sieve_range_le {A B : ℤ} (hB : B ≠ 0) (hAB : IsCoprime A B)
    {R N Y k : ℕ} (hR : 1 ≤ R) (hRY : R ^ 4 ≤ Y) (hN : N ≤ (R + 1) ^ k)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Y)
    (hvalues : ∀ n ∈ S, (A + B * n).natAbs ≤ N)
    (hcover : ∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
      0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧ ∀ p ∈ b.primeFactors, R < p) :
    (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
      3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (R + 1 : ℕ) *
        (2 : ℝ) ^ k * ∑ d ∈ Finset.Icc 1 N, (hooleyDelta d : ℝ) / d := by
  let D := Finset.Icc 1 (min (R ^ 2) N)
  have hbound := delta_weighted_factor_sieve_le (K := (2 : ℝ) ^ k) hB hAB hR S D hS
    (fun d hd => (Finset.mem_Icc.mp hd).1) (fun d hd => show d * R ^ 2 ≤ Y from by
      have hdR := (le_min_iff.mp (Finset.mem_Icc.mp hd).2).1
      calc
        _ ≤ R ^ 2 * R ^ 2 := Nat.mul_le_mul_right _ hdR
        _ = R ^ 4 := by ring
        _ ≤ Y := hRY) (by positivity)
  have hcoverD : ∀ n ∈ S, ∃ d ∈ D, ∃ b : ℕ, 0 < b ∧ (A + B * n).natAbs = d * b ∧
      (∀ p ∈ b.primeFactors, R < p) ∧ (b.divisors.card : ℝ) ≤ (2 : ℝ) ^ k := by
    intro n hn
    obtain ⟨a, b, hfactor, ha, hb, haR, hrough⟩ := hcover n hn
    have haN : a ≤ N := by nlinarith [hvalues n hn]
    have hbN : b ≤ N := by nlinarith [hvalues n hn]
    refine ⟨a, Finset.mem_Icc.mpr ⟨ha, le_min haR haN⟩, b, hb, hfactor, hrough, ?_⟩
    have hdiv := card_divisors_rough_le (P := R + 1) (X := N) (r := 1) (K := k)
      (by omega) hb.ne' (fun p hp => hrough p hp) hN (by simpa using hbN)
    simpa only [mul_one] using
      (show (b.divisors.card : ℝ) ≤ (2 : ℝ) ^ (k * 1) by exact_mod_cast hdiv)
  have hDsub : D ⊆ Finset.Icc 1 N := by
    intro d hd
    obtain ⟨hd1, hdmax⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨hd1, (le_min_iff.mp hdmax).2⟩
  exact (hbound hcoverD).trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg hDsub (fun d _ _ => by positivity)) (by
      have hlog : 0 < Real.log (R + 1 : ℕ) :=
        Real.log_pos (by exact_mod_cast (show 1 < R + 1 by omega))
      positivity))

/-- The main range already has the desired log-log exponent, before
absorbing the slope's totient ratio. -/
theorem exists_delta_main_sieve_loglog_bound (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ), B ≠ 0 → IsCoprime A B →
      ∀ R N Y : ℕ, 1 ≤ R → 2 ≤ N → R ^ 4 ≤ Y → N ≤ (R + 1) ^ k →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Y →
      (∀ n ∈ S, (A + B * n).natAbs ≤ N) →
      (∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
        0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧ ∀ p ∈ b.primeFactors, R < p) →
      (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
        C * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 := by
  obtain ⟨C₀, hC₀, hmean⟩ := exists_hooleyDelta_harmonic_loglog_bound
  refine ⟨3 * (2 : ℝ) ^ k * C₀ * k, by positivity, ?_⟩
  intro A B hB hAB R N Y hR hN hRY hRN S hS hvalues hcover
  have hlogR : 0 < Real.log (R + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R + 1 by omega))
  have hlogN : Real.log (N : ℝ) ≤ (k : ℝ) * Real.log (R + 1 : ℕ) := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < N by omega))
      (show (N : ℝ) ≤ ((R + 1 : ℕ) : ℝ) ^ k by exact_mod_cast hRN)
    rwa [Real.log_pow] at h
  have hratio : Real.log (N : ℝ) / Real.log (R + 1 : ℕ) ≤ k :=
    (div_le_iff₀ hlogR).mpr hlogN
  calc
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (R + 1 : ℕ) *
        (2 : ℝ) ^ k * ∑ d ∈ Finset.Icc 1 N, (hooleyDelta d : ℝ) / d :=
      delta_main_sieve_range_le hB hAB hR hRY hRN S hS hvalues hcover
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (R + 1 : ℕ) *
        (2 : ℝ) ^ k * (C₀ * Real.log (N : ℝ) * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) :=
      mul_le_mul_of_nonneg_left (hmean N hN) (by positivity)
    _ = (3 * (2 : ℝ) ^ k * C₀ * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
        (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) *
          (Real.log (N : ℝ) / Real.log (R + 1 : ℕ)) := by ring
    _ ≤ (3 * (2 : ℝ) ^ k * C₀ * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
        (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) * k :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end Erdos587
