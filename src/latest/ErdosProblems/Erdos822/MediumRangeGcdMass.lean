/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.MediumAnchorMass

/-! # Unconditional medium-range gcd mass -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem eventually_sum_inv_gilCofactors_le_harmonic (S : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, (∑ m ∈ gilCofactors N S C, (1 : ℝ) / m) ≤ (harmonic N : ℝ) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_reciprocalPrimeIntervalSum_four_five_upper_one,
    eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_upper_one]
    with N hN hRone hQone
  have hR : (∑ r ∈ middlePrimes N, (1 : ℝ) / r) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff] using hRone
  have hQ : (∑ q ∈ largePrimes N, (1 : ℝ) / q) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, largePrimes_eq_primesLE_sdiff] using hQone
  have hHnonneg : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj ↦ by positivity
  calc
    _ ≤ ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m :=
      Finset.sum_le_sum_of_subset_of_nonneg (gilCofactors_subset_oddRaw N S C)
        (fun m hm hnot ↦ by positivity)
    _ = (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
      rw [sum_oddRawCofactors_eq_triple hN]
      simp only [mul_assoc]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro q hq
      push_cast
      ring
    _ ≤ (harmonic N : ℝ) * 1 * 1 :=
      mul_le_mul (mul_le_mul (sum_inv_oddSmallFactors_le_harmonic N) hR
        (by positivity) hHnonneg) hQ (by positivity) (by positivity)
    _ = _ := by ring

theorem b1Cutoff_lt_pow_twentyone {N : ℕ} (hN : 2 ≤ N) : b1Cutoff N < N ^ 21 := by
  have hy : b1Cutoff N ≤ N :=
    (nthRoot_le_self_of_pos (by norm_num : 0 < 4)).trans
      ((Nat.log_le_self 2 (Nat.log 2 N)).trans (Nat.log_le_self 2 N))
  have hpow : N ^ 1 < N ^ 21 := Nat.pow_lt_pow_right (by omega) (by omega)
  exact hy.trans_lt (by simpa using hpow)

theorem eventually_sum_mediumGcdAnchorTerm_le (S : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m' ∈ gilCofactors N S C, ∑ m ∈ gilCofactors N S C,
        mediumGcdAnchorTerm N m m' / m') ≤ 4 := by
  filter_upwards [eventually_ge_atTop 2, tendsto_b1Cutoff_atTop.eventually_ge_atTop 1,
    eventually_gil_roughWeight_mul_harmonic_four_le S C,
    eventually_sum_inv_gilCofactors_le_harmonic S C] with N hN hy hW hmass
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hHpos : 0 < (harmonic N : ℝ) := by
    apply lt_of_lt_of_le _ (log_add_one_le_harmonic N)
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < N + 1))
  have hanchor (m' : ℕ) (hm' : m' ∈ gilCofactors N S C) :
      (∑ m ∈ gilCofactors N S C, mediumGcdAnchorTerm N m m') ≤ 4 / (harmonic N : ℝ) := by
    have hbase := sum_mediumGcdAnchorTerm_le hN hy (b1Cutoff_lt_pow_twentyone hN) hm'
    apply hbase.trans
    apply (le_div_iff₀ hHpos).mpr
    have hW' := hW m' hm'
    calc
      _ = 4 * ((5 : ℝ) ^ (roughPart (shiftedTotient m') (b1Cutoff N)).primeFactors.card *
          (harmonic N : ℝ) ^ 4) / N := by ring
      _ ≤ 4 * (N : ℝ) / N := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hW' (by norm_num)) hNR.le
      _ = 4 := by field_simp
  calc
    _ = ∑ m' ∈ gilCofactors N S C,
        (∑ m ∈ gilCofactors N S C, mediumGcdAnchorTerm N m m') / m' := by
      simp only [Finset.sum_div]
    _ ≤ ∑ m' ∈ gilCofactors N S C, (4 / (harmonic N : ℝ)) / m' :=
      Finset.sum_le_sum fun m' hm' ↦ div_le_div_of_nonneg_right (hanchor m' hm') (by positivity)
    _ = (4 / (harmonic N : ℝ)) * ∑ m' ∈ gilCofactors N S C, (1 : ℝ) / m' := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m' hm'
      ring
    _ ≤ (4 / (harmonic N : ℝ)) * (harmonic N : ℝ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 4 := by field_simp

#print axioms eventually_sum_mediumGcdAnchorTerm_le

end Erdos822
