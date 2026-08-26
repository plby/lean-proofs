/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlowCutoffB4Mass
import ErdosProblems.Erdos822.SlowCutoffAsymptotic
import ErdosProblems.Erdos822.PrimeReciprocalUpper
import ErdosProblems.Erdos822.HarmonicElementary

/-!
# Retained reciprocal mass after the genuine slow-cutoff B4 deletion
-/

namespace Erdos822

open scoped BigOperators

/-- Once the two prime-layer reciprocal sums are at most one, all four B4
failure channels are bounded by one cubic logarithmic envelope. -/
theorem sum_inv_slowCutoffBadOddCofactors_le_log_envelope
    {N y : ℕ} (hN : 2 ≤ N) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hR : ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤ 1)
    (hQ : ∑ q ∈ largePrimes N, (1 : ℝ) / q ≤ 1) :
    ∑ m ∈ slowCutoffBadOddCofactors N y, (1 : ℝ) / m ≤
      12 * (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) := by
  let A : ℝ := 1 + Real.log (N : ℝ)
  let H : ℝ := (harmonic N : ℝ)
  let L : ℝ := Nat.log 2 N
  let K : ℝ := ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k
  let R : ℝ := ∑ r ∈ middlePrimes N, (1 : ℝ) / r
  let Q : ℝ := ∑ q ∈ largePrimes N, (1 : ℝ) / q
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hH0 : 0 ≤ H := by
    dsimp [H]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Finset.sum_nonneg fun k hk => by positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun r hr => by positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg fun q hq => by positivity
  have hL0 : 0 ≤ L := by positivity
  have hyR : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hHA : H ≤ A := by
    dsimp [H, A]
    exact harmonic_le_one_add_log N
  have hKA : K ≤ A := by
    exact (sum_inv_oddSmallFactors_le_harmonic N).trans hHA
  have hL2A : L ≤ 2 * A := by
    have h := natLog_two_le_two_realLog (show 1 ≤ N by omega)
    dsimp [L, A]
    linarith
  have hyN4 : y ≤ N ^ 4 :=
    hyN.trans (Nat.le_pow (by omega : 0 < 4))
  have hyN21 : y ≤ N ^ 21 :=
    hyN.trans (Nat.le_pow (by omega : 0 < 21))
  have hinv4 : (1 : ℝ) / (N ^ 4 : ℕ) ≤ (1 : ℝ) / y := by
    apply one_div_le_one_div_of_le hyR
    exact_mod_cast hyN4
  have hinv21 : (1 : ℝ) / (N ^ 21 : ℕ) ≤ (1 : ℝ) / y := by
    apply one_div_le_one_div_of_le hyR
    exact_mod_cast hyN21
  have hLy : L / (y : ℝ) ≤ 2 * A / (y : ℝ) := by
    exact div_le_div_of_nonneg_right hL2A hyR.le
  have hL4 : L / ((N ^ 4 : ℕ) : ℝ) ≤ 2 * A / (y : ℝ) := by
    calc
      L / ((N ^ 4 : ℕ) : ℝ) = L * ((1 : ℝ) / (N ^ 4 : ℕ)) := by ring
      _ ≤ L * ((1 : ℝ) / y) := mul_le_mul_of_nonneg_left hinv4 hL0
      _ ≤ (2 * A) * ((1 : ℝ) / y) :=
        mul_le_mul_of_nonneg_right hL2A (by positivity)
      _ = 2 * A / (y : ℝ) := by ring
  have hL21 : L / ((N ^ 21 : ℕ) : ℝ) ≤ 2 * A / (y : ℝ) := by
    calc
      L / ((N ^ 21 : ℕ) : ℝ) = L * ((1 : ℝ) / (N ^ 21 : ℕ)) := by ring
      _ ≤ L * ((1 : ℝ) / y) := mul_le_mul_of_nonneg_left hinv21 hL0
      _ ≤ (2 * A) * ((1 : ℝ) / y) :=
        mul_le_mul_of_nonneg_right hL2A (by positivity)
      _ = 2 * A / (y : ℝ) := by ring
  have hAA2 : A ≤ A ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hA1 hA0
    simpa [pow_two] using h
  have hA2A3 : A ^ 2 ≤ A ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hA1 (sq_nonneg A)
    simpa [pow_two, pow_succ] using h
  have hch1 :
      ∑ m ∈ slowInternalTotientCofactors N y, (1 : ℝ) / m ≤
        2 * A ^ 3 / (y : ℝ) := by
    calc
      (∑ m ∈ slowInternalTotientCofactors N y, (1 : ℝ) / m) ≤
          (H / y + H ^ 2 / y) * R * Q := by
        simpa [H, R, Q] using sum_inv_slowInternalTotientCofactors_le hN hy
      _ ≤ (H / y + H ^ 2 / y) * 1 * 1 := by gcongr
      _ = H / y + H ^ 2 / y := by ring
      _ ≤ (A / y + A ^ 2 / y) := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right hHA hyR.le
        · exact div_le_div_of_nonneg_right
            (by simpa [pow_two] using mul_self_le_mul_self hH0 hHA) hyR.le
      _ ≤ A ^ 3 / y + A ^ 3 / y := by
        exact add_le_add
          (div_le_div_of_nonneg_right (hAA2.trans hA2A3) hyR.le)
          (div_le_div_of_nonneg_right hA2A3 hyR.le)
      _ = 2 * A ^ 3 / (y : ℝ) := by ring
  have hch2 :
      ∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m ≤
        4 * A ^ 3 / (y : ℝ) := by
    calc
      (∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m) ≤
          K * (((L / y + L / (N ^ 4 : ℕ)) * H) * Q) := by
        simpa [K, L, H, Q] using
          sum_inv_slowSmallMiddlePredCofactors_le_endpoint hN hy
      _ ≤ A * ((((2 * A / y) + (2 * A / y)) * A) * 1) := by
        gcongr
      _ = 4 * A ^ 3 / (y : ℝ) := by ring
  have hch3 :
      ∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m ≤
        4 * A ^ 3 / (y : ℝ) := by
    calc
      (∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m) ≤
          K * (R * ((L / y + L / (N ^ 21 : ℕ)) * H)) := by
        simpa [K, R, L, H] using
          sum_inv_slowSmallLargePredCofactors_le_endpoint hN hy
      _ ≤ A * (1 * (((2 * A / y) + (2 * A / y)) * A)) := by
        gcongr
      _ = 4 * A ^ 3 / (y : ℝ) := by ring
  have hch4 :
      ∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m ≤
        2 * A ^ 3 / (y : ℝ) := by
    calc
      (∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m) ≤
          K * ((1 / (N ^ 4 : ℕ)) * H +
            (1 / (N ^ 21 : ℕ)) * R * H) := by
        simpa [K, H, R] using sum_inv_middlePredLargeCofactors_le hN
      _ ≤ A * (((1 / (y : ℝ)) * A) + (1 / (y : ℝ)) * 1 * A) := by
        gcongr
      _ = 2 * A ^ 2 / (y : ℝ) := by ring
      _ ≤ 2 * A ^ 3 / (y : ℝ) := by gcongr
  have hall := sum_inv_slowCutoffBadOddCofactors_le_four_channels
    (N := N) (y := y) hN
  calc
    (∑ m ∈ slowCutoffBadOddCofactors N y, (1 : ℝ) / m) ≤
        (∑ m ∈ slowInternalTotientCofactors N y, (1 : ℝ) / m) +
          (∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m) +
            (∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m) +
              (∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m) := hall
    _ ≤ (2 * A ^ 3 / y) + (4 * A ^ 3 / y) +
          (4 * A ^ 3 / y) + (2 * A ^ 3 / y) := by
      exact add_le_add (add_le_add (add_le_add hch1 hch2) hch3) hch4
    _ = 12 * (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) := by
      dsimp [A]
      ring

/-- Subtracting the slow B4 exceptional family from the odd raw family. -/
theorem sum_inv_largeGcdFreeOddCofactors_ge
    {N y : ℕ} {R D : ℝ}
    (hraw : R ≤ ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m)
    (hbad : ∑ m ∈ slowCutoffBadOddCofactors N y, (1 : ℝ) / m ≤ D) :
    R - D ≤ ∑ m ∈ largeGcdFreeOddCofactors N y, (1 : ℝ) / m := by
  classical
  let good := largeGcdFreeOddCofactors N y
  let bad := slowCutoffBadOddCofactors N y
  have hpartition : oddRawCofactors N = good ∪ bad := by
    ext m
    by_cases hm : m ∈ oddRawCofactors N
    · simp only [hm, good, bad, mem_largeGcdFreeOddCofactors_iff,
        mem_slowCutoffBadOddCofactors_iff, true_and, Finset.mem_union]
      constructor
      · intro h
        by_cases hg : ∀ p : ℕ, p.Prime → y < p →
            ¬ (p ∣ m ∧ p ∣ Nat.totient m)
        · exact Or.inl hg
        · right
          push_neg at hg
          exact hg
      · intro h
        trivial
    · simp only [hm, good, bad, mem_largeGcdFreeOddCofactors_iff,
        mem_slowCutoffBadOddCofactors_iff, false_and, Finset.mem_union]
      simp
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro m hmg hmb
    have hg := (mem_largeGcdFreeOddCofactors_iff.mp hmg).2
    obtain ⟨_, p, hp, hyp, hpm, hpφ⟩ :=
      mem_slowCutoffBadOddCofactors_iff.mp hmb
    exact hg p hp hyp ⟨hpm, hpφ⟩
  have htotal :
      ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m =
        ∑ m ∈ good, (1 : ℝ) / m + ∑ m ∈ bad, (1 : ℝ) / m := by
    rw [hpartition, Finset.sum_union hdisj]
  dsimp [good, bad] at htotal ⊢
  linarith

/-- At the slow cutoff used by B5, the genuine B4 family still has
logarithmic reciprocal mass. -/
theorem eventually_slowLargeGcdFree_log_mass
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let y := Nat.nthRoot (4 * S) N
      (1 / 4000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ largeGcdFreeOddCofactors N y, (1 : ℝ) / m := by
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (48000 : ℝ))
  filter_upwards [eventually_log_le_mul_reciprocalOddRawCofactorSum,
      eventually_reciprocalPrimeIntervalSum_four_five_upper_one,
      eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_upper_one,
      eventually_slowCutoff_log_cube_div_le_one hS,
      eventually_nthRoot_ge (4 * S) 1 (by omega), hlog,
      Filter.eventually_ge_atTop 2] with N hraw hR hQ henv hy hlogN hN
  let y := Nat.nthRoot (4 * S) N
  have hy1 : 1 ≤ y := by simpa [y] using hy
  have hyN : y ≤ N := by
    dsimp [y]
    exact nthRoot_le_self_of_pos (by omega)
  have hR' : ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff] using hR
  have hQ' : ∑ q ∈ largePrimes N, (1 : ℝ) / q ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, largePrimes_eq_primesLE_sdiff] using hQ
  have hraw' :
      (1 / 2000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m := by
    simpa [reciprocalOddRawCofactorSum] using hraw
  have hbad :
      ∑ m ∈ slowCutoffBadOddCofactors N y, (1 : ℝ) / m ≤ 12 := by
    calc
      (∑ m ∈ slowCutoffBadOddCofactors N y, (1 : ℝ) / m) ≤
          12 * (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) :=
        sum_inv_slowCutoffBadOddCofactors_le_log_envelope
          hN hy1 hyN hR' hQ'
      _ ≤ 12 := by
        have : (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) ≤ 1 := by
          simpa [y] using henv
        calc
          12 * (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) =
              12 * ((1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ)) := by ring
          _ ≤ 12 * 1 := mul_le_mul_of_nonneg_left this (by norm_num)
          _ = 12 := by ring
  have hret := sum_inv_largeGcdFreeOddCofactors_ge hraw' hbad
  change (48000 : ℝ) ≤ Real.log (N : ℝ) at hlogN
  calc
    (1 / 4000 : ℝ) * Real.log (N : ℝ) ≤
        (1 / 2000 : ℝ) * Real.log (N : ℝ) - 12 := by
      nlinarith
    _ ≤ ∑ m ∈ largeGcdFreeOddCofactors N y, (1 : ℝ) / m := hret

end Erdos822
