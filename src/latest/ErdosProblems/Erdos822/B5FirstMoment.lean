/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.HarmonicCrude
import ErdosProblems.Erdos822.PrimeReciprocalUpper

/-!
# The B5 first moment at the slow cutoff

All ingredients are now finite and explicit.  For each sieve prime p the
fixed-incidence theorem gives a p-divisible small-factor term and a
residue-class term.  The slow-cutoff logarithm bound controls the latter
main term, while the crude power estimate absorbs its beta remainder.
Summing over p then uses the square-reciprocal bound.
-/

namespace Erdos822

open scoped BigOperators

/-- There are fixed constants S,D for which the weighted shifted-prime
mass first moment on odd raw cofactors is O(1 + log N). -/
theorem exists_eventually_shiftedMassFirstMoment_slowCutoff_le :
    ∃ S : ℕ, ∃ D : ℝ, 101 ≤ S ∧ 0 ≤ D ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let y := Nat.nthRoot (4 * S) N
        2 ≤ y ∧
          shiftedMassFirstMoment N 2 y ≤
            D * (1 + Real.log (N : ℝ)) := by
  obtain ⟨A, C, hA, hC, hfixed⟩ :=
    exists_sum_inv_shiftedDivisibleOddCofactors_upper_bound
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (99 * Real.log A / 4)
  let S : ℕ := max 101 (T + 100)
  have hS101 : 101 ≤ S := by
    dsimp [S]
    exact le_max_left _ _
  have hSpos : 0 < S := by omega
  have hTS : T ≤ S - 100 := by
    dsimp [S]
    omega
  have hlog :
      Real.log A ≤ 4 * (S - 100 : ℕ) / 99 := by
    have hTSR : (T : ℝ) ≤ (S - 100 : ℕ) := by exact_mod_cast hTS
    have hT' : 99 * Real.log A / 4 < (T : ℝ) := hT
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 99)).2
    have hmul :
        99 * Real.log A < (T : ℝ) * 4 :=
      (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hT'
    linarith
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let B : ℝ :=
    (1 + eta) * C * Real.exp 3 * Real.log 2 *
      ((1 : ℝ) / Real.log 2 + 8 * (S : ℝ))
  let D : ℝ := 2 * B + 2
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨S, D, hS101, hD, ?_⟩
  filter_upwards [
      eventually_nthRoot_ge (4 * S) 2 (by omega),
      eventually_reciprocalPrimeIntervalSum_four_five_upper_one,
      eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_upper_one,
      Filter.eventually_ge_atTop 2] with N hy hRone hQone hN
  let y := Nat.nthRoot (4 * S) N
  have hy2 : 2 ≤ y := by simpa [y] using hy
  have hyN : y ≤ N := by
    dsimp [y]
    exact nthRoot_le_self_of_pos (by omega)
  have hyN21 : y < N ^ 21 := by
    have hpow : N ^ 1 < N ^ 21 :=
      Nat.pow_lt_pow_right (by omega : 1 < N) (by omega)
    have hNN21 : N < N ^ 21 := by simpa using hpow
    exact hyN.trans_lt hNN21
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hL : 0 ≤ 1 + Real.log (N : ℝ) := by linarith
  have hH :
      (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) :=
    harmonic_le_one_add_log N
  have hR :
      ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff]
      using hRone
  have hQ :
      ∑ q ∈ largePrimes N, (1 : ℝ) / q ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, largePrimes_eq_primesLE_sdiff]
      using hQone
  have hKnot :
      ∀ p : ℕ,
        ∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
            (1 : ℝ) / k ≤ 1 + Real.log (N : ℝ) := by
    intro p
    calc
      (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
          (1 : ℝ) / k) ≤
          ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro k hk hnot
        exact one_div_nonneg.mpr (by exact_mod_cast (Nat.zero_le k))
      _ ≤ (harmonic N : ℝ) :=
        sum_inv_oddSmallFactors_le_harmonic N
      _ ≤ 1 + Real.log (N : ℝ) := hH
  have hHdiv :
      ∀ p : ℕ, (harmonic (N / p) : ℝ) ≤
        1 + Real.log (N : ℝ) := by
    intro p
    exact (harmonic_cast_mono (Nat.div_le_self N p)).trans hH
  have hratio :
      (harmonic N : ℝ) / Real.log (y : ℝ) ≤
        (1 : ℝ) / Real.log 2 + 8 * (S : ℝ) := by
    simpa [y] using harmonic_div_log_slowSieveCutoff_le hSpos hy
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hinc : ∀ p ∈ Erdos851.sievePrimes 2 y,
      ∑ m ∈ shiftedDivisibleOddCofactors N p, (1 : ℝ) / m ≤
        (D * (1 + Real.log (N : ℝ))) / p := by
    intro p hpMem
    have hpData := Erdos851.mem_sievePrimes.mp hpMem
    have hpPrime := hpData.2.2
    have hpY : p ≤ y := hpData.2.1
    have hpN : p ≤ N := hpY.trans hyN
    have hpN4 : p < N ^ 4 := by
      have hpow : N ^ 1 < N ^ 4 :=
        Nat.pow_lt_pow_right (by omega : 1 < N) (by omega)
      have hNN4 : N < N ^ 4 := by simpa using hpow
      exact hpN.trans_lt hNN4
    have hpN21 : p ≤ N ^ 21 := by
      have hpow : N ^ 1 < N ^ 21 :=
        Nat.pow_lt_pow_right (by omega : 1 < N) (by omega)
      have hNN21 : N ≤ N ^ 21 := by
        have : N < N ^ 21 := by simpa using hpow
        omega
      exact hpN.trans hNN21
    have hbase := hfixed N p y S hN hpPrime hpN4 hpN21
      hy2 hyN21 hS101 hlog
    dsimp only at hbase
    let W : ℝ :=
      (1 + eta) *
        (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
          Real.exp 3)
    let E : ℝ := ((y ^ S : ℕ) : ℝ) ^ 2
    let F : ℝ :=
      (2 * W / (p : ℝ) + E / ((N ^ 21 : ℕ) : ℝ)) *
        (harmonic N : ℝ)
    have hWH : W * (harmonic N : ℝ) ≤ B := by
      dsimp [W, B, eta]
      calc
        ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
                Real.exp 3)) *
            (harmonic N : ℝ) =
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              C * Real.exp 3 * Real.log 2) *
              ((harmonic N : ℝ) / Real.log (y : ℝ)) := by
          field_simp
        _ ≤
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              C * Real.exp 3 * Real.log 2) *
              ((1 : ℝ) / Real.log 2 + 8 * (S : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hratio (by positivity)
    have hperror :
        (p : ℝ) * E * (harmonic N : ℝ) ≤
          ((N ^ 21 : ℕ) : ℝ) := by
      dsimp [E]
      simpa [y] using
        slowSieveCutoff_prime_mul_error_mul_harmonic_le hN hSpos hpY
    have hN21pos : (0 : ℝ) < ((N ^ 21 : ℕ) : ℝ) := by
      exact_mod_cast
        (show 0 < N ^ 21 from Nat.pow_pos (by omega : 0 < N))
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have herror :
        E / ((N ^ 21 : ℕ) : ℝ) * (harmonic N : ℝ) ≤
          (1 : ℝ) / p := by
      have hratioError :
          ((p : ℝ) * E * (harmonic N : ℝ)) /
              ((N ^ 21 : ℕ) : ℝ) ≤ 1 :=
        (div_le_iff₀ hN21pos).2 (by simpa only [one_mul] using hperror)
      calc
        E / ((N ^ 21 : ℕ) : ℝ) * (harmonic N : ℝ) =
            ((1 : ℝ) / p) *
              (((p : ℝ) * E * (harmonic N : ℝ)) /
                ((N ^ 21 : ℕ) : ℝ)) := by
          field_simp
        _ ≤ ((1 : ℝ) / p) * 1 := by
          exact mul_le_mul_of_nonneg_left hratioError
            (one_div_nonneg.mpr hpR.le)
        _ = (1 : ℝ) / p := by ring
    have hF :
        F ≤ 2 * B / (p : ℝ) + (1 : ℝ) / p := by
      dsimp [F]
      calc
        (2 * W / (p : ℝ) + E / ((N ^ 21 : ℕ) : ℝ)) *
            (harmonic N : ℝ) =
            2 * (W * (harmonic N : ℝ)) / (p : ℝ) +
              E / ((N ^ 21 : ℕ) : ℝ) * (harmonic N : ℝ) := by
          ring
        _ ≤ 2 * B / (p : ℝ) + (1 : ℝ) / p := by
          apply add_le_add
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hWH (by norm_num))
              hpR.le
          · exact herror
    have hfirst :
        ((harmonic (N / p) : ℝ) / (p : ℝ)) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              (∑ q ∈ largePrimes N, (1 : ℝ) / q) ≤
          (1 + Real.log (N : ℝ)) / (p : ℝ) := by
      have hR0 : 0 ≤ ∑ r ∈ middlePrimes N, (1 : ℝ) / r :=
        Finset.sum_nonneg fun r hr =>
          one_div_nonneg.mpr (by exact_mod_cast (Nat.zero_le r))
      have hQ0 : 0 ≤ ∑ q ∈ largePrimes N, (1 : ℝ) / q :=
        Finset.sum_nonneg fun q hq =>
          one_div_nonneg.mpr (by exact_mod_cast (Nat.zero_le q))
      have hdivP :
          (harmonic (N / p) : ℝ) / (p : ℝ) ≤
            (1 + Real.log (N : ℝ)) / (p : ℝ) :=
        div_le_div_of_nonneg_right (hHdiv p) hpR.le
      have hLp0 :
          0 ≤ (1 + Real.log (N : ℝ)) / (p : ℝ) :=
        div_nonneg hL hpR.le
      calc
        ((harmonic (N / p) : ℝ) / (p : ℝ)) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              (∑ q ∈ largePrimes N, (1 : ℝ) / q) ≤
            ((1 + Real.log (N : ℝ)) / (p : ℝ)) *
              (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
                (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hdivP hR0) hQ0
        _ ≤ ((1 + Real.log (N : ℝ)) / (p : ℝ)) * 1 *
              (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR hLp0) hQ0
        _ ≤ ((1 + Real.log (N : ℝ)) / (p : ℝ)) * 1 * 1 := by
          exact mul_le_mul_of_nonneg_left hQ
            (mul_nonneg hLp0 (by norm_num))
        _ = (1 + Real.log (N : ℝ)) / (p : ℝ) := by ring
    have hsecond :
        (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
            (1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F ≤
          (1 + Real.log (N : ℝ)) *
            (2 * B / (p : ℝ) + (1 : ℝ) / p) := by
      have hK0 : 0 ≤ ∑ k ∈ (oddSmallFactors N).filter
          (fun k => ¬ p ∣ k), (1 : ℝ) / k :=
        Finset.sum_nonneg fun k hk =>
          one_div_nonneg.mpr (by exact_mod_cast (Nat.zero_le k))
      have hR0 : 0 ≤ ∑ r ∈ middlePrimes N, (1 : ℝ) / r :=
        Finset.sum_nonneg fun r hr =>
          one_div_nonneg.mpr (by exact_mod_cast (Nat.zero_le r))
      have hH0 : 0 ≤ (harmonic N : ℝ) := by
        rw [harmonic_eq_sum_Icc, Rat.cast_sum]
        exact Finset.sum_nonneg fun i hi => by
          simp only [Rat.cast_inv, Rat.cast_natCast]
          exact inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le i))
      have hW0 : 0 ≤ W := by
        dsimp [W]
        exact mul_nonneg (by linarith [heta])
          (mul_nonneg
            (mul_nonneg hC.le (div_nonneg hlog2.le hlogy.le))
            (Real.exp_pos 3).le)
      have hE0 : 0 ≤ E := by
        dsimp [E]
        exact sq_nonneg _
      have hF0 : 0 ≤ F := by
        dsimp [F, W, E]
        exact mul_nonneg
          (add_nonneg
            (div_nonneg (mul_nonneg (by norm_num) hW0) hpR.le)
            (div_nonneg hE0 hN21pos.le))
          hH0
      have hG0 : 0 ≤ 2 * B / (p : ℝ) + (1 : ℝ) / p := by
        exact add_nonneg
          (div_nonneg (mul_nonneg (by norm_num) hB) hpR.le)
          (one_div_nonneg.mpr hpR.le)
      calc
        (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
            (1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F ≤
            (1 + Real.log (N : ℝ)) *
              (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hKnot p) hR0) hF0
        _ ≤ (1 + Real.log (N : ℝ)) * 1 * F := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR hL) hF0
        _ ≤ (1 + Real.log (N : ℝ)) * 1 *
              (2 * B / (p : ℝ) + (1 : ℝ) / p) := by
          exact mul_le_mul_of_nonneg_left hF
            (mul_nonneg hL (by norm_num))
        _ = (1 + Real.log (N : ℝ)) *
            (2 * B / (p : ℝ) + (1 : ℝ) / p) := by ring
    calc
      (∑ m ∈ shiftedDivisibleOddCofactors N p, (1 : ℝ) / m) ≤
          ((harmonic (N / p) : ℝ) / (p : ℝ)) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              (∑ q ∈ largePrimes N, (1 : ℝ) / q) +
          (∑ k ∈ (oddSmallFactors N).filter (fun k => ¬ p ∣ k),
              (1 : ℝ) / k) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * F := by
        simpa [W, E, F, eta] using hbase
      _ ≤ (1 + Real.log (N : ℝ)) / (p : ℝ) +
          (1 + Real.log (N : ℝ)) *
            (2 * B / (p : ℝ) + (1 : ℝ) / p) :=
        add_le_add hfirst hsecond
      _ = (D * (1 + Real.log (N : ℝ))) / (p : ℝ) := by
        dsimp [D]
        ring
  refine ⟨hy2, ?_⟩
  exact shiftedMassFirstMoment_le_one_add_log_of_incidence
    N 2 y hD hL (by omega) hinc

end Erdos822
