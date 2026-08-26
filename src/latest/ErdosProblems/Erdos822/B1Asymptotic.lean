/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1PrimeMean
import ErdosProblems.Erdos822.SlowCutoffAsymptotic

/-!
# The B1 exceptional set at an iterated-log cutoff

The estimates are first uniform in every cutoff `y` with `256*y ≤ Z`,
where `Z = log₂(log₂ N)` uses natural-number binary logarithms.  Taking
the fourth root of `Z` makes the B1 failure proportion tend to zero.
-/

namespace Erdos822

open Filter
open scoped BigOperators

def b1DoubleLog (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 N)

def b1Cutoff (N : ℕ) : ℕ := Nat.nthRoot 4 (b1DoubleLog N)

theorem tendsto_natLog_two_atTop : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2 ^ b)] with N hN
  have hNpos : 0 < N := (by positivity : 0 < 2 ^ b).trans_le hN
  exact (Nat.le_log_iff_pow_le (by norm_num) hNpos.ne').mpr hN

theorem tendsto_b1DoubleLog_atTop : Tendsto b1DoubleLog atTop atTop :=
  tendsto_natLog_two_atTop.comp tendsto_natLog_two_atTop

theorem tendsto_b1Cutoff_atTop : Tendsto b1Cutoff atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact tendsto_b1DoubleLog_atTop.eventually
    (eventually_nthRoot_ge 4 b (by norm_num))

theorem packetPrimeMean_b1PrimePacket_mono {N N' d : ℕ} (hNN' : N ≤ N') :
    packetPrimeMean (b1PrimePacket N d) ≤ packetPrimeMean (b1PrimePacket N' d) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨hqN, hqp, hqd⟩ := mem_b1PrimePacket_iff.mp hq
    exact mem_b1PrimePacket_iff.mpr ⟨hqN.trans hNN', hqp, hqd⟩
  · intro q hq hnot
    positivity

/-- Uniform reciprocal packet mass for every modulus substantially below
the double logarithm. -/
theorem eventually_packetPrimeMean_mul_lower :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      2 ≤ d → 256 * d ≤ b1DoubleLog N →
        (b1DoubleLog N : ℝ) / 128 ≤
          (d : ℝ) * packetPrimeMean (b1PrimePacket N d) := by
  obtain ⟨J₀, hJ₀⟩ := exists_packetPrimeMean_log_lower
  have hlogSmall := tendsto_b1DoubleLog_atTop.eventually
    (eventually_const_mul_log_pow_div_natCast_le_one 24 1)
  filter_upwards [hlogSmall,
      tendsto_b1DoubleLog_atTop.eventually_ge_atTop (max J₀ 24),
      tendsto_natLog_two_atTop.eventually_ge_atTop 4,
      eventually_ge_atTop 1] with N hsmall hZlarge hK4 hN1
  intro d hd hdZ
  let K := Nat.log 2 N
  let Z := b1DoubleLog N
  have hZ24 : 24 ≤ Z := (le_max_right J₀ 24).trans hZlarge
  have hJ : J₀ ≤ Z := (le_max_left J₀ 24).trans hZlarge
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hZK : Z ≤ K := Nat.log_le_self 2 K
  have hdJ : d ≤ Z + 1 := by change 256 * d ≤ Z at hdZ; omega
  have hbound := hJ₀ Z K d hJ hZK hd hdJ
  have hlogZ : 12 * (1 + Real.log (Z : ℝ)) ≤ (Z : ℝ) := by
    change 24 * Real.log (Z : ℝ) ^ 1 / (Z : ℝ) ≤ 1 at hsmall
    have hsm := (div_le_iff₀ hZpos).mp hsmall
    have hZ24R : (24 : ℝ) ≤ Z := by exact_mod_cast hZ24
    simp only [pow_one, one_mul] at hsm
    linarith
  have hlogK : (Z : ℝ) / 3 ≤ Real.log ((K : ℝ) + 1) := by
    have hscale := Erdos387.binaryLogScale_cast_le_three_mul_log hK4
    have hmono : Real.log (K : ℝ) ≤ Real.log ((K : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast (show 0 < K by omega)) (by linarith)
    have hscale' : (Z : ℝ) + 1 ≤ 3 * Real.log (K : ℝ) := by
      simpa [Erdos387.binaryLogScale, K, Z, b1DoubleLog] using hscale
    linarith
  have hdZR : 256 * (d : ℝ) ≤ Z := by exact_mod_cast hdZ
  have hbound' : (Z : ℝ) / 128 ≤
      (d : ℝ) * packetPrimeMean (b1PrimePacket (2 ^ K) d) := by
    nlinarith
  have hpow : 2 ^ K ≤ N := Nat.pow_log_le_self 2 (by omega)
  exact hbound'.trans (mul_le_mul_of_nonneg_left
    (packetPrimeMean_b1PrimePacket_mono hpow) (by positivity))

/-- The uniform counting bound before choosing a particular cutoff. -/
theorem eventually_card_b1FailureIndices_mul_doubleLog_le :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℕ, 256 * y ≤ b1DoubleLog N →
      ((b1FailureIndices N y).card : ℝ) * b1DoubleLog N ≤
        1536 * N * (y : ℝ) ^ 2 := by
  filter_upwards [eventually_packetPrimeMean_mul_lower] with N hN
  intro y hy
  have hyR : 256 * (y : ℝ) ≤ b1DoubleLog N := by exact_mod_cast hy
  have h := card_b1FailureIndices_mul_le N y
    (M := (b1DoubleLog N : ℝ) / 128) (by positivity) (by linarith) (by
      intro d hd
      have hdy := (Finset.mem_Icc.mp hd).2
      exact hN d (Finset.mem_Icc.mp hd).1
        ((Nat.mul_le_mul_left 256 hdy).trans hy))
  nlinarith

theorem eventually_b1Cutoff_mul_256_le_doubleLog :
    ∀ᶠ N : ℕ in atTop, 256 * b1Cutoff N ≤ b1DoubleLog N := by
  filter_upwards [tendsto_b1Cutoff_atTop.eventually_ge_atTop 7] with N hy
  have hy3 : 256 ≤ b1Cutoff N ^ 3 :=
    (by norm_num : 256 ≤ 7 ^ 3).trans (Nat.pow_le_pow_left hy 3)
  calc
    256 * b1Cutoff N ≤ b1Cutoff N ^ 3 * b1Cutoff N :=
      Nat.mul_le_mul_right (b1Cutoff N) hy3
    _ = b1Cutoff N ^ 4 := by ring
    _ ≤ b1DoubleLog N := nthRoot_pow_le (by norm_num)

/-- At the fourth-root cutoff the reciprocal failure proportion is bounded
by `1536 / y^2`, which tends to zero. -/
theorem eventually_card_b1FailureIndices_mul_cutoff_sq_le :
    ∀ᶠ N : ℕ in atTop,
      ((b1FailureIndices N (b1Cutoff N)).card : ℝ) * (b1Cutoff N : ℝ) ^ 2 ≤
        1536 * N := by
  filter_upwards [eventually_card_b1FailureIndices_mul_doubleLog_le,
      eventually_b1Cutoff_mul_256_le_doubleLog,
      tendsto_b1Cutoff_atTop.eventually_ge_atTop 1] with N hN hy hy1
  have h := hN (b1Cutoff N) hy
  have hypos : (0 : ℝ) < b1Cutoff N := by exact_mod_cast (show 0 < b1Cutoff N by omega)
  have hy4 : (b1Cutoff N : ℝ) ^ 4 ≤ b1DoubleLog N := by
    exact_mod_cast (nthRoot_pow_le (k := 4) (x := b1DoubleLog N) (by norm_num))
  have hmul := mul_le_mul_of_nonneg_left hy4
    (show (0 : ℝ) ≤ (b1FailureIndices N (b1Cutoff N)).card by positivity)
  have hsq : (b1Cutoff N : ℝ) ^ 2 *
      (((b1FailureIndices N (b1Cutoff N)).card : ℝ) * (b1Cutoff N : ℝ) ^ 2) ≤
        (b1Cutoff N : ℝ) ^ 2 * (1536 * N) := by nlinarith
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hypos)).mp hsq

/-- Normal-order formulation: for every positive error fraction, eventually
at most that fraction of the integers fail B1. -/
theorem eventually_card_b1FailureIndices_le_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((b1FailureIndices N (b1Cutoff N)).card : ℝ) ≤ ε * N := by
  have hyT : Tendsto (fun N ↦ (b1Cutoff N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_b1Cutoff_atTop
  filter_upwards [eventually_card_b1FailureIndices_mul_cutoff_sq_le,
      hyT.eventually_ge_atTop (max 1 (1536 / ε))] with N hN hy
  have hy1 : (1 : ℝ) ≤ b1Cutoff N := (le_max_left _ _).trans hy
  have hypos : (0 : ℝ) < b1Cutoff N := zero_lt_one.trans_le hy1
  have hysq : (b1Cutoff N : ℝ) ≤ (b1Cutoff N : ℝ) ^ 2 := by nlinarith
  have hyε : 1536 ≤ ε * (b1Cutoff N : ℝ) ^ 2 := by
    have hle : 1536 / ε ≤ (b1Cutoff N : ℝ) := (le_max_right _ _).trans hy
    have hmul := (div_le_iff₀ hε).mp hle
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hyε (show (0 : ℝ) ≤ N by positivity)
  have hsq : (b1Cutoff N : ℝ) ^ 2 *
      ((b1FailureIndices N (b1Cutoff N)).card : ℝ) ≤
        (b1Cutoff N : ℝ) ^ 2 * (ε * N) := by nlinarith
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hypos)).mp hsq

/-- The B1 exceptional proportion tends to zero, with the cutoff itself
growing as the fourth root of the integer double logarithm. -/
theorem tendsto_b1FailureProportion_zero :
    Tendsto (fun N : ℕ ↦
      ((b1FailureIndices N (b1Cutoff N)).card : ℝ) / N) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [eventually_card_b1FailureIndices_le_mul (ε := ε / 2) (by positivity),
      eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hquot : ((b1FailureIndices N (b1Cutoff N)).card : ℝ) / N ≤ ε / 2 :=
    (div_le_iff₀ hNpos).mpr (by nlinarith)
  linarith

#print axioms tendsto_b1FailureProportion_zero

end Erdos822
