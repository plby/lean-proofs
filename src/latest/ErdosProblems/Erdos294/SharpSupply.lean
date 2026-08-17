/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos294.SharpParameters
import ErdosProblems.Erdos297.AuxiliaryDataSupply

/-!
# Arithmetic supply for the corrected constant-width cutoff

This specializes the finite auxiliary-prime sieve to `sharpGoodSet`.  The
only new numerical estimate is the product of `sharpS` with the repaired
small-prime cutoff; the nine powers of `log log` in `sharpSReal` were chosen
precisely to make that estimate immediate.
-/

open Filter Finset Real
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega BigOperators Topology

namespace Erdos294.SharpSupply

open Erdos297
open Erdos297.ActiveLcm Erdos297.AuxiliaryDataSupply
open Erdos297.AuxiliarySupply Erdos297.GoodFactorization
open Erdos297.MinorArc Erdos297.NearbyMultiple Erdos297.PrimeIntervals
open Erdos297.SmoothMultiple Erdos297.SupplyNumerics
open Erdos294.SharpParameters

noncomputable section

attribute [local instance] Classical.propDecidable

lemma eventually_one_le_sharpM_and_sharpM_le_N :
    ∀ᶠ N : ℕ in atTop, 1 ≤ sharpM N ∧ sharpM N ≤ N := by
  filter_upwards [eventually_ge_atTop (100 : ℕ)] with N hN
  simp only [sharpM]
  omega

lemma eventually_KSafe_le_sharpM :
    ∀ᶠ N : ℕ in atTop, KSafe N ≤ sharpM N := by
  filter_upwards [eventually_nat_KSafe_upper,
      tendsto_logScale.eventually_ge_atTop 100,
      eventually_pos_scales] with N hK hL hpos
  have hLpos : 0 < logScale N := zero_lt_one.trans hpos.2.1
  have hreal : (KSafe N : ℝ) ≤ (N : ℝ) / 100 := by
    calc
      (KSafe N : ℝ) ≤ (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N) := hK
      _ ≤ (N : ℝ) / 100 := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        · norm_num
        · nlinarith
  rw [sharpM]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 100)).2
  have hmul : (KSafe N : ℝ) * 100 ≤ (N : ℝ) :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).mp hreal
  exact_mod_cast hmul

lemma eventually_sharp_safe_scale_chain :
    ∀ᶠ N : ℕ in atTop,
      sharpS N ≤ KSafe N ∧ KSafe N ≤ sharpM N ∧ sharpM N ≤ N := by
  filter_upwards [eventually_sharpS_le_KSafe, eventually_KSafe_le_sharpM,
      eventually_one_le_sharpM_and_sharpM_le_N] with N hSK hKM hMN
  exact ⟨hSK, hKM, hMN.2⟩

lemma eventually_two_mul_KSafe_lt_sharpM :
    ∀ᶠ N : ℕ in atTop, 2 * KSafe N < sharpM N := by
  filter_upwards [eventually_nat_KSafe_upper, eventually_nat_KSafe_lower,
      eventually_pos_scales] with N hKupper hKlower hpos
  have hL : 0 < logScale N := zero_lt_one.trans hpos.2.1
  have hKposR : 0 < (KSafe N : ℝ) :=
    (div_pos hpos.1 (pow_pos hL 10)).trans_le hKlower
  have hden : (400 : ℝ) ≤ (10 : ℝ) ^ 7 * logScale N := by
    nlinarith [hpos.2.1]
  have hfour : ((400 * KSafe N : ℕ) : ℝ) ≤ (N : ℝ) := by
    push_cast
    calc
      (400 : ℝ) * KSafe N ≤
          400 * ((N : ℝ) / ((10 : ℝ) ^ 7 * logScale N)) := by gcongr
      _ ≤ (N : ℝ) := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [hpos.1]
  have hfourNat : 400 * KSafe N ≤ N := by exact_mod_cast hfour
  have hfourDiv : 4 * KSafe N ≤ N / 100 := by omega
  have hKpos : 0 < KSafe N := by exact_mod_cast hKposR
  simp only [sharpM]
  omega

lemma eventually_minorThreshold_candidate_budget_sharp :
    ∀ᶠ N : ℕ in atTop, ∀ q ∈ activePrimePowers (sharpGoodSet N),
      factorBound N * (minorThreshold N - 1) <
        (SupplyNumerics.smallPrimeCandidates (smallPrimeCutoff N) q).card *
          (fiberBudget N + 1) := by
  filter_upwards [eventually_smallPrimeCandidates_budget,
      eventually_minorThreshold_sub_one_le_minorBadThreshold] with N hbudget hround
  intro q hq
  have hqpp := activePrimePower_isPrimePow hq
  exact (Nat.mul_le_mul_left (factorBound N) hround).trans_lt
    (hbudget q hqpp)

/-- The corrected cutoff absorbs the complete repaired `p'` cutoff. -/
theorem eventually_sharpS_mul_smallPrimeCutoff_le_KSafe :
    ∀ᶠ N : ℕ in atTop,
      sharpS N * smallPrimeCutoff N ≤ KSafe N := by
  filter_upwards [eventually_pos_scales, eventually_sharpSReal_ge_two,
      eventually_KSafeReal_ge_two, eventually_nat_KSafe_lower] with
      N hpos hSlarge hKlarge hKlower
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hK : 0 < (KSafe N : ℝ) :=
    (div_pos hN (pow_pos hL 10)).trans_le hKlower
  have hSfloor : (sharpS N : ℝ) ≤ sharpSReal N := by
    apply Nat.floor_le
    dsimp [sharpSReal]
    positivity
  have hKhalf : KSafeReal N / 2 ≤ (KSafe N : ℝ) :=
    half_le_floor hKlarge
  have hcubic : (sharpS N : ℝ) *
      (4 * (10 : ℝ) ^ 8 * (N : ℝ) ^ 2 * logLogScale N ^ 6) ≤
        (KSafe N : ℝ) ^ 3 := by
    have hcore : sharpSReal N *
        (4 * (10 : ℝ) ^ 8 * (N : ℝ) ^ 2 * logLogScale N ^ 6) ≤
          (KSafeReal N / 2) ^ 3 := by
      dsimp [sharpSReal, KSafeReal, KReal]
      field_simp
      norm_num [sharpConstant]
    exact (mul_le_mul_of_nonneg_right hSfloor (by positivity)).trans
      (hcore.trans (pow_le_pow_left₀ (by positivity) hKhalf 3))
  let R : ℝ := 100 * (N : ℝ) ^ 2 * logScale N *
      logLogScale N ^ 2 / (KSafe N : ℝ) ^ 2
  let Y : ℝ := (10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
      logLogScale N ^ 4 / logScale N
  let U : ℝ := (10 : ℝ) ^ 8 * (N : ℝ) ^ 2 *
      logLogScale N ^ 6 / (KSafe N : ℝ) ^ 2
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hT : (minorBadThreshold N : ℝ) ≤ R := Nat.floor_le hR0
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hYU : Y ≤ U := by
    dsimp [Y, U, R] at *
    rw [div_le_iff₀ hL]
    calc
      (10 : ℝ) ^ 6 * (minorBadThreshold N : ℝ) *
          logLogScale N ^ 4 ≤
          (10 : ℝ) ^ 6 * R * logLogScale N ^ 4 := by gcongr
      _ = ((10 : ℝ) ^ 8 * (N : ℝ) ^ 2 *
          logLogScale N ^ 6 / (KSafe N : ℝ) ^ 2) * logScale N := by
        dsimp [R]
        field_simp
        ring
  have hXU : (smallPrimeCutoff N : ℝ) ≤ U + 1 :=
    (Nat.ceil_lt_add_one hY0).le.trans (by linarith)
  have hSU : (sharpS N : ℝ) * U ≤ (KSafe N : ℝ) / 4 := by
    dsimp [U]
    field_simp [hK.ne']
    nlinarith [hcubic]
  have hSle : (sharpS N : ℝ) ≤ (KSafe N : ℝ) / 2 := by
    have hSreal : sharpSReal N ≤ KSafeReal N / 4 := by
      dsimp [sharpSReal, KSafeReal, KReal]
      field_simp
      norm_num [sharpConstant]
      have hL2 : (1 : ℝ) ≤ logScale N ^ 2 := one_le_pow₀ hLone.le
      have hLL8 : (1 : ℝ) ≤ logLogScale N ^ 8 := one_le_pow₀ hLLone.le
      have hprod : (1 : ℝ) ≤
          logScale N ^ 2 * logLogScale N ^ 8 := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ logScale N ^ 2 * logLogScale N ^ 8 := by gcongr
      exact (by norm_num : (1 : ℝ) /
        250000000000000000000000000000000 ≤ 1).trans hprod
    exact hSfloor.trans (hSreal.trans (by linarith))
  have hreal : (sharpS N : ℝ) * (smallPrimeCutoff N : ℝ) ≤
      (KSafe N : ℝ) := by
    calc
      (sharpS N : ℝ) * (smallPrimeCutoff N : ℝ) ≤
          (sharpS N : ℝ) * (U + 1) := by gcongr
      _ = (sharpS N : ℝ) * U + sharpS N := by ring
      _ ≤ (KSafe N : ℝ) / 4 + (KSafe N : ℝ) / 2 := by gcongr
      _ ≤ (KSafe N : ℝ) := by linarith
  exact_mod_cast hreal

lemma eventually_two_mul_sharpS_le_KSafe :
    ∀ᶠ N : ℕ in atTop, 2 * sharpS N ≤ KSafe N := by
  filter_upwards [eventually_sharpS_mul_smallPrimeCutoff_le_KSafe,
      eventually_floor_logLogScale_le_smallPrimeCutoff,
      tendsto_logLogScale.eventually_ge_atTop 2] with N hprod hX hLL
  have hfloor : 2 ≤ ⌊logLogScale N⌋₊ := by
    apply Nat.le_floor
    simpa using hLL
  have htwoX : 2 ≤ smallPrimeCutoff N := hfloor.trans hX
  calc
    2 * sharpS N ≤ smallPrimeCutoff N * sharpS N :=
      Nat.mul_le_mul_right (sharpS N) htwoX
    _ = sharpS N * smallPrimeCutoff N := by ac_rfl
    _ ≤ KSafe N := hprod

lemma eventually_five_le_card_primesHalfFull_sharpS :
    ∀ᶠ N : ℕ in atTop, 5 ≤ (primesHalfFull (sharpS N)).card :=
  tendsto_sharpS_atTop.eventually eventually_five_le_card_primesHalfFull

/-- Generic smooth-multiple supply specialized to the constant-width set. -/
theorem eventually_exists_sharpGoodDenominator_multiple :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      KSafe N ≤ d →
      (d : ℝ) ≤ 4000 * (KSafe N : ℝ) * logScale N →
      d.primeFactors.card ≤ 5 →
      Erdos285.PrimePowers.PrimePowerSmooth (sharpS N) d →
      maxPrimeExponent d ≤ exponentBound N →
      Ω d + 1 ≤ factorBound N →
      ∃ n ∈ sharpGoodSet N, N / 2 ≤ n ∧ n ≤ N ∧ d ∣ n := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    eventually_six_le_card_primesBetween_dyadic
  have hExp : ∀ᶠ N : ℕ in atTop, 1 ≤ exponentBound N := by
    filter_upwards [tendsto_logLogScale.eventually_ge_atTop 1] with N hLL
    rw [exponentBound]
    apply Nat.le_floor
    simpa [logLogScale, logScale] using
      (show (1 : ℝ) ≤ 5 * logLogScale N by linarith)
  filter_upwards [eventually_sharp_safe_scale_chain,
      eventually_KSafeReal_ge_two,
      tendsto_dyadicMultiplierScale.eventually_ge_atTop (2 * T : ℝ),
      eventually_N_div_KSafe_le_sharpS, eventually_pos_scales, hExp]
      with N hchain hsafe hdyadic hNKS hpos hExpPos
  intro d hKd hdUpper hdCard hdSmooth hdExp hdOmega
  rcases hpos with ⟨hNpos, hL, hLL, hLLL⟩
  have hKpos : 0 < KSafe N := by
    have hhalf := half_le_floor hsafe
    have hhalfpos : (0 : ℝ) < KSafeReal N / 2 := by nlinarith
    exact_mod_cast hhalfpos.trans_le hhalf
  have hd0 : d ≠ 0 := (hKpos.trans_le hKd).ne'
  have hMhalf : sharpM N ≤ N / 2 := by
    simp only [sharpM]
    omega
  have hquotS : N / d ≤ sharpS N :=
    (Nat.div_le_div_left hKd hKpos).trans hNKS
  have hDpos : 0 < 4000 * (KSafe N : ℝ) * logScale N :=
    mul_pos (mul_pos (by norm_num) (by exact_mod_cast hKpos))
      (zero_lt_one.trans hL)
  have hTlower : T ≤ N / (2 * d) := by
    have hclearedD : (2 * (T : ℝ)) *
        (4000 * (KSafe N : ℝ) * logScale N) ≤ (N : ℝ) :=
      (le_div_iff₀ hDpos).mp (by
        simpa [dyadicMultiplierScale] using hdyadic)
    have hcleared : ((T * (2 * d) : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      calc
        (T : ℝ) * (2 * (d : ℝ)) = (2 * (T : ℝ)) * (d : ℝ) := by ring
        _ ≤ (2 * (T : ℝ)) *
            (4000 * (KSafe N : ℝ) * logScale N) := by gcongr
        _ ≤ (N : ℝ) := hclearedD
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * d)).2
    exact_mod_cast hcleared
  have hcardSix : 6 ≤ (multiplierPrimes N d).card := by
    apply (hT _ hTlower).trans
    apply Finset.card_le_card
    intro p hp
    rw [mem_primesBetween] at hp
    rw [mem_multiplierPrimes]
    have hlower : N / (2 * d) = (N / d) / 2 := by
      rw [Nat.mul_comm 2 d, Nat.div_div_eq_div_mul]
    rw [hlower] at hp ⊢
    exact ⟨by omega, hp.2.1.trans (Nat.mul_div_le (N / d) 2), hp.2.2⟩
  have hcard : d.primeFactors.card < (multiplierPrimes N d).card := by omega
  exact exists_goodDenominator_multiple hd0 hMhalf hcard hquotS hdSmooth
    hdExp hExpPos hdOmega

theorem eventually_good_multiple_of_sharpBaseExtension :
    ∀ᶠ N : ℕ in atTop, ∀ {q : ℕ}
      (base : BaseExtension N (sharpS N) (KSafe N) q)
      {p : ℕ}, p ∈ auxiliaryPrimes N → p.Coprime base.base →
      ∃ n ∈ sharpGoodSet N,
        N / 2 ≤ n ∧ n ≤ N ∧ base.base * p ∣ n := by
  filter_upwards [eventually_exists_sharpGoodDenominator_multiple,
      eventually_exponentBound_add_five_le_factorBound,
      eventually_auxiliaryPrime_le_sharpS,
      tendsto_logLogScale.eventually_ge_atTop 1, eventually_pos_scales]
      with N hmultiple hbudget hpS hLL hpos
  intro q base p hpP hcop
  have hpData := mem_auxiliaryPrimes.mp hpP
  have hpPrime := hpData.2.2
  have hpNot : ¬p ∣ base.base := hpPrime.coprime_iff_not_dvd.mp hcop
  have hE : 1 ≤ exponentBound N := by
    rw [exponentBound]
    apply Nat.le_floor
    simpa [logLogScale, logScale] using
      (show (1 : ℝ) ≤ 5 * logLogScale N by linarith)
  obtain ⟨hdSmooth, hdExp, hdOmega, hdomega⟩ :=
    factorization_data_mul_fresh_prime
      (by have := base.lower; omega) hpPrime hpNot (hpS p hpP) hE
      base.smooth base.exponent
  let d := base.base * p
  apply hmultiple d
  · have hpPos := hpPrime.pos
    dsimp [d]
    nlinarith [base.lower]
  · have hpUpper : (p : ℝ) ≤ 40 * logScale N := by
      have hpFloorR : (p : ℝ) ≤ (⌊40 * Real.log (N : ℝ)⌋₊ : ℝ) := by
        exact_mod_cast hpData.2.1
      exact hpFloorR.trans (by
        simpa [logScale] using
          (Nat.floor_le (show 0 ≤ 40 * Real.log (N : ℝ) by positivity)))
    have hbaseR : (base.base : ℝ) ≤ 100 * (KSafe N : ℝ) := by
      exact_mod_cast base.upper
    calc
      (d : ℝ) = (base.base : ℝ) * p := by simp [d]
      _ ≤ (100 * (KSafe N : ℝ)) * (40 * logScale N) := by
        exact mul_le_mul hbaseR hpUpper (Nat.cast_nonneg _) (by positivity)
      _ = 4000 * (KSafe N : ℝ) * logScale N := by ring
  · rw [card_primeFactors_eq_omega]
    calc
      ω d = ω base.base + 1 := by simpa [d] using hdomega
      _ ≤ 4 + 1 := Nat.add_le_add_right base.distinct 1
      _ = 5 := by norm_num
  · exact hdSmooth
  · exact hdExp
  · dsimp [d]
    rw [hdOmega]
    exact (Nat.add_le_add_right base.factors 2).trans hbudget

end

end Erdos294.SharpSupply
