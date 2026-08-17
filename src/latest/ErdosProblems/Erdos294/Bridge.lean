/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos297.LocalLimit
import ErdosProblems.Erdos297.AuxiliarySupply

/-!
# A large bridge modulus supported at every good scale

The bridge is the product of the primes in `[S/2,S]`.  Every such prime is
an exact local part of a source good denominator, and hence is active.  The
product is exponentially large in `S`; this is the common denominator used
in both halves of the Liu--Sawhney gluing argument.
-/

open Filter Finset Real
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega BigOperators Topology

namespace Erdos294.Bridge

open Erdos285.PrimePowers
open Erdos297
open Erdos297.ActiveLcm Erdos297.AuxiliarySupply
open Erdos297.GoodFactorization Erdos297.LogisticNormalization
open Erdos297.PrimeIntervals Erdos297.SmoothMultiple
open Erdos297.SupplyNumerics

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The product of the large primes below the good-set smoothness cutoff. -/
def bridgeModulus (N : ℕ) : ℕ := (primesHalfFull (S N)).prod id

private theorem eventually_four_mul_almostOnePower_le_S :
    ∀ᶠ N : ℕ in atTop, 4 * almostOnePower N ≤ (S N : ℝ) := by
  filter_upwards [eventually_mul_almostOnePower_le_SReal 8 (by norm_num),
    eventually_real_scales_ge_two] with N hlarge hscales
  have hhalf : SReal N / 2 ≤ (S N : ℝ) := half_le_floor hscales.1
  linarith

private theorem eventually_three_mul_N_le_S_sq :
    ∀ᶠ N : ℕ in atTop, 3 * N ≤ S N * S N := by
  filter_upwards [eventually_four_mul_almostOnePower_le_S,
    eventually_ge_atTop (1 : ℕ)] with N hS hN
  have hpow : Real.sqrt (N : ℝ) ≤ almostOnePower N := by
    rw [Real.sqrt_eq_rpow, almostOnePower]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) (by norm_num)
  have hsqrt : 4 * Real.sqrt (N : ℝ) ≤ (S N : ℝ) :=
    (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hS
  have hsqrt0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsquare := mul_self_le_mul_self
    (mul_nonneg (by norm_num) hsqrt0) hsqrt
  have hsqrtSq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg N)
  have hreal : (3 : ℝ) * N ≤ (S N : ℝ) * S N := by
    nlinarith
  exact_mod_cast hreal

private theorem eventually_two_mul_T_mul_S_le_N (T : ℕ) :
    ∀ᶠ N : ℕ in atTop, 2 * T * S N ≤ N := by
  filter_upwards [tendsto_logScale.eventually_ge_atTop (2 * T : ℝ),
    eventually_pos_scales] with N hL hpos
  have hLpos : 0 < logScale N := zero_lt_one.trans hpos.2.1
  have hSupper : (S N : ℝ) ≤ SReal N :=
    Nat.floor_le (by dsimp [SReal]; positivity)
  have hpow : (2 * T : ℝ) ≤ logScale N ^ 4 := by
    have hLone : 1 ≤ logScale N := hpos.2.1.le
    calc
      (2 * T : ℝ) ≤ logScale N := hL
      _ = logScale N ^ (1 : ℕ) := by ring
      _ ≤ logScale N ^ (4 : ℕ) :=
        pow_le_pow_right₀ hLone (by norm_num)
  have hreal : ((2 * T * S N : ℕ) : ℝ) ≤ (N : ℝ) := by
    push_cast
    calc
      (2 : ℝ) * T * S N ≤ (2 : ℝ) * T * SReal N := by gcongr
      _ = (2 : ℝ) * T * ((N : ℝ) / logScale N ^ 4) := by rfl
      _ = ((2 : ℝ) * T * N) / logScale N ^ 4 := by ring
      _ ≤ (N : ℝ) := by
        rw [div_le_iff₀ (pow_pos hLpos 4)]
        nlinarith [hpow, hpos.1]
  exact_mod_cast hreal

/-- Every prime in `[S/2,S]` is an active exact prime part of the source
good set. -/
theorem eventually_primesHalfFull_subset_activePrimePowers :
    ∀ᶠ N : ℕ in atTop,
      primesHalfFull (S N) ⊆ activePrimePowers (goodSet N) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    eventually_six_le_card_primesBetween_dyadic
  filter_upwards [eventually_two_mul_T_mul_S_le_N T,
    eventually_three_mul_N_le_S_sq, eventually_nat_scale_chain,
    eventually_exponentBound_add_five_le_factorBound,
    tendsto_logLogScale.eventually_ge_atTop 1,
    eventually_ge_atTop (3 : ℕ)] with N hTS hNSq hchain hfactor hLL hN
  intro q hq
  have hqData := mem_primesHalfFull.mp hq
  rcases hqData with ⟨hqLower, hqS, hqPrime⟩
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hScmp : S N ≤ 3 * q := by
    have : S N ≤ 3 * (S N / 2) := by omega
    exact this.trans (Nat.mul_le_mul_left 3 hqLower)
  have hNqS : N ≤ q * S N := by
    have : 3 * N ≤ 3 * (q * S N) := by
      calc
        3 * N ≤ S N * S N := hNSq
        _ ≤ (3 * q) * S N := Nat.mul_le_mul_right (S N) hScmp
        _ = 3 * (q * S N) := by ring
    omega
  have hquotS : N / q ≤ S N := by
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm] using hNqS
  have hTquot : T ≤ N / (2 * q) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * q)).2
    calc
      T * (2 * q) = 2 * T * q := by ring
      _ ≤ 2 * T * S N := Nat.mul_le_mul_left (2 * T) hqS
      _ ≤ N := hTS
  have hsixBase : 6 ≤
      (primesBetween (N / (2 * q) + 1) (2 * (N / (2 * q)))).card :=
    hT (N / (2 * q)) hTquot
  have hsix : 6 ≤ (multiplierPrimes N q).card := by
    apply hsixBase.trans
    apply Finset.card_le_card
    intro p hp
    rw [mem_primesBetween] at hp
    rw [mem_multiplierPrimes]
    refine ⟨by omega, ?_, hp.2.2⟩
    exact hp.2.1.trans (by
      rw [show N / (2 * q) = (N / q) / 2 by
        rw [Nat.mul_comm 2 q, Nat.div_div_eq_div_mul]]
      exact Nat.mul_div_le (N / q) 2)
  have hcard : q.primeFactors.card < (multiplierPrimes N q).card := by
    have hqcard : q.primeFactors.card = 1 :=
      isPrimePow_iff_card_primeFactors_eq_one.mp hqPrime.isPrimePow
    omega
  have hMhalf : Erdos297.M N ≤ N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    have hreal : (((Erdos297.M N) * 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      nlinarith [hchain.2.2]
    exact_mod_cast hreal
  have hE : 1 ≤ exponentBound N := by
    rw [exponentBound]
    apply Nat.le_floor
    have : (1 : ℝ) ≤ 5 * logLogScale N := by nlinarith
    simpa [logLogScale, logScale] using this
  have hqSmooth : PrimePowerSmooth (S N) q :=
    primePowerSmooth_mono hqS (primePowerSmooth_self q)
  have hqOmega : Ω q = 1 := by
    rw [ArithmeticFunction.cardFactors_apply_prime hqPrime]
  have hqExp : maxPrimeExponent q ≤ exponentBound N := by
    exact (maxPrimeExponent_le_Omega q).trans (by simpa [hqOmega] using hE)
  have hqFactor : Ω q + 1 ≤ factorBound N := by
    rw [hqOmega]
    omega
  obtain ⟨p, hpPrime, hpLower, hpUpper, hpNot⟩ :=
    exists_coprime_multiplier_prime hqPrime.ne_zero hcard
  have hpS : p ≤ S N := hpUpper.trans hquotS
  have hnGood : q * p ∈ goodDenominators N (Erdos297.M N) (S N) := by
    rw [mem_goodDenominators]
    have hrange := mul_mem_half_interval hqPrime.ne_zero hpLower hpUpper
    refine ⟨hMhalf.trans hrange.1, hrange.2, ?_, ?_, ?_⟩
    · exact primePowerSmooth_mul_prime_of_not_dvd hqPrime.ne_zero hpPrime
        hpNot hqSmooth hpS
    · exact maxPrimeExponent_mul_prime_of_not_dvd hqPrime.ne_zero hpPrime
        hpNot hE hqExp
    · rw [ArithmeticFunction.cardFactors_mul hqPrime.ne_zero hpPrime.ne_zero,
        ArithmeticFunction.cardFactors_apply_prime hpPrime]
      exact hqFactor
  rw [mem_activePrimePowers]
  refine ⟨hqPrime.isPrimePow, q * p, ?_, dvd_mul_right q p, ?_⟩
  · exact hnGood
  · have hcop : q.Coprime p :=
      (hpPrime.coprime_iff_not_dvd.mpr hpNot).symm
    simpa [hqPrime.ne_zero] using hcop

/-- The bridge modulus divides the active LCM of the good set. -/
theorem eventually_bridgeModulus_dvd_activeLcm :
    ∀ᶠ N : ℕ in atTop,
      bridgeModulus N ∣ activeLcm (goodSet N) := by
  filter_upwards [eventually_primesHalfFull_subset_activePrimePowers] with N hsub
  have hprime : ∀ q ∈ primesHalfFull (S N), q.Prime := by
    intro q hq
    exact (mem_primesHalfFull.mp hq).2.2
  have hpair : (primesHalfFull (S N) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  rw [bridgeModulus, ← Finset.lcm_eq_prod hpair]
  exact lcm_subset_dvd_activeLcm hsub

/-! ## Transporting bridge primes to a larger scale -/

/-- At a large scale, every prime `q ≥ 3` below both the smoothness cutoff
and half the safe factorization cutoff divides some source-good denominator.
Exactness is unnecessary here: the active LCM equals the ordinary denominator
LCM on the positive good set. -/
theorem eventually_prime_dvd_goodSet :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ,
      q.Prime → 3 ≤ q → q ≤ S N → 2 * q ≤ KSafe N →
      ∃ n ∈ goodSet N, q ∣ n := by
  filter_upwards [eventually_two_hundred_le_S,
    eventually_hundred_mul_KSafe_le_S_sq,
    eventually_five_le_card_primesHalfFull_S,
    eventually_auxiliaryPrimes_band_budget,
    eventually_good_multiple_of_baseExtension,
    tendsto_logLogScale.eventually_ge_atTop 1] with
      N hS200 hKSsq hhalf hband hmultiple hLL
  intro q hqPrime hqThree hqS hqK
  have hE : 1 ≤ exponentBound N := by
    rw [exponentBound]
    apply Nat.le_floor
    simpa [logLogScale, logScale] using
      (show (1 : ℝ) ≤ 5 * logLogScale N by linarith)
  have htwoPrime : Nat.Prime 2 := Nat.prime_two
  have htwoCop : (2 : ℕ).Coprime q := by
    exact (Nat.coprime_primes htwoPrime hqPrime).mpr (by omega)
  have hcards : ExtensionCardConditions (S N) (KSafe N) (q * 2) := by
    apply extensionCardConditions_of_quadratic_bounds hS200
      (by simpa [pow_two] using hKSsq) (by nlinarith) _ hhalf
    have hqOmega : ω q = 1 := by
      rw [ArithmeticFunction.cardDistinctFactors_apply_prime hqPrime]
    rw [ArithmeticFunction.cardDistinctFactors_mul htwoCop.symm,
      hqOmega, ArithmeticFunction.cardDistinctFactors_apply_prime htwoPrime]
  obtain ⟨base, hbaseSmall⟩ := exists_baseExtension_of_card_conditions
    hqPrime (by norm_num : 1 ≤ (1 : ℕ)) (by simp) (by simpa using hE) hE
    hqS htwoPrime htwoCop (by omega) (by simpa [Nat.mul_comm] using hqK) hcards
  have hbase0 : base.base ≠ 0 := by
    have := base.lower
    omega
  have hbaseCard : base.base.primeFactors.card ≤ 4 := by
    rw [card_primeFactors_eq_omega]
    exact base.distinct
  have hauxFive : 5 ≤ (auxiliaryPrimes N).card := by
    omega
  have hcard : base.base.primeFactors.card < (auxiliaryPrimes N).card :=
    hbaseCard.trans_lt hauxFive
  obtain ⟨p, hpPrime, hpLower, hpUpper, hpNot⟩ :=
    exists_prime_in_interval_not_dvd hbase0 (by
      simpa [auxiliaryPrimes] using hcard)
  have hpAux : p ∈ auxiliaryPrimes N := by
    rw [mem_auxiliaryPrimes]
    exact ⟨hpLower, hpUpper, hpPrime⟩
  have hpCop : p.Coprime base.base := hpPrime.coprime_iff_not_dvd.mpr hpNot
  obtain ⟨n, hn, -, -, hbasepn⟩ := hmultiple base hpAux hpCop
  refine ⟨n, by simpa [goodSet] using hn, ?_⟩
  exact base.q_dvd.trans ((dvd_mul_right base.base p).trans hbasepn)

/-- A finite family of primes satisfying the transported supply bounds has
product dividing the active LCM. -/
theorem eventually_primeProduct_dvd_activeLcm :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ,
      (∀ q ∈ P, q.Prime ∧ 3 ≤ q ∧ q ≤ S N ∧ 2 * q ≤ KSafe N) →
      P.prod id ∣ activeLcm (goodSet N) := by
  filter_upwards [eventually_prime_dvd_goodSet, eventually_one_le_M] with
      N hsupply hM
  intro P hP
  have hpair : (P : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hP p hp).1 (hP q hq).1).mpr hpq
  rw [← Finset.lcm_eq_prod hpair]
  rw [activeLcm_eq_lcm]
  · apply Finset.lcm_dvd
    intro q hq
    obtain ⟨n, hn, hqn⟩ := hsupply q (hP q hq).1 (hP q hq).2.1
      (hP q hq).2.2.1 (hP q hq).2.2.2
    exact hqn.trans (Finset.dvd_lcm hn)
  · intro hzero
    have hz : 0 ∈ goodDenominators N (M N) (S N) := by
      simpa [goodSet] using hzero
    have := goodDenominator_pos hM hz
    omega

/-! ## Size of the bridge -/

/-- The squarefree bridge already has exponential size in `S`. -/
theorem eventually_exp_S_div_twenty_le_bridgeModulus :
    ∀ᶠ N : ℕ in atTop,
      Real.exp ((S N : ℝ) / 20) ≤ (bridgeModulus N : ℝ) := by
  have hcount := Erdos297.AuxiliarySupply.tendsto_S_atTop.eventually
    eventually_div_ten_log_le_card_primesHalfFull
  filter_upwards [hcount,
    Erdos297.AuxiliarySupply.tendsto_S_atTop.eventually_ge_atTop 9] with
      N hcard hS
  let P := primesHalfFull (S N)
  have hSpos : (0 : ℝ) < S N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 9) hS)
  have hlogS : 0 < Real.log (S N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < S N)
  have hprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    exact (mem_primesHalfFull.mp hq).2.2
  have hlogProd : Real.log (P.prod id : ℕ) =
      ∑ q ∈ P, Real.log (q : ℝ) := by
    push_cast
    rw [Real.log_prod]
    · simp
    · intro q hq
      exact_mod_cast (hprime q hq).ne_zero
  have hterm : ∀ q ∈ P,
      Real.log (S N : ℝ) / 2 ≤ Real.log (q : ℝ) := by
    intro q hq
    have hqData := mem_primesHalfFull.mp hq
    have hScmp : S N ≤ 3 * q := by
      have : S N ≤ 3 * (S N / 2) := by omega
      exact this.trans (Nat.mul_le_mul_left 3 hqData.1)
    have hqThree : 3 ≤ q := by
      have hhalf : 3 ≤ S N / 2 := by omega
      exact hhalf.trans hqData.1
    have hSq : S N ≤ q ^ 2 := by
      calc
        S N ≤ 3 * q := hScmp
        _ ≤ q * q := Nat.mul_le_mul_right q hqThree
        _ = q ^ 2 := by ring
    have hlogSq : Real.log (S N : ℝ) ≤ Real.log ((q : ℝ) ^ 2) := by
      apply Real.log_le_log hSpos
      exact_mod_cast hSq
    rw [Real.log_pow] at hlogSq
    have hlogSq' : Real.log (S N : ℝ) ≤
        2 * Real.log (q : ℝ) := by
      norm_num at hlogSq ⊢
      exact hlogSq
    calc
      Real.log (S N : ℝ) / 2 ≤ (2 * Real.log (q : ℝ)) / 2 := by
        gcongr
      _ = Real.log (q : ℝ) := by ring
  have hsum : ((P.card : ℝ) * (Real.log (S N : ℝ) / 2)) ≤
      ∑ q ∈ P, Real.log (q : ℝ) := by
    calc
      (P.card : ℝ) * (Real.log (S N : ℝ) / 2) =
          ∑ _q ∈ P, Real.log (S N : ℝ) / 2 := by simp
      _ ≤ ∑ q ∈ P, Real.log (q : ℝ) :=
        Finset.sum_le_sum hterm
  have hcard' : (S N : ℝ) / (10 * Real.log (S N : ℝ)) ≤
      (P.card : ℝ) := by simpa [P] using hcard
  have hmain : (S N : ℝ) / 20 ≤
      ∑ q ∈ P, Real.log (q : ℝ) := by
    calc
      (S N : ℝ) / 20 =
          ((S N : ℝ) / (10 * Real.log (S N : ℝ))) *
            (Real.log (S N : ℝ) / 2) := by
        field_simp [hlogS.ne']
        norm_num
      _ ≤ (P.card : ℝ) * (Real.log (S N : ℝ) / 2) := by gcongr
      _ ≤ ∑ q ∈ P, Real.log (q : ℝ) := hsum
  have hprodPos : (0 : ℝ) < (P.prod id : ℕ) := by
    exact_mod_cast Finset.prod_pos fun q hq ↦ (hprime q hq).pos
  calc
    Real.exp ((S N : ℝ) / 20) ≤
        Real.exp (Real.log (P.prod id : ℕ)) := by
      exact Real.exp_le_exp.mpr (hmain.trans_eq hlogProd.symm)
    _ = (P.prod id : ℕ) := Real.exp_log hprodPos
    _ = (bridgeModulus N : ℝ) := by rfl

end

end Erdos294.Bridge
