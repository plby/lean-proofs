/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpRepresentation
import ErdosProblems.Erdos297.AuxiliarySupply

/-! # Bridge modulus for the corrected cutoff -/

open Filter Finset Real
open scoped ArithmeticFunction.omega BigOperators Topology

namespace Erdos294.SharpBridge

open Erdos297 Erdos297.ActiveLcm Erdos297.AuxiliarySupply
open Erdos297.GoodFactorization Erdos297.PrimeIntervals
open Erdos297.SupplyNumerics
open Erdos294.SharpParameters Erdos294.SharpSupply

noncomputable section

attribute [local instance] Classical.propDecidable

def bridgeModulus (N : ℕ) : ℕ := (primesHalfFull (sharpS N)).prod id

theorem eventually_prime_dvd_sharpGoodSet :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ,
      q.Prime → 3 ≤ q → q ≤ sharpS N → 2 * q ≤ KSafe N →
      ∃ n ∈ sharpGoodSet N, q ∣ n := by
  filter_upwards [eventually_two_hundred_le_sharpS,
      eventually_hundred_mul_KSafe_le_sharpS_sq,
      eventually_five_le_card_primesHalfFull_sharpS,
      eventually_auxiliaryPrimes_band_budget,
      eventually_good_multiple_of_sharpBaseExtension,
      tendsto_logLogScale.eventually_ge_atTop 1] with
      N hS200 hKSsq hhalf hband hmultiple hLL
  intro q hqPrime hqThree hqS hqK
  have hE : 1 ≤ exponentBound N := by
    rw [exponentBound]
    apply Nat.le_floor
    simpa [logLogScale, logScale] using
      (show (1 : ℝ) ≤ 5 * logLogScale N by linarith)
  have htwoPrime : Nat.Prime 2 := Nat.prime_two
  have htwoCop : (2 : ℕ).Coprime q :=
    (Nat.coprime_primes htwoPrime hqPrime).mpr (by omega)
  have hcards : ExtensionCardConditions (sharpS N) (KSafe N) (q * 2) := by
    apply extensionCardConditions_of_quadratic_bounds hS200
      (by simpa [pow_two] using hKSsq) (by nlinarith) _ hhalf
    have hqOmega : ω q = 1 := by
      rw [ArithmeticFunction.cardDistinctFactors_apply_prime hqPrime]
    rw [ArithmeticFunction.cardDistinctFactors_mul htwoCop.symm,
      hqOmega, ArithmeticFunction.cardDistinctFactors_apply_prime htwoPrime]
  obtain ⟨base, hbaseSmall⟩ := exists_baseExtension_of_card_conditions
    hqPrime (by norm_num : 1 ≤ (1 : ℕ)) (by simp) (by simpa using hE) hE
    hqS htwoPrime htwoCop (by omega) (by simpa [Nat.mul_comm] using hqK) hcards
  have hbase0 : base.base ≠ 0 := by have := base.lower; omega
  have hbaseCard : base.base.primeFactors.card ≤ 4 := by
    rw [card_primeFactors_eq_omega]
    exact base.distinct
  have hauxFive : 5 ≤ (auxiliaryPrimes N).card := by omega
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
  exact ⟨n, hn, base.q_dvd.trans ((dvd_mul_right base.base p).trans hbasepn)⟩

theorem eventually_primeProduct_dvd_sharpActiveLcm :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ,
      (∀ q ∈ P, q.Prime ∧ 3 ≤ q ∧ q ≤ sharpS N ∧ 2 * q ≤ KSafe N) →
      P.prod id ∣ activeLcm (sharpGoodSet N) := by
  filter_upwards [eventually_prime_dvd_sharpGoodSet,
      eventually_one_le_sharpM_and_sharpM_le_N] with N hsupply hM
  intro P hP
  have hpair : (P : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hP p hp).1 (hP q hq).1).mpr hpq
  rw [← Finset.lcm_eq_prod hpair, activeLcm_eq_lcm]
  · apply Finset.lcm_dvd
    intro q hq
    obtain ⟨n, hn, hqn⟩ := hsupply q (hP q hq).1 (hP q hq).2.1
      (hP q hq).2.2.1 (hP q hq).2.2.2
    exact hqn.trans (Finset.dvd_lcm hn)
  · intro hzero
    exact (goodDenominator_pos hM.1 (by simpa [sharpGoodSet] using hzero)).ne' rfl

theorem eventually_bridgeModulus_dvd_sharpActiveLcm :
    ∀ᶠ N : ℕ in atTop,
      bridgeModulus N ∣ activeLcm (sharpGoodSet N) := by
  filter_upwards [eventually_primeProduct_dvd_sharpActiveLcm,
      eventually_two_mul_sharpS_le_KSafe,
      eventually_two_hundred_le_sharpS] with N hsupply hSK hS
  apply hsupply
  intro q hq
  have hqData := mem_primesHalfFull.mp hq
  exact ⟨hqData.2.2, by omega, hqData.2.1,
    (Nat.mul_le_mul_left 2 hqData.2.1).trans hSK⟩

theorem eventually_exp_sharpS_div_twenty_le_bridgeModulus :
    ∀ᶠ N : ℕ in atTop,
      Real.exp ((sharpS N : ℝ) / 20) ≤ (bridgeModulus N : ℝ) := by
  have hcount := tendsto_sharpS_atTop.eventually
    eventually_div_ten_log_le_card_primesHalfFull
  filter_upwards [hcount, tendsto_sharpS_atTop.eventually_ge_atTop 9] with
      N hcard hS
  let P := primesHalfFull (sharpS N)
  have hSpos : (0 : ℝ) < sharpS N := by exact_mod_cast (by omega : 0 < sharpS N)
  have hlogS : 0 < Real.log (sharpS N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < sharpS N))
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
      Real.log (sharpS N : ℝ) / 2 ≤ Real.log (q : ℝ) := by
    intro q hq
    have hqData := mem_primesHalfFull.mp hq
    have hScmp : sharpS N ≤ 3 * q := by
      exact (show sharpS N ≤ 3 * (sharpS N / 2) by omega).trans
        (Nat.mul_le_mul_left 3 hqData.1)
    have hqThree : 3 ≤ q := (show 3 ≤ sharpS N / 2 by omega).trans hqData.1
    have hSq : sharpS N ≤ q ^ 2 := by
      calc
        sharpS N ≤ 3 * q := hScmp
        _ ≤ q * q := Nat.mul_le_mul_right q hqThree
        _ = q ^ 2 := by ring
    have hlogSq : Real.log (sharpS N : ℝ) ≤ Real.log ((q : ℝ) ^ 2) := by
      apply Real.log_le_log hSpos
      exact_mod_cast hSq
    rw [Real.log_pow] at hlogSq
    norm_num at hlogSq ⊢
    linarith
  have hsum : ((P.card : ℝ) * (Real.log (sharpS N : ℝ) / 2)) ≤
      ∑ q ∈ P, Real.log (q : ℝ) := by
    calc
      (P.card : ℝ) * (Real.log (sharpS N : ℝ) / 2) =
          ∑ _q ∈ P, Real.log (sharpS N : ℝ) / 2 := by simp
      _ ≤ ∑ q ∈ P, Real.log (q : ℝ) := Finset.sum_le_sum hterm
  have hcard' : (sharpS N : ℝ) /
      (10 * Real.log (sharpS N : ℝ)) ≤ (P.card : ℝ) := by
    simpa [P] using hcard
  have hmain : (sharpS N : ℝ) / 20 ≤
      ∑ q ∈ P, Real.log (q : ℝ) := by
    calc
      (sharpS N : ℝ) / 20 =
          ((sharpS N : ℝ) / (10 * Real.log (sharpS N : ℝ))) *
            (Real.log (sharpS N : ℝ) / 2) := by
        field_simp [hlogS.ne']
        norm_num
      _ ≤ (P.card : ℝ) * (Real.log (sharpS N : ℝ) / 2) := by gcongr
      _ ≤ ∑ q ∈ P, Real.log (q : ℝ) := hsum
  have hprodPos : (0 : ℝ) < (P.prod id : ℕ) := by
    exact_mod_cast Finset.prod_pos fun q hq ↦ (hprime q hq).pos
  calc
    Real.exp ((sharpS N : ℝ) / 20) ≤
        Real.exp (Real.log (P.prod id : ℕ)) :=
      Real.exp_le_exp.mpr (hmain.trans_eq hlogProd.symm)
    _ = (P.prod id : ℕ) := Real.exp_log hprodPos
    _ = (bridgeModulus N : ℝ) := by rfl

end

end Erdos294.SharpBridge
