/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpSupply
import ErdosProblems.Erdos297.AuxiliaryEventual

/-! # Eventual auxiliary-prime data for the corrected cutoff -/

namespace Erdos294.SharpAuxiliaryEventual

open Filter Finset Real
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos297 Erdos297.ActiveLcm Erdos297.AuxiliaryDataSupply
open Erdos297.AuxiliarySupply Erdos297.GoodFactorization
open Erdos297.MinorArc Erdos297.NearbyMultiple Erdos297.PrimeIntervals
open Erdos297.SupplyNumerics
open Erdos297.AuxiliaryEventual
open Erdos294.SharpParameters Erdos294.SharpSupply

/-- The repaired auxiliary-prime construction at constant width. -/
theorem eventually_active_auxiliaryData :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℤ,
      let A := sharpGoodSet N
      let D := goodModuliOn (activePrimePowers A) A h (KSafe N)
        (minorThreshold N)
      Nonempty (AuxiliaryData D (nearbyLower h (KSafe N))
        (nearbyUpper h (KSafe N)) N) := by
  filter_upwards [eventually_one_le_sharpM_and_sharpM_le_N,
      eventually_sharp_safe_scale_chain,
      tendsto_logLogScale.eventually_ge_atTop 1,
      eventually_minorThreshold_candidate_budget_sharp,
      eventually_sharpS_mul_smallPrimeCutoff_le_KSafe,
      eventually_smallPrimeCutoff_le_sharpS,
      eventually_two_hundred_le_sharpS,
      eventually_hundred_mul_KSafe_le_sharpS_sq,
      eventually_five_le_card_primesHalfFull_sharpS,
      eventually_auxiliaryPrimes_band_budget,
      eventually_good_multiple_of_sharpBaseExtension,
      eventually_product_auxiliaryPrimes_dense]
      with N hM hchain hLL hcandidate hSX hXS hS200 hKSsq hhalf
        hdensity hmultiple hlargeProduct
  intro h
  let A := sharpGoodSet N
  let D := goodModuliOn (activePrimePowers A) A h (KSafe N)
    (minorThreshold N)
  have hAsub : A ⊆ goodDenominators N (sharpM N) (sharpS N) := by
    simp [A, sharpGoodSet]
  have hactive : ∀ q ∈ D, ∃ a k : ℕ,
      a.Prime ∧ 1 ≤ k ∧ q = a ^ k ∧
        k ≤ exponentBound N ∧ q ≤ sharpS N := by
    intro q hqD
    have hqA : q ∈ activePrimePowers A := (mem_goodModuliOn.mp hqD).1
    obtain ⟨a, k, ha, hk, hqpow, hkE⟩ :=
      activePrimePower_exponent_le hM.1 hAsub hqA
    exact ⟨a, k, ha, hk, hqpow, hkE,
      activePrimePower_le_smoothCutoff hM.1 hAsub hqA⟩
  have hE : 1 ≤ exponentBound N := by
    rw [exponentBound]
    apply Nat.le_floor
    simpa [logLogScale, logScale] using
      (show (1 : ℝ) ≤ 5 * logLogScale N by linarith)
  have hA0 : ∀ n ∈ A, n ≠ 0 := by
    intro n hn
    exact (goodDenominator_pos hM.1 (hAsub hn)).ne'
  have hAF : ∀ n ∈ A, Ω n ≤ factorBound N := by
    intro n hn
    exact goodDenominator_factorBound (hAsub hn)
  have hcandidateBudget : ∀ q ∈ D,
      (divisiblePart A q \ nearbySet A h (KSafe N) q).card *
          factorBound N <
        (AuxiliarySupply.smallPrimeCandidates (smallPrimeCutoff N) q).card *
          (fiberBudget N + 1) := by
    intro q hqD
    have hqA : q ∈ activePrimePowers A := (mem_goodModuliOn.mp hqD).1
    have hfar :
        (divisiblePart A q \ nearbySet A h (KSafe N) q).card <
          minorThreshold N := by
      rw [← farSet_eq_sdiff_nearbySet]
      exact (mem_goodModuliOn.mp hqD).2
    have hcard :
        (divisiblePart A q \ nearbySet A h (KSafe N) q).card ≤
          minorThreshold N - 1 := by omega
    have hbudget := hcandidate q (by simpa [A] using hqA)
    calc
      (divisiblePart A q \ nearbySet A h (KSafe N) q).card *
          factorBound N ≤ (minorThreshold N - 1) * factorBound N :=
        Nat.mul_le_mul_right (factorBound N) hcard
      _ = factorBound N * (minorThreshold N - 1) := by ac_rfl
      _ < (AuxiliarySupply.smallPrimeCandidates (smallPrimeCutoff N) q).card *
          (fiberBudget N + 1) := by
        simpa [AuxiliarySupply.smallPrimeCandidates,
          SupplyNumerics.smallPrimeCandidates] using hbudget
  have hqXK : ∀ q ∈ D, q * smallPrimeCutoff N ≤ KSafe N := by
    intro q hqD
    have hqA : q ∈ activePrimePowers A := (mem_goodModuliOn.mp hqD).1
    calc
      q * smallPrimeCutoff N ≤ sharpS N * smallPrimeCutoff N :=
        Nat.mul_le_mul_right (smallPrimeCutoff N)
          (activePrimePower_le_smoothCutoff hM.1 hAsub hqA)
      _ ≤ KSafe N := hSX
  have hcards : ∀ q ∈ D,
      ∀ p' ∈ AuxiliarySupply.smallPrimeCandidates (smallPrimeCutoff N) q,
        ExtensionCardConditions (sharpS N) (KSafe N) (q * p') := by
    intro q hqD p' hp'
    obtain ⟨a, k, ha, hk, hqpow, hkE, hqS⟩ := hactive q hqD
    have hp'Data := AuxiliarySupply.mem_smallPrimeCandidates.mp hp'
    have hd : 4 ≤ q * p' := by
      have hqTwo : 2 ≤ q := by
        rw [hqpow]
        exact ha.two_le.trans (Nat.le_pow hk)
      calc
        4 = 2 * 2 := by norm_num
        _ ≤ q * p' := Nat.mul_le_mul hqTwo hp'Data.1
    have hdomega : ω (q * p') ≤ 2 := by
      have hcop : q.Coprime p' := hp'Data.2.2.2.symm
      rw [ArithmeticFunction.cardDistinctFactors_mul hcop, hqpow,
        ArithmeticFunction.cardDistinctFactors_apply_prime_pow ha (by omega),
        ArithmeticFunction.cardDistinctFactors_apply_prime hp'Data.2.2.1]
    exact extensionCardConditions_of_quadratic_bounds hS200
      (by simpa [pow_two] using hKSsq) hd hdomega hhalf
  have hPprime : ∀ p ∈ auxiliaryPrimes N, p.Prime := by
    intro p hp
    exact (mem_auxiliaryPrimes.mp hp).2.2
  have hgoodMultiple : ∀ q ∈ D,
      ∀ base : BaseExtension N (sharpS N) (KSafe N) q,
      ∀ p ∈ auxiliaryPrimes N, p.Coprime base.base →
        (divisiblePart A (base.base * p)).Nonempty := by
    intro q hqD base p hpP hcop
    obtain ⟨n, hnA, hnLower, hnUpper, hdvd⟩ := hmultiple base hpP hcop
    exact ⟨n, mem_divisiblePart.mpr ⟨by simpa [A] using hnA, hdvd⟩⟩
  have hnearby : ∀ q ∈ D, ∀ n ∈ nearbySet A h (KSafe N) q,
      ∃ x : ℤ, InHalfOpenInterval (nearbyLower h (KSafe N))
        (nearbyUpper h (KSafe N)) x ∧ (n : ℤ) ∣ x := by
    intro q hqD n hn
    exact nearbySet_has_interval_multiple hn
  have hKpos : 0 < KSafe N := by omega
  have hKN : KSafe N ≤ N := hchain.2.1.trans hchain.2.2
  exact exists_auxiliaryData_of_card_conditions
    (N := N) (S := sharpS N) (K := KSafe N)
    (X := smallPrimeCutoff N) (F := factorBound N) (B := fiberBudget N)
    (A := A) (D := D) (P := auxiliaryPrimes N)
    (h := h) (lower := nearbyLower h (KSafe N))
    (upper := nearbyUpper h (KSafe N))
    hactive hE hA0 hAF hcandidateBudget hXS hqXK hcards hPprime
    hdensity hgoodMultiple hnearby
    ⟨h, self_mem_nearbyInterval hKpos⟩
    (by rw [nearbyInterval_width]) hKN hlargeProduct

theorem eventually_nearbyMultiplePair :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℤ,
      let A := sharpGoodSet N
      let D := goodModuliOn (activePrimePowers A) A h (KSafe N)
        (minorThreshold N)
      nearbyMultiplePair (KSafe N) (D.lcm id) h := by
  filter_upwards [eventually_active_auxiliaryData] with N hdata
  intro h
  dsimp only
  obtain ⟨data⟩ := hdata h
  exact nearbyMultiplePair_lcm_of_auxiliaryData data
    (fun z hz ↦ abs_sub_center_le_of_mem_nearbyInterval hz)

end

end Erdos294.SharpAuxiliaryEventual

#print axioms Erdos294.SharpAuxiliaryEventual.eventually_active_auxiliaryData
