/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.AuxiliaryDataSupply
import ErdosProblems.Erdos297.SupplyNumerics

/-!
# Eventual auxiliary-prime supply for Erdős Problem 297

This file specializes the repaired finite sieve to the concrete safe scale.
The interval endpoints below are the integral version of
`(h - K/2, h + K/2]`; their asymmetric rounding gives exact width `K`.
-/

namespace Erdos297.AuxiliaryEventual

open Filter Finset Real
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

open ActiveLcm AuxiliaryDataSupply AuxiliarySupply GoodFactorization
open LogisticNormalization MinorArc NearbyMultiple PrimeIntervals SupplyNumerics

/-- Lower endpoint of the integral nearby interval. -/
def nearbyLower (h : ℤ) (K : ℕ) : ℤ :=
  h - ((K + 1) / 2 : ℕ)

/-- Upper endpoint of the integral nearby interval. -/
def nearbyUpper (h : ℤ) (K : ℕ) : ℤ :=
  h + (K / 2 : ℕ)

lemma nearbyInterval_width (h : ℤ) (K : ℕ) :
    nearbyUpper h K - nearbyLower h K = (K : ℤ) := by
  dsimp [nearbyUpper, nearbyLower]
  push_cast
  omega

lemma self_mem_nearbyInterval {h : ℤ} {K : ℕ} (hK : 0 < K) :
    InHalfOpenInterval (nearbyLower h K) (nearbyUpper h K) h := by
  rw [InHalfOpenInterval]
  dsimp [nearbyLower, nearbyUpper]
  constructor <;> push_cast <;> omega

lemma sub_mem_nearbyInterval_of_abs_cast_lt {h r : ℤ} {K : ℕ}
    (hr : |(r : ℝ)| < (K : ℝ) / 2) :
    InHalfOpenInterval (nearbyLower h K) (nearbyUpper h K) (h - r) := by
  have hrBounds := abs_lt.mp hr
  have hrUpper : r < (((K + 1) / 2 : ℕ) : ℤ) := by
    by_contra hnot
    have hge : (((K + 1) / 2 : ℕ) : ℤ) ≤ r := le_of_not_gt hnot
    have hceilNat : K ≤ 2 * ((K + 1) / 2) := by omega
    have hgeR : ((((K + 1) / 2 : ℕ) : ℤ) : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast hge
    have hceilR : (K : ℝ) ≤
        2 * ((((K + 1) / 2 : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast hceilNat
    linarith
  have hrLower : -(((K / 2 : ℕ) : ℤ)) ≤ r := by
    by_contra hnot
    let m := K / 2
    have hlt : r < -((m : ℕ) : ℤ) := by simpa [m] using lt_of_not_ge hnot
    have hle : r ≤ -((m : ℕ) : ℤ) - 1 := by omega
    have hleR : (r : ℝ) ≤
        -((((m : ℕ) : ℤ) : ℝ)) - 1 := by
      exact_mod_cast hle
    have hrem : K = 2 * m ∨ K = 2 * m + 1 := by
      dsimp [m]
      omega
    rcases hrem with hKeven | hKodd
    · rw [hKeven] at hrBounds
      push_cast at hrBounds hleR
      norm_num at hrBounds hleR
      linarith
    · rw [hKodd] at hrBounds
      push_cast at hrBounds hleR
      norm_num at hrBounds hleR
      linarith
  rw [InHalfOpenInterval]
  dsimp [nearbyLower, nearbyUpper]
  constructor <;> push_cast <;> omega

lemma centeredResidue_complement_dvd (h : ℤ) (n : ℕ) :
    (n : ℤ) ∣ h - centeredResidue h n := by
  refine ⟨round ((h : ℝ) / n), ?_⟩
  simp [centeredResidue]

lemma nearbySet_has_interval_multiple {A : Finset ℕ} {h : ℤ} {K q n : ℕ}
    (hn : n ∈ nearbySet A h K q) :
    ∃ x : ℤ, InHalfOpenInterval (nearbyLower h K) (nearbyUpper h K) x ∧
      (n : ℤ) ∣ x := by
  refine ⟨h - centeredResidue h n, ?_, centeredResidue_complement_dvd h n⟩
  exact sub_mem_nearbyInterval_of_abs_cast_lt (mem_nearbySet.mp hn).2.2

lemma abs_sub_center_le_of_mem_nearbyInterval {h z : ℤ} {K : ℕ}
    (hz : InHalfOpenInterval (nearbyLower h K) (nearbyUpper h K) z) :
    |z - h| ≤ (K : ℤ) := by
  rw [InHalfOpenInterval] at hz
  dsimp [nearbyLower, nearbyUpper] at hz
  rw [abs_le]
  constructor <;> push_cast at hz ⊢ <;> omega

/-- The repaired auxiliary-prime construction, specialized to the exact
active prime powers, ceiling threshold, and safe factorization scale used in
the local-limit argument. -/
theorem eventually_active_auxiliaryData :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℤ,
      let A := goodSet N
      let D := goodModuliOn (activePrimePowers A) A h (KSafe N)
        (minorThreshold N)
      Nonempty (AuxiliaryData D (nearbyLower h (KSafe N))
        (nearbyUpper h (KSafe N)) N) := by
  filter_upwards [eventually_one_le_M_and_M_le_N,
      eventually_nat_safe_scale_chain,
      tendsto_logLogScale.eventually_ge_atTop 1,
      eventually_minorThreshold_smallPrimeCandidates_budget,
      eventually_S_mul_smallPrimeCutoff_le_KSafe,
      eventually_smallPrimeCutoff_le_S,
      eventually_two_hundred_le_S,
      eventually_hundred_mul_KSafe_le_S_sq,
      eventually_five_le_card_primesHalfFull_S,
      eventually_auxiliaryPrimes_band_budget,
      eventually_good_multiple_of_baseExtension,
      eventually_product_auxiliaryPrimes_dense]
      with N hM hchain hLL hcandidate hSX hXS hS200 hKSsq hhalf
        hdensity hmultiple hlargeProduct
  intro h
  let A := goodSet N
  let D := goodModuliOn (activePrimePowers A) A h (KSafe N)
    (minorThreshold N)
  have hAsub : A ⊆ goodDenominators N (M N) (S N) := by
    simp [A, goodSet]
  have hactive : ∀ q ∈ D, ∃ a k : ℕ,
      a.Prime ∧ 1 ≤ k ∧ q = a ^ k ∧
        k ≤ exponentBound N ∧ q ≤ S N := by
    intro q hqD
    have hqA : q ∈ activePrimePowers A :=
      (mem_goodModuliOn.mp hqD).1
    obtain ⟨a, k, ha, hk, hqpow, hkE⟩ :=
      activePrimePower_exponent_le hM.1 hAsub hqA
    exact ⟨a, k, ha, hk, hqpow,
      hkE, activePrimePower_le_smoothCutoff hM.1 hAsub hqA⟩
  have hE : 1 ≤ exponentBound N := by
    rw [exponentBound]
    apply Nat.le_floor
    have : (1 : ℝ) ≤ 5 * logLogScale N := by linarith
    simpa [logLogScale, logScale] using this
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
    have hqA : q ∈ activePrimePowers A :=
      (mem_goodModuliOn.mp hqD).1
    have hfar :
        (divisiblePart A q \ nearbySet A h (KSafe N) q).card <
          minorThreshold N := by
      rw [← farSet_eq_sdiff_nearbySet]
      exact (mem_goodModuliOn.mp hqD).2
    have hcard :
        (divisiblePart A q \ nearbySet A h (KSafe N) q).card ≤
          minorThreshold N - 1 := by omega
    have hbudget := hcandidate q (by simpa [A, goodSet] using hqA)
    calc
      (divisiblePart A q \ nearbySet A h (KSafe N) q).card *
          factorBound N ≤
          (minorThreshold N - 1) * factorBound N :=
        Nat.mul_le_mul_right (factorBound N) hcard
      _ = factorBound N * (minorThreshold N - 1) := by ac_rfl
      _ < (AuxiliarySupply.smallPrimeCandidates (smallPrimeCutoff N) q).card *
          (fiberBudget N + 1) := by
        simpa [AuxiliarySupply.smallPrimeCandidates,
          SupplyNumerics.smallPrimeCandidates] using hbudget
  have hqXK : ∀ q ∈ D, q * smallPrimeCutoff N ≤ KSafe N := by
    intro q hqD
    have hqA : q ∈ activePrimePowers A :=
      (mem_goodModuliOn.mp hqD).1
    calc
      q * smallPrimeCutoff N ≤ S N * smallPrimeCutoff N :=
        Nat.mul_le_mul_right (smallPrimeCutoff N)
          (activePrimePower_le_smoothCutoff hM.1 hAsub hqA)
      _ ≤ KSafe N := hSX
  have hcards : ∀ q ∈ D,
      ∀ p' ∈ AuxiliarySupply.smallPrimeCandidates (smallPrimeCutoff N) q,
        ExtensionCardConditions (S N) (KSafe N) (q * p') := by
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
      rw [ArithmeticFunction.cardDistinctFactors_mul hcop,
        hqpow,
        ArithmeticFunction.cardDistinctFactors_apply_prime_pow ha (by omega),
        ArithmeticFunction.cardDistinctFactors_apply_prime hp'Data.2.2.1]
    exact extensionCardConditions_of_quadratic_bounds hS200
      (by simpa [pow_two] using hKSsq) hd hdomega hhalf
  have hPprime : ∀ p ∈ auxiliaryPrimes N, p.Prime := by
    intro p hp
    exact (mem_auxiliaryPrimes.mp hp).2.2
  have hgoodMultiple : ∀ q ∈ D,
      ∀ base : BaseExtension N (S N) (KSafe N) q,
      ∀ p ∈ auxiliaryPrimes N, p.Coprime base.base →
        (divisiblePart A (base.base * p)).Nonempty := by
    intro q hqD base p hpP hcop
    obtain ⟨n, hnA, hnLower, hnUpper, hdvd⟩ := hmultiple base hpP hcop
    exact ⟨n, mem_divisiblePart.mpr ⟨by simpa [A, goodSet] using hnA, hdvd⟩⟩
  have hnearby : ∀ q ∈ D, ∀ n ∈ nearbySet A h (KSafe N) q,
      ∃ x : ℤ, InHalfOpenInterval (nearbyLower h (KSafe N))
        (nearbyUpper h (KSafe N)) x ∧ (n : ℤ) ∣ x := by
    intro q hqD n hn
    exact nearbySet_has_interval_multiple hn
  have hSK : S N ≤ KSafe N := by exact_mod_cast hchain.1
  have hKpos : 0 < KSafe N := by omega
  have hKN : KSafe N ≤ N := by
    have hKM : KSafe N ≤ M N := by exact_mod_cast hchain.2.1
    exact hKM.trans hM.2
  exact exists_auxiliaryData_of_card_conditions
    (N := N) (S := S N) (K := KSafe N)
    (X := smallPrimeCutoff N) (F := factorBound N) (B := fiberBudget N)
    (A := A) (D := D) (P := auxiliaryPrimes N)
    (h := h) (lower := nearbyLower h (KSafe N))
    (upper := nearbyUpper h (KSafe N))
    hactive hE hA0 hAF hcandidateBudget hXS hqXK hcards hPprime
    hdensity hgoodMultiple hnearby
    ⟨h, self_mem_nearbyInterval hKpos⟩
    (by rw [nearbyInterval_width]) hKN hlargeProduct

/-- Common-nearby-multiple output of the concrete eventual supply. -/
theorem eventually_commonNearbyMultiple :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℤ,
      let A := goodSet N
      let D := goodModuliOn (activePrimePowers A) A h (KSafe N)
        (minorThreshold N)
      ∃ z : ℤ,
        InHalfOpenInterval (nearbyLower h (KSafe N))
          (nearbyUpper h (KSafe N)) z ∧
        ((D.lcm id : ℕ) : ℤ) ∣ z := by
  filter_upwards [eventually_active_auxiliaryData] with N hdata
  intro h
  dsimp only
  let A := goodSet N
  let D := goodModuliOn (activePrimePowers A) A h (KSafe N)
    (minorThreshold N)
  obtain ⟨data⟩ := hdata h
  obtain ⟨z, hz, hq, hlcm⟩ :=
    commonNearbyMultiple_of_auxiliaryData data
  exact ⟨z, hz, hlcm⟩

/-- Predicate-level form consumed directly by the minor-frequency fiber
count. -/
theorem eventually_nearbyMultiplePair :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℤ,
      let A := goodSet N
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

end Erdos297.AuxiliaryEventual

#print axioms Erdos297.AuxiliaryEventual.eventually_active_auxiliaryData
#print axioms Erdos297.AuxiliaryEventual.eventually_nearbyMultiplePair
