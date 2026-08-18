/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos1149.Sieve
import ErdosProblems.Erdos1149.PowerDiscrepancy
import ErdosProblems.Erdos1149.FloorBridge

/-!
# The superlinear sieve reduction for Erdős Problem 1149

This file separates the finite combinatorics of the large-prime sieve from
the analytic discrepancy estimate.  In particular, it records the union
bound and the hyperbola split in a form that does not depend on the precise
constants furnished by the monomial-discrepancy theorem.
-/

namespace Erdos1149

open Filter
open scoped BigOperators

/-- The gcd whose value has to be one in Erdős Problem 1149. -/
noncomputable def powerFloorGCD (α : ℝ) (n : ℕ) : ℕ :=
  Nat.gcd n ⌊Real.rpow (n : ℝ) α⌋₊

/-- A prime window version of `largePrimeEvent`.  Unlike
`largePrimeEvent`, it has a finite witness range and is therefore directly
suited to a finite union bound. -/
def primeWindowEvent (ξ : ℕ → ℕ) (D U n : ℕ) : Prop :=
  0 < n ∧ ∃ p : ℕ, p.Prime ∧ D < p ∧ p ≤ U ∧ p ∣ ξ n

noncomputable instance primeWindowEvent.instDecidable
    (ξ : ℕ → ℕ) (D U n : ℕ) : Decidable (primeWindowEvent ξ D U n) :=
  Classical.propDecidable _

noncomputable instance largePrimeEvent.instDecidable
    (ξ : ℕ → ℕ) (D n : ℕ) : Decidable (largePrimeEvent ξ D n) :=
  Classical.propDecidable _

/-- The primes in the half-open numerical window `(D,U]`. -/
def primeWindow (D U : ℕ) : Finset ℕ :=
  (Finset.range (U + 1)).filter fun p ↦ p.Prime ∧ D < p

lemma mem_primeWindow {D U p : ℕ} :
    p ∈ primeWindow D U ↔ p.Prime ∧ D < p ∧ p ≤ U := by
  simp only [primeWindow, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  aesop

/-- The reciprocal-square mass of any prime window `(D,U]` is at most
`1/D`.  Primality is not used: this is the elementary telescoping
reciprocal-square tail. -/
lemma sum_primeWindow_inv_sq_le_inv (D U : ℕ) (hD : D ≠ 0) :
    (∑ p ∈ primeWindow D U, ((p : ℝ) ^ 2)⁻¹) ≤ (D : ℝ)⁻¹ := by
  classical
  have hsubset : primeWindow D U ⊆ Finset.Ioc D (max D U) := by
    intro p hp
    have hp' := mem_primeWindow.mp hp
    simp only [Finset.mem_Ioc]
    exact ⟨hp'.2.1, hp'.2.2.trans (le_max_right _ _)⟩
  calc
    (∑ p ∈ primeWindow D U, ((p : ℝ) ^ 2)⁻¹)
        ≤ ∑ p ∈ Finset.Ioc D (max D U), ((p : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ inv_nonneg.mpr (sq_nonneg _))
    _ ≤ (D : ℝ)⁻¹ - ((max D U : ℕ) : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub hD (le_max_left _ _)
    _ ≤ (D : ℝ)⁻¹ := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The finite prime-window event is exactly a union of local divisor
events. -/
lemma filter_primeWindowEvent_eq_biUnion (ξ : ℕ → ℕ) (D U N : ℕ) :
    (Finset.range N).filter (primeWindowEvent ξ D U) =
      (primeWindow D U).biUnion fun p ↦
        (Finset.range N).filter (localDivisorEvent ξ p) := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion,
    mem_primeWindow, primeWindowEvent, localDivisorEvent]
  constructor
  · rintro ⟨hnN, hn, p, hp, hDp, hpU, hpdvd⟩
    exact ⟨p, ⟨hp, hDp, hpU⟩, hnN, hn, hpdvd⟩
  · rintro ⟨p, ⟨hp, hDp, hpU⟩, hnN, hn, hpdvd⟩
    exact ⟨hnN, hn, p, hp, hDp, hpU, hpdvd⟩

/-- Union bound for a finite prime window. -/
theorem prefixCount_primeWindowEvent_le_sum_local (ξ : ℕ → ℕ)
    (D U N : ℕ) :
    prefixCount (primeWindowEvent ξ D U) N ≤
      ∑ p ∈ primeWindow D U, prefixCount (localDivisorEvent ξ p) N := by
  classical
  simp_rw [prefixCount_eq_ncard]
  let A : Set ℕ := {n | primeWindowEvent ξ D U n} ∩ Set.Iio N
  let B : ℕ → Set ℕ := fun p ↦ {n | localDivisorEvent ξ p n} ∩ Set.Iio N
  have hsub : A ⊆ ⋃ p ∈ (primeWindow D U : Set ℕ), B p := by
    rintro n ⟨hn, hnN⟩
    obtain ⟨hn0, p, hp, hDp, hpU, hpdvd⟩ := hn
    refine Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact (mem_primeWindow.mpr ⟨hp, hDp, hpU⟩)
    · exact ⟨⟨hn0, hpdvd⟩, hnN⟩
  have hfinite : (⋃ p ∈ (primeWindow D U : Set ℕ), B p).Finite := by
    apply (Set.finite_Iio N).subset
    intro n hn
    simp only [Set.mem_iUnion] at hn
    obtain ⟨p, hp⟩ := hn
    obtain ⟨hpwin, hnB⟩ := hp
    exact hnB.2
  calc
    A.ncard ≤ (⋃ p ∈ (primeWindow D U : Set ℕ), B p).ncard :=
      Set.ncard_le_ncard hsub hfinite
    _ ≤ ∑ p ∈ primeWindow D U, (B p).ncard := by
      simpa [Set.biUnion_insert, B] using
        (Finset.set_ncard_biUnion_le (primeWindow D U) B)

/-- Normalized real-valued union bound for a finite prime window. -/
theorem prefixRatio_primeWindowEvent_le_sum_local (ξ : ℕ → ℕ)
    (D U N : ℕ) :
    prefixRatio (primeWindowEvent ξ D U) N ≤
      ∑ p ∈ primeWindow D U, prefixRatio (localDivisorEvent ξ p) N := by
  rw [prefixRatio]
  have hnat := prefixCount_primeWindowEvent_le_sum_local ξ D U N
  have hreal : (prefixCount (primeWindowEvent ξ D U) N : ℝ) ≤
      ∑ p ∈ primeWindow D U,
        (prefixCount (localDivisorEvent ξ p) N : ℝ) := by
    exact_mod_cast hnat
  calc
    (prefixCount (primeWindowEvent ξ D U) N : ℝ) / N
        ≤ (∑ p ∈ primeWindow D U,
          (prefixCount (localDivisorEvent ξ p) N : ℝ)) / N :=
      div_le_div_of_nonneg_right hreal (Nat.cast_nonneg N)
    _ = ∑ p ∈ primeWindow D U,
          prefixRatio (localDivisorEvent ξ p) N := by
      simp_rw [prefixRatio, Finset.sum_div]

/-- For a sequence whose values divide their indices, every prime witness in
the prefix `[0,N)` is at most `N`.  Thus the unbounded large-prime event is
already the finite window `(D,N]`. -/
lemma filter_largePrimeEvent_eq_filter_primeWindowEvent
    (ξ : ℕ → ℕ) (hξ : ∀ n, ξ n ∣ n) (D N : ℕ) :
    (Finset.range N).filter (largePrimeEvent ξ D) =
      (Finset.range N).filter (primeWindowEvent ξ D N) := by
  classical
  apply Finset.ext
  intro n
  simp only [Finset.mem_filter, Finset.mem_range, largePrimeEvent,
    primeWindowEvent]
  constructor
  · rintro ⟨hnN, hn, p, hp, hDp, hpξ⟩
    have hpn : p ∣ n := hpξ.trans (hξ n)
    have hp0 : 0 < p := hp.pos
    have hple : p ≤ n := Nat.le_of_dvd hn hpn
    exact ⟨hnN, hn, p, hp, hDp, hple.trans hnN.le, hpξ⟩
  · rintro ⟨hnN, hn, p, hp, hDp, hpN, hpξ⟩
    exact ⟨hnN, hn, p, hp, hDp, hpξ⟩

lemma powerFloorGCD_dvd_index (α : ℝ) (n : ℕ) :
    powerFloorGCD α n ∣ n := by
  exact Nat.gcd_dvd_left _ _

/-- Number just beyond the last positive multiplier `m` for which
`d*m < N`. -/
def multipleIndexCutoff (N d : ℕ) : ℕ :=
  (N - 1) / d + 1

lemma tendsto_multipleIndexCutoff_atTop (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N ↦ multipleIndexCutoff N d) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  refine ⟨B * d + 1, ?_⟩
  intro N hN
  have hmul : B * d ≤ N - 1 := by omega
  have hdiv : B ≤ (N - 1) / d :=
    (Nat.le_div_iff_mul_le hd).mpr hmul
  simp only [multipleIndexCutoff]
  omega

/-- The number of positive multiples of `d` in `[0,N)` is asymptotic to
`N/d`.  This elementary quotient lemma is kept explicit because it is the
endpoint correction in every fixed-divisor density. -/
lemma tendsto_positiveMultipleCount_div (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ ↦ (((N - 1) / d : ℕ) : ℝ) / N) atTop
      (nhds (d : ℝ)⁻¹) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hinv : Tendsto (fun N : ℕ ↦ ((N : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, (N : ℝ)⁻¹ < ε :=
    hinv.eventually (Iio_mem_nhds hε)
  apply Filter.eventually_atTop.1
  filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with N hNinv hN
  let q := (N - 1) / d
  have hqd : q * d ≤ N - 1 := Nat.div_mul_le_self (N - 1) d
  have hNqd : N ≤ (q + 1) * d := by
    have hlt : N - 1 < (q + 1) * d := by
      apply (Nat.div_lt_iff_lt_mul hd).mp
      exact Nat.lt_succ_self q
    omega
  have hqdN : q * d ≤ N := hqd.trans (Nat.sub_le N 1)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  have hupper : (q : ℝ) / N ≤ (d : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hNr hdr).mpr
    simpa using (show (q : ℝ) * d ≤ (N : ℝ) by exact_mod_cast hqdN)
  have hlower : (d : ℝ)⁻¹ - (N : ℝ)⁻¹ ≤ (q : ℝ) / N := by
    rw [inv_eq_one_div, inv_eq_one_div]
    have hNqdR : (N : ℝ) ≤ ((q + 1) * d : ℕ) := by exact_mod_cast hNqd
    field_simp
    push_cast at hNqdR ⊢
    nlinarith
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  have hbound : (d : ℝ)⁻¹ - (q : ℝ) / N ≤ (N : ℝ)⁻¹ := by linarith
  simpa only [neg_sub] using hbound.trans_lt hNinv

/-- Exact finite reindexing of a local gcd-divisor count by its multiplier.
The sole arithmetic input `hbridge` is the floor/fractional-part bridge;
the rest of the statement is finite combinatorics. -/
theorem powerFloorGCD_local_prefixCount_eq_monomialIntervalCount_of_bridge
    (α : ℝ) (d N : ℕ) (hd : 0 < d)
    (hbridge : ∀ m : ℕ, 0 < m →
      (d ∣ ⌊Real.rpow ((d * m : ℕ) : ℝ) α⌋₊ ↔
        Int.fract ((d : ℝ) ^ (α - 1) * (m : ℝ) ^ α) < (d : ℝ)⁻¹)) :
    prefixCount (localDivisorEvent (powerFloorGCD α) d) N =
      monomialIntervalCount α ((d : ℝ) ^ (α - 1)) (d : ℝ)⁻¹
        1 (multipleIndexCutoff N d) := by
  classical
  unfold prefixCount monomialIntervalCount
  apply Finset.card_bij (fun n _ ↦ n / d)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, localDivisorEvent,
      powerFloorGCD, Nat.dvd_gcd_iff] at hn
    rcases hn with ⟨hnN, hn0, hdn, hdfloor⟩
    have hdnle : d ≤ n := Nat.le_of_dvd hn0 hdn
    have hq0 : 0 < n / d := Nat.div_pos hdnle hd
    have hnle : n ≤ N - 1 := by omega
    have hqle : n / d ≤ (N - 1) / d := Nat.div_le_div_right hnle
    have hphase :
        Int.fract ((d : ℝ) ^ (α - 1) * (n / d : ℕ) ^ α) < (d : ℝ)⁻¹ := by
      rw [← (hbridge (n / d) hq0)]
      simpa [Nat.mul_div_cancel' hdn]
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hq0, by simp [multipleIndexCutoff]; omega⟩, hphase⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_filter, Finset.mem_range, localDivisorEvent,
      powerFloorGCD, Nat.dvd_gcd_iff] at hn₁ hn₂
    have hd1 : d ∣ n₁ := hn₁.2.2.1
    have hd2 : d ∣ n₂ := hn₂.2.2.1
    calc
      n₁ = d * (n₁ / d) := (Nat.mul_div_cancel' hd1).symm
      _ = d * (n₂ / d) := by rw [heq]
      _ = n₂ := Nat.mul_div_cancel' hd2
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ico] at hm
    rcases hm with ⟨⟨hm0, hmcut⟩, hmphase⟩
    have hmle : m ≤ (N - 1) / d := by
      change m < (N - 1) / d + 1 at hmcut
      omega
    have hmul_le : m * d ≤ N - 1 :=
      (Nat.le_div_iff_mul_le hd).mp hmle
    have hN : 0 < N := by
      have hprod : 0 < m * d := Nat.mul_pos hm0 hd
      omega
    have hdmN : d * m < N := by
      rw [Nat.mul_comm]
      exact (Nat.le_sub_one_iff_lt hN).mp hmul_le
    have hfloor : d ∣ ⌊Real.rpow ((d * m : ℕ) : ℝ) α⌋₊ :=
      (hbridge m hm0).mpr hmphase
    refine ⟨d * m, ?_⟩
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range, localDivisorEvent,
        powerFloorGCD, Nat.dvd_gcd_iff]
      exact ⟨hdmN, Nat.mul_pos hd hm0, dvd_mul_right d m, hfloor⟩
    · simpa [Nat.mul_comm] using Nat.mul_div_left m hd

/-- A normalized monomial discrepancy tending to zero gives the fixed-`d`
local density `1/d²`.  The main term uses only the elementary asymptotic
for the number of positive multiples below `N`. -/
theorem powerFloorGCD_local_tendsto_of_bridge_and_error
    (α : ℝ) (d : ℕ) (hd : 0 < d)
    (hbridge : ∀ m : ℕ, 0 < m →
      (d ∣ ⌊Real.rpow ((d * m : ℕ) : ℝ) α⌋₊ ↔
        Int.fract ((d : ℝ) ^ (α - 1) * (m : ℝ) ^ α) < (d : ℝ)⁻¹))
    (herror : Tendsto (fun N : ℕ ↦
      monomialIntervalError α ((d : ℝ) ^ (α - 1)) (d : ℝ)⁻¹
        1 (multipleIndexCutoff N d) / N) atTop (nhds 0)) :
    Tendsto (prefixRatio (localDivisorEvent (powerFloorGCD α) d)) atTop
      (nhds ((d : ℝ)⁻¹ ^ 2)) := by
  have hmain : Tendsto (fun N : ℕ ↦
      (d : ℝ)⁻¹ * ((((N - 1) / d : ℕ) : ℝ) / N)) atTop
      (nhds ((d : ℝ)⁻¹ * (d : ℝ)⁻¹)) :=
    tendsto_const_nhds.mul (tendsto_positiveMultipleCount_div d hd)
  have hsum := herror.add hmain
  convert hsum using 1
  · funext N
    rw [prefixRatio,
      powerFloorGCD_local_prefixCount_eq_monomialIntervalCount_of_bridge
        α d N hd hbridge]
    unfold monomialIntervalError
    have hcut : multipleIndexCutoff N d - 1 = (N - 1) / d := by
      simp [multipleIndexCutoff]
    rw [hcut]
    ring_nf
  · ring_nf

/-- A prefix power-saving discrepancy estimate has negligible normalized
error along the multiplier cutoffs occurring in a fixed divisor count. -/
theorem monomial_error_div_tendsto_zero_of_prefixPowerSaving
    (α : ℝ) (hα : 1 < α) (d : ℕ) (hd : 0 < d)
    (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C)
    (hdisc : MonomialPrefixPowerSaving α (α - 1) η C) :
    Tendsto (fun N : ℕ ↦
      monomialIntervalError α ((d : ℝ) ^ (α - 1)) (d : ℝ)⁻¹
        1 (multipleIndexCutoff N d) / N) atTop (nhds 0) := by
  have hKtop := tendsto_multipleIndexCutoff_atTop d hd
  have hKreal : Tendsto
      (fun N : ℕ ↦ (multipleIndexCutoff N d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hKtop
  have hpow : Tendsto
      (fun N : ℕ ↦ (multipleIndexCutoff N d : ℝ) ^ (-η)) atTop
      (nhds 0) := (tendsto_rpow_neg_atTop hη).comp hKreal
  have hmajor : Tendsto
      (fun N : ℕ ↦ C * (multipleIndexCutoff N d : ℝ) ^ (-η)) atTop
      (nhds 0) := by simpa using hpow.const_mul C
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmajorE : ∀ᶠ N : ℕ in atTop,
      C * (multipleIndexCutoff N d : ℝ) ^ (-η) < ε :=
    hmajor.eventually (Iio_mem_nhds hε)
  have hKE : ∀ᶠ N : ℕ in atTop,
      max d 2 ≤ multipleIndexCutoff N d :=
    hKtop.eventually (Ici_mem_atTop (max d 2))
  apply Filter.eventually_atTop.1
  filter_upwards [hmajorE, hKE, eventually_gt_atTop (0 : ℕ)] with N hmaj hK hN
  let K := multipleIndexCutoff N d
  have hK2 : 2 ≤ K := (le_max_right d 2).trans hK
  have hdK : d ≤ K := (le_max_left d 2).trans hK
  have hK0 : 0 < (K : ℝ) := by positivity
  have hA : 0 ≤ α - 1 := sub_nonneg.mpr hα.le
  have ha1 : 1 ≤ (d : ℝ) ^ (α - 1) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num)
        (show (1 : ℝ) ≤ d by exact_mod_cast hd) hA
  have haK : (d : ℝ) ^ (α - 1) ≤ (K : ℝ) ^ (α - 1) :=
    Real.rpow_le_rpow (Nat.cast_nonneg d) (by exact_mod_cast hdK) hA
  have hb0 : 0 ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg d)
  have hb1 : (d : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast hd)
  have herr := hdisc K ((d : ℝ) ^ (α - 1)) (d : ℝ)⁻¹
    hK2 ha1 haK hb0 hb1
  have hKN : K ≤ N := by
    have hq : (N - 1) / d ≤ N - 1 := Nat.div_le_self _ _
    simp only [K, multipleIndexCutoff]
    omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpow_id : (K : ℝ) ^ (1 - η) = (K : ℝ) * (K : ℝ) ^ (-η) := by
    rw [show 1 - η = 1 + (-η) by ring, Real.rpow_add hK0,
      Real.rpow_one]
  have hnorm :
      |monomialIntervalError α ((d : ℝ) ^ (α - 1)) (d : ℝ)⁻¹ 1 K / N| ≤
        C * (K : ℝ) ^ (-η) := by
    rw [abs_div, abs_of_pos hNr]
    calc
      |monomialIntervalError α ((d : ℝ) ^ (α - 1)) (d : ℝ)⁻¹ 1 K| / (N : ℝ)
          ≤ (C * (K : ℝ) ^ (1 - η)) / N :=
        div_le_div_of_nonneg_right herr hNr.le
      _ = C * (K : ℝ) ^ (-η) * ((K : ℝ) / N) := by
        rw [hpow_id]
        ring
      _ ≤ C * (K : ℝ) ^ (-η) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact (div_le_one hNr).mpr (by exact_mod_cast hKN)
        · exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg K) (-η))
      _ = C * (K : ℝ) ^ (-η) := mul_one _
  rw [Real.dist_eq, sub_zero]
  exact hnorm.trans_lt hmaj

/-- Fixed local divisor density derived directly from a prefix monomial
power saving and the floor/fractional-part bridge. -/
theorem powerFloorGCD_local_tendsto_of_prefixPowerSaving
    (α : ℝ) (hα : 1 < α) (d : ℕ) (hd : 0 < d)
    (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C)
    (hdisc : MonomialPrefixPowerSaving α (α - 1) η C)
    (hbridge : ∀ m : ℕ, 0 < m →
      (d ∣ ⌊Real.rpow ((d * m : ℕ) : ℝ) α⌋₊ ↔
        Int.fract ((d : ℝ) ^ (α - 1) * (m : ℝ) ^ α) < (d : ℝ)⁻¹)) :
    Tendsto (prefixRatio (localDivisorEvent (powerFloorGCD α) d)) atTop
      (nhds ((d : ℝ)⁻¹ ^ 2)) :=
  powerFloorGCD_local_tendsto_of_bridge_and_error α d hd hbridge
    (monomial_error_div_tendsto_zero_of_prefixPowerSaving
      α hα d hd η C hη hC hdisc)

/-- Unconditional arithmetic specialization of
`powerFloorGCD_local_tendsto_of_prefixPowerSaving`: the bridge is supplied
by `dvd_natFloor_rpow_mul_iff_fract`. -/
theorem powerFloorGCD_local_tendsto_of_monomialPrefixPowerSaving
    (α : ℝ) (hα : 1 < α) (d : ℕ) (hd : 0 < d)
    (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C)
    (hdisc : MonomialPrefixPowerSaving α (α - 1) η C) :
    Tendsto (prefixRatio (localDivisorEvent (powerFloorGCD α) d)) atTop
      (nhds ((d : ℝ)⁻¹ ^ 2)) := by
  apply powerFloorGCD_local_tendsto_of_prefixPowerSaving
    α hα d hd η C hη hC hdisc
  intro m hm
  exact dvd_natFloor_rpow_mul_iff_fract d m hd α

/-- Quantitative local-divisor bound in the square-root range.  The
multiplier length is at most `2N/p`, while `p² ≤ N` ensures that the
coefficient `p^(α-1)` is covered by the prefix discrepancy hypothesis. -/
theorem powerFloorGCD_local_prefixRatio_le
    (α : ℝ) (hα : 1 < α) (p N : ℕ) (hp : p.Prime) (hN : 0 < N)
    (hpSq : p ^ 2 ≤ N) (η C : ℝ) (_hη0 : 0 < η) (hη1 : η < 1)
    (hC : 0 ≤ C) (hdisc : MonomialPrefixPowerSaving α (α - 1) η C) :
    prefixRatio (localDivisorEvent (powerFloorGCD α) p) N ≤
      ((p : ℝ) ^ 2)⁻¹ +
        C * ((2 : ℝ) * N / p) ^ (1 - η) / N := by
  let K := multipleIndexCutoff N p
  have hp0 : 0 < p := hp.pos
  have hpN : p ≤ N := by
    have hp1 : 1 ≤ p := hp.one_le
    nlinarith
  have hpmul : (p - 1) * p ≤ N - 1 := by
    have hpp : p * p ≤ N := by simpa [pow_two] using hpSq
    rw [Nat.sub_mul, one_mul]
    omega
  have hpK : p ≤ K := by
    have hdiv : p - 1 ≤ (N - 1) / p :=
      (Nat.le_div_iff_mul_le hp0).mpr hpmul
    simp only [K, multipleIndexCutoff]
    omega
  have hK2 : 2 ≤ K := hp.two_le.trans hpK
  have hKpN : K * p ≤ 2 * N := by
    have hqmul := Nat.div_mul_le_self (N - 1) p
    have hKmul : K * p ≤ (N - 1) + p := by
      change (((N - 1) / p + 1) * p) ≤ (N - 1) + p
      rw [Nat.add_mul, one_mul]
      exact Nat.add_le_add_right hqmul p
    exact hKmul.trans (by omega)
  have hKr : (K : ℝ) ≤ (2 : ℝ) * N / p := by
    apply (le_div_iff₀ (by exact_mod_cast hp0)).mpr
    exact_mod_cast hKpN
  have hK0r : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hA0 : 0 ≤ α - 1 := by linarith
  have ha1 : 1 ≤ (p : ℝ) ^ (α - 1) := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num)
      (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_le) hA0
  have haK : (p : ℝ) ^ (α - 1) ≤ (K : ℝ) ^ (α - 1) :=
    Real.rpow_le_rpow (Nat.cast_nonneg p) (by exact_mod_cast hpK) hA0
  have hb0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hb1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  have herr := hdisc K ((p : ℝ) ^ (α - 1)) (p : ℝ)⁻¹
    hK2 ha1 haK hb0 hb1
  have herrorUpper : monomialIntervalError α ((p : ℝ) ^ (α - 1))
      (p : ℝ)⁻¹ 1 K ≤ C * (K : ℝ) ^ (1 - η) :=
    (le_abs_self _).trans herr
  have hpowMono : (K : ℝ) ^ (1 - η) ≤
      ((2 : ℝ) * N / p) ^ (1 - η) := by
    exact Real.rpow_le_rpow hK0r hKr (sub_nonneg.mpr hη1.le)
  have hcountEq :=
    powerFloorGCD_local_prefixCount_eq_monomialIntervalCount_of_bridge
      α p N hp0 (fun m _ ↦ dvd_natFloor_rpow_mul_iff_fract p m hp0 α)
  have hmainNat : (K - 1) * p ≤ N := by
    have hqmul := Nat.div_mul_le_self (N - 1) p
    have hkm : K - 1 = (N - 1) / p := by simp [K, multipleIndexCutoff]
    rw [hkm]
    exact hqmul.trans (Nat.sub_le N 1)
  have hmain : (p : ℝ)⁻¹ * (K - 1 : ℕ) / N ≤ ((p : ℝ) ^ 2)⁻¹ := by
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hpr : 0 < (p : ℝ) := by exact_mod_cast hp0
    rw [inv_eq_one_div, inv_eq_one_div]
    field_simp
    exact_mod_cast (by simpa [Nat.mul_comm] using hmainNat)
  rw [prefixRatio, hcountEq]
  unfold monomialIntervalError at herrorUpper
  have hlen : K - 1 = (N - 1) / p := by simp [K, multipleIndexCutoff]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    (monomialIntervalCount α ((p : ℝ) ^ (α - 1)) (p : ℝ)⁻¹ 1 K : ℝ) / N
        ≤ ((p : ℝ)⁻¹ * (K - 1 : ℕ) + C * (K : ℝ) ^ (1 - η)) / N := by
          apply div_le_div_of_nonneg_right _ hNr.le
          norm_num at herrorUpper ⊢
          simpa [add_comm] using herrorUpper
    _ = ((p : ℝ)⁻¹ * (K - 1 : ℕ)) / N +
          C * (K : ℝ) ^ (1 - η) / N := by ring
    _ ≤ ((p : ℝ) ^ 2)⁻¹ + C * (K : ℝ) ^ (1 - η) / N := by
          gcongr
    _ ≤ ((p : ℝ) ^ 2)⁻¹ + C * ((2 : ℝ) * N / p) ^ (1 - η) / N := by
          gcongr

/-- The large-prime event for the power-floor gcd is bounded by the sum of
its local prime-divisor counts. -/
theorem powerFloorGCD_largePrime_prefixCount_le_sum_local
    (α : ℝ) (D N : ℕ) :
    prefixCount (largePrimeEvent (powerFloorGCD α) D) N ≤
      ∑ p ∈ primeWindow D N,
        prefixCount (localDivisorEvent (powerFloorGCD α) p) N := by
  classical
  unfold prefixCount
  rw [filter_largePrimeEvent_eq_filter_primeWindowEvent
    (powerFloorGCD α) (powerFloorGCD_dvd_index α) D N]
  exact prefixCount_primeWindowEvent_le_sum_local (powerFloorGCD α) D N N

/-- A rectangular box of swapped `(p,m)` variables.  It contains every
large-prime witness `n=p*m` after primality and the product condition have
been discarded, which is precisely the hyperbola switch used in the
superlinear tail. -/
noncomputable def swappedPrimeBox (α : ℝ) (Y U N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Ioc Y U).product
    (Finset.Ico 1 (multipleIndexCutoff N (Y + 1)))).filter fun z ↦
      Int.fract (monomialValue (α - 1) ((z.2 : ℝ) ^ α) z.1) <
        ((Y + 1 : ℕ) : ℝ)⁻¹

private noncomputable def selectedPrime
    (ξ : ℕ → ℕ) (D U n : ℕ) : ℕ := by
  classical
  exact if h : primeWindowEvent ξ D U n then Classical.choose h.2 else 0

private lemma selectedPrime_spec {ξ : ℕ → ℕ} {D U n : ℕ}
    (h : primeWindowEvent ξ D U n) :
    (selectedPrime ξ D U n).Prime ∧ D < selectedPrime ξ D U n ∧
      selectedPrime ξ D U n ≤ U ∧ selectedPrime ξ D U n ∣ ξ n := by
  classical
  unfold selectedPrime
  rw [dif_pos h]
  exact Classical.choose_spec h.2

/-- Hyperbola-switch injection.  Each integer with a common prime divisor
in `(Y,U]` is injected into its selected factorization `n=p*m`; the target
is a monomial discrepancy box in the prime variable. -/
theorem powerFloorGCD_primeWindow_prefixCount_le_swappedPrimeBox
    (α : ℝ) (Y U N : ℕ) :
    prefixCount (primeWindowEvent (powerFloorGCD α) Y U) N ≤
      (swappedPrimeBox α Y U N).card := by
  classical
  unfold prefixCount
  let P : ℕ → ℕ := fun n ↦ selectedPrime (powerFloorGCD α) Y U n
  let f : ℕ → ℕ × ℕ := fun n ↦ (P n, n / P n)
  apply Finset.card_le_card_of_injOn f
  · intro n hn
    change n ∈ (Finset.range N).filter
      (primeWindowEvent (powerFloorGCD α) Y U) at hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rcases hn with ⟨hnN, hnEvent⟩
    have hP := selectedPrime_spec hnEvent
    change (P n).Prime ∧ Y < P n ∧ P n ≤ U ∧
      P n ∣ powerFloorGCD α n at hP
    have hP0 : 0 < P n := hP.1.pos
    have hPdvdG : P n ∣ powerFloorGCD α n := hP.2.2.2
    have hPdvdN : P n ∣ n := hPdvdG.trans (powerFloorGCD_dvd_index α n)
    have hn0 : 0 < n := hnEvent.1
    have hPn : P n ≤ n := Nat.le_of_dvd hn0 hPdvdN
    have hm0 : 0 < n / P n := Nat.div_pos hPn hP0
    have hmul : P n * (n / P n) = n := Nat.mul_div_cancel' hPdvdN
    have hYleP : Y + 1 ≤ P n := by omega
    have hmulY : (n / P n) * (Y + 1) ≤ N - 1 := by
      have hprod : (Y + 1) * (n / P n) ≤ n := by
        calc
          (Y + 1) * (n / P n) ≤ P n * (n / P n) :=
            Nat.mul_le_mul_right (n / P n) hYleP
          _ = n := hmul
      have hnle : n ≤ N - 1 := by omega
      simpa [Nat.mul_comm] using hprod.trans hnle
    have hmle : n / P n ≤ (N - 1) / (Y + 1) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr hmulY
    have hmcut : n / P n < multipleIndexCutoff N (Y + 1) := by
      simp only [multipleIndexCutoff]
      omega
    have hPfloor : P n ∣ ⌊Real.rpow (n : ℝ) α⌋₊ := by
      exact (Nat.dvd_gcd_iff.mp hPdvdG).2
    have hPfloor' :
        P n ∣ ⌊Real.rpow (((P n) * (n / P n) : ℕ) : ℝ) α⌋₊ := by
      simpa only [hmul] using hPfloor
    have hphaseP := (dvd_natFloor_rpow_mul_iff_fract
      (P n) (n / P n) hP0 α).mp hPfloor'
    have hinv : ((P n : ℕ) : ℝ)⁻¹ ≤ ((Y + 1 : ℕ) : ℝ)⁻¹ := by
      exact inv_anti₀ (by positivity) (by exact_mod_cast hYleP)
    have hphase :
        Int.fract (monomialValue (α - 1) (((n / P n : ℕ) : ℝ) ^ α) (P n)) <
          ((Y + 1 : ℕ) : ℝ)⁻¹ := by
      have heq : monomialValue (α - 1) (((n / P n : ℕ) : ℝ) ^ α) (P n) =
          ((P n : ℕ) : ℝ) ^ (α - 1) * ((n / P n : ℕ) : ℝ) ^ α := by
        simp only [monomialValue]
        ring
      rw [heq]
      exact hphaseP.trans_le hinv
    change f n ∈ (↑(swappedPrimeBox α Y U N) : Set (ℕ × ℕ))
    simp only [Finset.mem_coe]
    change (P n, n / P n) ∈ swappedPrimeBox α Y U N
    unfold swappedPrimeBox
    rw [Finset.mem_filter]
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_Ioc.mpr ⟨hP.2.1, hP.2.2.1⟩
      · exact Finset.mem_Ico.mpr ⟨hm0, hmcut⟩
    · simpa using hphase
  · intro n₁ hn₁ n₂ hn₂ heq
    change n₁ ∈ (Finset.range N).filter
      (primeWindowEvent (powerFloorGCD α) Y U) at hn₁
    change n₂ ∈ (Finset.range N).filter
      (primeWindowEvent (powerFloorGCD α) Y U) at hn₂
    simp only [Finset.mem_filter, Finset.mem_range] at hn₁ hn₂
    have hP1 := selectedPrime_spec hn₁.2
    have hP2 := selectedPrime_spec hn₂.2
    have hdvd1 : P n₁ ∣ n₁ := hP1.2.2.2.trans
      (powerFloorGCD_dvd_index α n₁)
    have hdvd2 : P n₂ ∣ n₂ := hP2.2.2.2.trans
      (powerFloorGCD_dvd_index α n₂)
    have hpEq : P n₁ = P n₂ := congrArg Prod.fst heq
    have hmEq : n₁ / P n₁ = n₂ / P n₂ := congrArg Prod.snd heq
    have hmEq' : n₁ / P n₂ = n₂ / P n₂ := by simpa [hpEq] using hmEq
    calc
      n₁ = P n₁ * (n₁ / P n₁) := (Nat.mul_div_cancel' hdvd1).symm
      _ = P n₂ * (n₁ / P n₂) := by rw [hpEq]
      _ = P n₂ * (n₂ / P n₂) := by rw [hmEq']
      _ = n₂ := Nat.mul_div_cancel' hdvd2

/-- The swapped box is the sum of monomial fractional-part counts over the
short multiplier range.  This is the exact finite form to which interval
power discrepancy is applied. -/
theorem swappedPrimeBox_card_eq_sum_monomialIntervalCount
    (α : ℝ) (Y U N : ℕ) :
    (swappedPrimeBox α Y U N).card =
      ∑ m ∈ Finset.Ico 1 (multipleIndexCutoff N (Y + 1)),
        monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
          ((Y + 1 : ℕ) : ℝ)⁻¹ (Y + 1) (U + 1) := by
  classical
  unfold swappedPrimeBox
  calc
    (((Finset.Ioc Y U).product
        (Finset.Ico 1 (multipleIndexCutoff N (Y + 1)))).filter fun z ↦
      Int.fract (monomialValue (α - 1) ((z.2 : ℝ) ^ α) z.1) <
        ((Y + 1 : ℕ) : ℝ)⁻¹).card =
        ∑ z ∈ (Finset.Ioc Y U).product
            (Finset.Ico 1 (multipleIndexCutoff N (Y + 1))),
          (if Int.fract
              (monomialValue (α - 1) ((z.2 : ℝ) ^ α) z.1) <
                ((Y + 1 : ℕ) : ℝ)⁻¹ then 1 else 0 : ℕ) := by
      rw [Finset.sum_boole]
      norm_cast
    _ = ∑ p ∈ Finset.Ioc Y U,
          ∑ m ∈ Finset.Ico 1 (multipleIndexCutoff N (Y + 1)),
            (if Int.fract (monomialValue (α - 1) ((m : ℝ) ^ α) p) <
              ((Y + 1 : ℕ) : ℝ)⁻¹ then 1 else 0 : ℕ) := by
      simpa using (Finset.sum_product'
        (Finset.Ioc Y U) (Finset.Ico 1 (multipleIndexCutoff N (Y + 1)))
        (fun p m ↦ (if Int.fract
          (monomialValue (α - 1) ((m : ℝ) ^ α) p) <
            ((Y + 1 : ℕ) : ℝ)⁻¹ then 1 else 0 : ℕ)))
    _ = ∑ m ∈ Finset.Ico 1 (multipleIndexCutoff N (Y + 1)),
          ∑ p ∈ Finset.Ioc Y U,
            (if Int.fract (monomialValue (α - 1) ((m : ℝ) ^ α) p) <
              ((Y + 1 : ℕ) : ℝ)⁻¹ then 1 else 0 : ℕ) := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.Ico 1 (multipleIndexCutoff N (Y + 1)),
        monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
          ((Y + 1 : ℕ) : ℝ)⁻¹ (Y + 1) (U + 1) := by
      apply Finset.sum_congr rfl
      intro m hm
      unfold monomialIntervalCount
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hpY, hpU⟩, hphase⟩
        exact ⟨⟨by omega, by omega⟩, hphase⟩
      · rintro ⟨⟨hpY, hpU⟩, hphase⟩
        exact ⟨⟨by omega, by omega⟩, hphase⟩

/-- Fully expanded hyperbola-switch bound, ready for termwise interval
power discrepancy in the `p` variable. -/
theorem powerFloorGCD_primeWindow_prefixCount_le_swappedMonomialSum
    (α : ℝ) (Y U N : ℕ) :
    prefixCount (primeWindowEvent (powerFloorGCD α) Y U) N ≤
      ∑ m ∈ Finset.Ico 1 (multipleIndexCutoff N (Y + 1)),
        monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
          ((Y + 1 : ℕ) : ℝ)⁻¹ (Y + 1) (U + 1) := by
  exact (powerFloorGCD_primeWindow_prefixCount_le_swappedPrimeBox
    α Y U N).trans_eq (swappedPrimeBox_card_eq_sum_monomialIntervalCount
      α Y U N)

/-- Dropping a lower endpoint can only increase a monomial interval count. -/
lemma monomialIntervalCount_Ioc_le_prefix
    (γ a b : ℝ) (Y U : ℕ) :
    monomialIntervalCount γ a b (Y + 1) (U + 1) ≤
      monomialIntervalCount γ a b 1 (U + 1) := by
  classical
  unfold monomialIntervalCount
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
  exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩

/-- A prefix power saving bounds one shifted interval count by its prefix
main term plus the same error. -/
lemma monomialIntervalCount_Ioc_le_main_add_error_of_prefixPowerSaving
    (γ A η C a b : ℝ) (Y U : ℕ)
    (hdisc : MonomialPrefixPowerSaving γ A η C)
    (hU : 2 ≤ U + 1) (ha1 : 1 ≤ a) (haU : a ≤ (U + 1 : ℕ) ^ A)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (monomialIntervalCount γ a b (Y + 1) (U + 1) : ℝ) ≤
      b * U + C * (U + 1 : ℕ) ^ (1 - η) := by
  have hprefix := hdisc (U + 1) a b hU ha1 haU hb0 hb1
  have herrorUpper : monomialIntervalError γ a b 1 (U + 1) ≤
      C * (U + 1 : ℕ) ^ (1 - η) :=
    (le_abs_self _).trans hprefix
  have hcount : (monomialIntervalCount γ a b 1 (U + 1) : ℝ) ≤
      b * U + C * (U + 1 : ℕ) ^ (1 - η) := by
    unfold monomialIntervalError at herrorUpper
    norm_num at herrorUpper ⊢
    simpa [add_comm] using herrorUpper
  have hmono :
      (monomialIntervalCount γ a b (Y + 1) (U + 1) : ℝ) ≤
        monomialIntervalCount γ a b 1 (U + 1) := by
    exact_mod_cast monomialIntervalCount_Ioc_le_prefix γ a b Y U
  exact hmono.trans hcount

/-- Sum a family of pointwise local bounds over a small-prime window.  The
main reciprocal-square mass is collapsed to `1/D`. -/
theorem sum_local_prefixRatio_le_inv_add_remainder
    (ξ : ℕ → ℕ) (D U N : ℕ) (hD : D ≠ 0) (R : ℕ → ℝ)
    (hlocal : ∀ p ∈ primeWindow D U,
      prefixRatio (localDivisorEvent ξ p) N ≤ ((p : ℝ) ^ 2)⁻¹ + R p) :
    (∑ p ∈ primeWindow D U,
      prefixRatio (localDivisorEvent ξ p) N) ≤
      (D : ℝ)⁻¹ + ∑ p ∈ primeWindow D U, R p := by
  calc
    (∑ p ∈ primeWindow D U,
        prefixRatio (localDivisorEvent ξ p) N)
        ≤ ∑ p ∈ primeWindow D U, (((p : ℝ) ^ 2)⁻¹ + R p) := by
      exact Finset.sum_le_sum fun p hp ↦ hlocal p hp
    _ = (∑ p ∈ primeWindow D U, ((p : ℝ) ^ 2)⁻¹) +
          ∑ p ∈ primeWindow D U, R p := by
      rw [Finset.sum_add_distrib]
    _ ≤ (D : ℝ)⁻¹ + ∑ p ∈ primeWindow D U, R p := by
      gcongr
      exact sum_primeWindow_inv_sq_le_inv D U hD

/-- Integral-test estimate for the power sum that occurs after adding the
uniform local discrepancies. -/
lemma sum_range_succ_rpow_eta_sub_one_le
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (Y : ℕ) (hY : 1 ≤ Y) :
    (∑ j ∈ Finset.range Y, ((j + 1 : ℕ) : ℝ) ^ (η - 1)) ≤
      1 + ((Y : ℝ) ^ η - 1) / η := by
  let f : ℝ → ℝ := fun x ↦ x ^ (η - 1)
  have hf : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) (Y : ℝ)) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      (by
        intro x hx
        norm_num at hx ⊢
        exact zero_lt_one.trans_le hx.1)
  have htail := AntitoneOn.sum_le_integral_Ico (f := f) hY hf
  have hsum :
      (∑ j ∈ Finset.range Y, ((j + 1 : ℕ) : ℝ) ^ (η - 1)) =
        1 + ∑ j ∈ Finset.Ico 1 Y, ((j + 1 : ℕ) : ℝ) ^ (η - 1) := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Y ≠ 0)
    rw [Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range]
    rw [add_comm]
    norm_num
    congr 1
    funext j
    congr 1
    ring
  rw [hsum]
  gcongr
  calc
    (∑ j ∈ Finset.Ico 1 Y, ((j + 1 : ℕ) : ℝ) ^ (η - 1))
        ≤ ∫ x in (1 : ℝ)..(Y : ℝ), x ^ (η - 1) := by
          simpa [f] using htail
    _ = ((Y : ℝ) ^ η - 1) / η := by
      rw [integral_rpow]
      · norm_num
      · left
        linarith

/-- The same power-sum estimate over an arbitrary subset of `[1,Y]`. -/
lemma sum_subset_Icc_rpow_eta_sub_one_le
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (s : Finset ℕ) (Y : ℕ)
    (hs : s ⊆ Finset.Icc 1 Y) (hY : 1 ≤ Y) :
    (∑ p ∈ s, (p : ℝ) ^ (η - 1)) ≤
      1 + ((Y : ℝ) ^ η - 1) / η := by
  calc
    (∑ p ∈ s, (p : ℝ) ^ (η - 1))
        ≤ ∑ p ∈ Finset.Icc 1 Y, (p : ℝ) ^ (η - 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg hs
            (fun _ _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ∑ j ∈ Finset.range Y, ((j + 1 : ℕ) : ℝ) ^ (η - 1) := by
      symm
      apply Finset.sum_bij (fun j _ ↦ j + 1)
      · intro j hj
        exact Finset.mem_Icc.mpr
          ⟨by omega, by simpa using Finset.mem_range.mp hj⟩
      · intro i hi j hj hij
        omega
      · intro p hp
        have hpI := Finset.mem_Icc.mp hp
        exact ⟨p - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro j hj
        rfl
    _ ≤ 1 + ((Y : ℝ) ^ η - 1) / η :=
      sum_range_succ_rpow_eta_sub_one_le η hη0 hη1 Y hY

/-- The total normalized discrepancy error for primes up to `sqrt N` has a
uniform `N^(-η/2)` majorant. -/
lemma sum_sqrtWindow_localRemainder_le
    (D N : ℕ) (hN : 0 < N) (η C : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hC : 0 ≤ C) :
    (∑ p ∈ primeWindow D N.sqrt,
        C * ((2 : ℝ) * N / p) ^ (1 - η) / N) ≤
      C * (2 : ℝ) ^ (1 - η) * (1 + η⁻¹) *
        (N : ℝ) ^ (-(η / 2)) := by
  have hY : 1 ≤ N.sqrt := by
    exact Nat.sqrt_pos.2 hN
  have hs : primeWindow D N.sqrt ⊆ Finset.Icc 1 N.sqrt := by
    intro p hp
    have hp' := mem_primeWindow.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.1.one_le, hp'.2.2⟩
  have hsum := sum_subset_Icc_rpow_eta_sub_one_le
    η hη0 hη1 (primeWindow D N.sqrt) N.sqrt hs hY
  have hY0r : (0 : ℝ) ≤ N.sqrt := Nat.cast_nonneg _
  have hYpow1 : (1 : ℝ) ≤ (N.sqrt : ℝ) ^ η := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num)
      (show (1 : ℝ) ≤ N.sqrt by exact_mod_cast hY) hη0.le
  have hsum' : (∑ p ∈ primeWindow D N.sqrt, (p : ℝ) ^ (η - 1)) ≤
      (1 + η⁻¹) * (N.sqrt : ℝ) ^ η := by
    calc
      (∑ p ∈ primeWindow D N.sqrt, (p : ℝ) ^ (η - 1))
          ≤ 1 + ((N.sqrt : ℝ) ^ η - 1) / η := hsum
      _ ≤ (1 + η⁻¹) * (N.sqrt : ℝ) ^ η := by
        rw [div_eq_mul_inv]
        have hηinv : 0 ≤ η⁻¹ := inv_nonneg.mpr hη0.le
        nlinarith
  have hterm : ∀ p ∈ primeWindow D N.sqrt,
      C * ((2 : ℝ) * N / p) ^ (1 - η) / N =
        (C * ((2 : ℝ) * N) ^ (1 - η) / N) *
          (p : ℝ) ^ (η - 1) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (mem_primeWindow.mp hp).1.pos
    have hpPow : ((p : ℝ) ^ (1 - η))⁻¹ = (p : ℝ) ^ (η - 1) := by
      rw [← Real.rpow_neg hp0.le]
      congr 1
      ring
    rw [Real.div_rpow (by positivity) hp0.le]
    simp only [div_eq_mul_inv, hpPow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hpref : 0 ≤ C * ((2 : ℝ) * N) ^ (1 - η) / N := by positivity
  calc
    (C * ((2 : ℝ) * N) ^ (1 - η) / N) *
          ∑ p ∈ primeWindow D N.sqrt, (p : ℝ) ^ (η - 1)
        ≤ (C * ((2 : ℝ) * N) ^ (1 - η) / N) *
            ((1 + η⁻¹) * (N.sqrt : ℝ) ^ η) :=
          mul_le_mul_of_nonneg_left hsum' hpref
    _ ≤ (C * ((2 : ℝ) * N) ^ (1 - η) / N) *
            ((1 + η⁻¹) * (N : ℝ) ^ (η / 2)) := by
      gcongr
      have hsqrt : (N.sqrt : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        exact_mod_cast (show N.sqrt ^ 2 ≤ N by
          simpa [pow_two] using Nat.sqrt_le N)
      calc
        (N.sqrt : ℝ) ^ η ≤ Real.sqrt (N : ℝ) ^ η :=
          Real.rpow_le_rpow hY0r hsqrt hη0.le
        _ = (N : ℝ) ^ (η / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          congr 1
          ring
    _ = C * (2 : ℝ) ^ (1 - η) * (1 + η⁻¹) *
          (N : ℝ) ^ (-(η / 2)) := by
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hNr.le]
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        C * (2 ^ (1 - η) * (N : ℝ) ^ (1 - η)) * (N : ℝ) ^ (-(1 : ℝ)) *
              ((1 + η⁻¹) * (N : ℝ) ^ (η / 2)) =
            C * 2 ^ (1 - η) * (1 + η⁻¹) *
              (((N : ℝ) ^ (1 - η) * (N : ℝ) ^ (η / 2)) *
                (N : ℝ) ^ (-(1 : ℝ))) := by ring
        _ = C * 2 ^ (1 - η) * (1 + η⁻¹) *
              (N : ℝ) ^ (-(η / 2)) := by
          rw [← Real.rpow_add hNr, ← Real.rpow_add hNr]
          congr 2
          ring

/-- Small-prime square-root-range estimate obtained by summing the prefix
power saving. -/
theorem powerFloorGCD_smallPrime_sum_le
    (α : ℝ) (hα : 1 < α) (D N : ℕ) (hD : D ≠ 0) (hN : 0 < N)
    (η C : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hC : 0 ≤ C)
    (hdisc : MonomialPrefixPowerSaving α (α - 1) η C) :
    (∑ p ∈ primeWindow D N.sqrt,
        prefixRatio (localDivisorEvent (powerFloorGCD α) p) N) ≤
      (D : ℝ)⁻¹ +
        C * (2 : ℝ) ^ (1 - η) * (1 + η⁻¹) *
          (N : ℝ) ^ (-(η / 2)) := by
  let R : ℕ → ℝ := fun p ↦ C * ((2 : ℝ) * N / p) ^ (1 - η) / N
  have hlocal : ∀ p ∈ primeWindow D N.sqrt,
      prefixRatio (localDivisorEvent (powerFloorGCD α) p) N ≤
        ((p : ℝ) ^ 2)⁻¹ + R p := by
    intro p hp
    have hp' := mem_primeWindow.mp hp
    have hpSq : p ^ 2 ≤ N := calc
      p ^ 2 ≤ N.sqrt ^ 2 := Nat.pow_le_pow_left hp'.2.2 2
      _ ≤ N := by simpa [pow_two] using Nat.sqrt_le N
    exact powerFloorGCD_local_prefixRatio_le α hα p N hp'.1 hN hpSq
      η C hη0 hη1 hC hdisc
  calc
    (∑ p ∈ primeWindow D N.sqrt,
        prefixRatio (localDivisorEvent (powerFloorGCD α) p) N)
        ≤ (D : ℝ)⁻¹ + ∑ p ∈ primeWindow D N.sqrt, R p :=
          sum_local_prefixRatio_le_inv_add_remainder
            (powerFloorGCD α) D N.sqrt N hD R hlocal
    _ ≤ (D : ℝ)⁻¹ +
          C * (2 : ℝ) ^ (1 - η) * (1 + η⁻¹) *
            (N : ℝ) ^ (-(η / 2)) := by
      gcongr
      exact sum_sqrtWindow_localRemainder_le D N hN η C hη0 hη1 hC

/-- The small-prime hypothesis required by the abstract hyperbola assembly,
with the canonical cutoff `sqrt N`. -/
theorem powerFloorGCD_smallPrime_hyperbola_of_prefixPowerSaving
    (α : ℝ) (hα : 1 < α) (η C : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hC : 0 ≤ C) (hdisc : MonomialPrefixPowerSaving α (α - 1) η C) :
    ∀ ε > 0, ∃ D₀, ∀ D ≥ D₀,
      ∀ᶠ N : ℕ in atTop,
        (∑ p ∈ primeWindow D N.sqrt,
          prefixRatio (localDivisorEvent (powerFloorGCD α) p) N) < ε := by
  intro ε hε
  have hinv : Tendsto (fun D : ℕ ↦ (D : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hinvE : ∀ᶠ D : ℕ in atTop, (D : ℝ)⁻¹ < ε / 2 :=
    hinv.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨D₀, hD₀⟩ := Filter.eventually_atTop.1 hinvE
  refine ⟨max 1 D₀, fun D hD ↦ ?_⟩
  have hD1 : 1 ≤ D := (le_max_left 1 D₀).trans hD
  have hDinv : (D : ℝ)⁻¹ < ε / 2 :=
    hD₀ D ((le_max_right 1 D₀).trans hD)
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(η / 2))) atTop
      (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < η / 2)).comp
      tendsto_natCast_atTop_atTop
  have hmajor : Tendsto (fun N : ℕ ↦
      C * (2 : ℝ) ^ (1 - η) * (1 + η⁻¹) *
        (N : ℝ) ^ (-(η / 2))) atTop (nhds 0) := by
    simpa using hpow.const_mul
      (C * (2 : ℝ) ^ (1 - η) * (1 + η⁻¹))
  have hmajorE : ∀ᶠ N : ℕ in atTop,
      C * (2 : ℝ) ^ (1 - η) * (1 + η⁻¹) *
        (N : ℝ) ^ (-(η / 2)) < ε / 2 :=
    hmajor.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hmajorE, eventually_gt_atTop (0 : ℕ)] with N hmaj hN
  have hbound := powerFloorGCD_smallPrime_sum_le α hα D N
    (Nat.ne_of_gt hD1) hN η C hη0 hη1 hC hdisc
  exact hbound.trans_lt (by linarith)

/-- One dyadic large-prime block after the hyperbola switch.  If
`N ≤ (P+1)²`, interval power discrepancy for exponent `α-1` gives the
normalized bound `1/(P+1) + C(P+1)^(-η)`. -/
theorem powerFloorGCD_dyadicBlock_prefixRatio_le
    (α : ℝ) (hα : 1 < α) (P N : ℕ) (hP : 1 ≤ P) (hN : 0 < N)
    (hNP : N ≤ (P + 1) ^ 2) (η C : ℝ) (hC : 0 ≤ C)
    (hdisc : MonomialIntervalPowerSaving (α - 1) (α + 1) η C) :
    prefixRatio (primeWindowEvent (powerFloorGCD α) P (2 * P)) N ≤
      ((P + 1 : ℕ) : ℝ)⁻¹ + C * ((P + 1 : ℕ) : ℝ) ^ (-η) := by
  let K := multipleIndexCutoff N (P + 1)
  let B : ℝ := ((P + 1 : ℕ) : ℝ)⁻¹ * P +
    C * ((P + 1 : ℕ) : ℝ) ^ (1 - η)
  have hcountNat := powerFloorGCD_primeWindow_prefixCount_le_swappedMonomialSum
    α P (2 * P) N
  have hterm : ∀ m ∈ Finset.Ico 1 K,
      (monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
        ((P + 1 : ℕ) : ℝ)⁻¹ (P + 1) (2 * P + 1) : ℝ) ≤ B := by
    intro m hm
    have hmI := Finset.mem_Ico.mp hm
    have hmleq : m ≤ (N - 1) / (P + 1) := by
      change 1 ≤ m ∧ m < (N - 1) / (P + 1) + 1 at hmI
      omega
    have hqleP : (N - 1) / (P + 1) ≤ P + 1 := by
      have hqmul := Nat.div_mul_le_self (N - 1) (P + 1)
      have hcalc : (N - 1) / (P + 1) * (P + 1) ≤
          (P + 1) * (P + 1) := calc
        (N - 1) / (P + 1) * (P + 1) ≤ N - 1 := hqmul
        _ ≤ N := Nat.sub_le N 1
        _ ≤ (P + 1) ^ 2 := hNP
        _ = (P + 1) * (P + 1) := by ring
      exact Nat.le_of_mul_le_mul_right hcalc (by omega)
    have hmP : m ≤ P + 1 := hmleq.trans hqleP
    have hm0r : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hmI.1
    have hα0 : 0 ≤ α := by linarith
    have ha1 : 1 ≤ (m : ℝ) ^ α := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num) hm1r hα0
    have hpowBase : (m : ℝ) ^ α ≤ ((P + 1 : ℕ) : ℝ) ^ α :=
      Real.rpow_le_rpow hm0r (by exact_mod_cast hmP) hα0
    have hpowExp : ((P + 1 : ℕ) : ℝ) ^ α ≤
        ((P + 1 : ℕ) : ℝ) ^ (α + 1) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ ((P + 1 : ℕ) : ℝ) by
          exact_mod_cast (show 1 ≤ P + 1 by omega)) (by linarith)
    have hb0 : 0 ≤ ((P + 1 : ℕ) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    have hb1 : ((P + 1 : ℕ) : ℝ)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀
        (show (1 : ℝ) ≤ ((P + 1 : ℕ) : ℝ) by
          exact_mod_cast (show 1 ≤ P + 1 by omega))
    have herr := hdisc (P + 1) (P + 1) (2 * P + 1)
      ((m : ℝ) ^ α) ((P + 1 : ℕ) : ℝ)⁻¹
      (by omega) (le_rfl) (by omega) (by omega) ha1
      (hpowBase.trans hpowExp) hb0 hb1
    have hupper : monomialIntervalError (α - 1) ((m : ℝ) ^ α)
        ((P + 1 : ℕ) : ℝ)⁻¹ (P + 1) (2 * P + 1) ≤
        C * ((P + 1 : ℕ) : ℝ) ^ (1 - η) :=
      (le_abs_self _).trans herr
    unfold monomialIntervalError at hupper
    have hlen : 2 * P + 1 - (P + 1) = P := by omega
    rw [hlen] at hupper
    change (monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
        ((P + 1 : ℕ) : ℝ)⁻¹ (P + 1) (2 * P + 1) : ℝ) ≤ B
    dsimp only [B]
    norm_num at hupper ⊢
    simpa [add_comm] using hupper
  have hsumReal :
      (∑ m ∈ Finset.Ico 1 K,
        monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
          ((P + 1 : ℕ) : ℝ)⁻¹ (P + 1) (2 * P + 1) : ℝ) ≤
        ((Finset.Ico 1 K).card : ℝ) * B := by
    calc
      (∑ m ∈ Finset.Ico 1 K,
          monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
            ((P + 1 : ℕ) : ℝ)⁻¹ (P + 1) (2 * P + 1) : ℝ)
          = ∑ m ∈ Finset.Ico 1 K,
              (monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
                ((P + 1 : ℕ) : ℝ)⁻¹ (P + 1) (2 * P + 1) : ℝ) := by norm_num
      _ ≤ ∑ _m ∈ Finset.Ico 1 K, B := Finset.sum_le_sum hterm
      _ = ((Finset.Ico 1 K).card : ℝ) * B := by simp
  have hcountReal :
      (prefixCount (primeWindowEvent (powerFloorGCD α) P (2 * P)) N : ℝ) ≤
        ((Finset.Ico 1 K).card : ℝ) * B := by
    have hcast : (prefixCount
        (primeWindowEvent (powerFloorGCD α) P (2 * P)) N : ℝ) ≤
        (∑ m ∈ Finset.Ico 1 K,
          monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
            ((P + 1 : ℕ) : ℝ)⁻¹ (P + 1) (2 * P + 1) : ℕ) := by
      exact_mod_cast hcountNat
    push_cast at hcast
    have hsumReal' :
        (∑ m ∈ Finset.Ico 1 K,
          (monomialIntervalCount (α - 1) ((m : ℝ) ^ α)
            ((P : ℝ) + 1)⁻¹ (P + 1) (2 * P + 1) : ℝ)) ≤
          ((Finset.Ico 1 K).card : ℝ) * B := by
      simpa only [Nat.cast_add, Nat.cast_one] using hsumReal
    exact hcast.trans hsumReal'
  have hcard : (Finset.Ico 1 K).card = (N - 1) / (P + 1) := by
    simp [K, multipleIndexCutoff]
  have hcardRatio : ((Finset.Ico 1 K).card : ℝ) / N ≤
      ((P + 1 : ℕ) : ℝ)⁻¹ := by
    rw [hcard]
    have hmul := Nat.div_mul_le_self (N - 1) (P + 1)
    have hmulN : ((N - 1) / (P + 1)) * (P + 1) ≤ N :=
      hmul.trans (Nat.sub_le N 1)
    apply (div_le_iff₀ (by exact_mod_cast hN)).mpr
    rw [mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀
      (show (0 : ℝ) < (P + 1 : ℕ) by positivity)).mpr
        (by exact_mod_cast hmulN)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hBbound : B ≤ 1 + C * ((P + 1 : ℕ) : ℝ) ^ (1 - η) := by
    dsimp only [B]
    gcongr
    rw [inv_mul_eq_div]
    exact (div_le_one (by positivity)).mpr
      (by exact_mod_cast (show P ≤ P + 1 by omega))
  rw [prefixRatio]
  calc
    (prefixCount (primeWindowEvent (powerFloorGCD α) P (2 * P)) N : ℝ) / N
        ≤ (((Finset.Ico 1 K).card : ℝ) * B) / N :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = (((Finset.Ico 1 K).card : ℝ) / N) * B := by ring
    _ ≤ ((P + 1 : ℕ) : ℝ)⁻¹ * B :=
      mul_le_mul_of_nonneg_right hcardRatio hB0
    _ ≤ ((P + 1 : ℕ) : ℝ)⁻¹ *
        (1 + C * ((P + 1 : ℕ) : ℝ) ^ (1 - η)) := by
      gcongr
    _ = ((P + 1 : ℕ) : ℝ)⁻¹ +
        C * ((P + 1 : ℕ) : ℝ) ^ (-η) := by
      have hbase : 0 < ((P + 1 : ℕ) : ℝ) := by positivity
      rw [show 1 - η = 1 + (-η) by ring, Real.rpow_add hbase,
        Real.rpow_one]
      field_simp

/-- Left endpoint of the dyadic block containing `p`, scaled so that every
block begins at or above the moving cutoff `Y`. -/
def scaledDyadicBase (Y p : ℕ) : ℕ :=
  Y * 2 ^ Nat.log 2 ((p - 1) / Y)

/-- Scaled dyadic blocks occupied by a finite set. -/
def scaledDyadicKeys (Y : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.image (scaledDyadicBase Y)

/-- A point strictly above a positive cutoff lies in its scaled dyadic
block. -/
lemma mem_Ioc_scaledDyadicBase_two_mul
    {Y p : ℕ} (hY : 0 < Y) (hpY : Y < p) :
    p ∈ Finset.Ioc (scaledDyadicBase Y p) (2 * scaledDyadicBase Y p) := by
  let q := (p - 1) / Y
  have hYle : Y ≤ p - 1 := by omega
  have hq0 : 0 < q := Nat.div_pos hYle hY
  have hbase_le : 2 ^ Nat.log 2 q ≤ q :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hq0)
  have hq_lt : q < 2 ^ (Nat.log 2 q).succ :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two q
  have hq_succ : q + 1 ≤ 2 * 2 ^ Nat.log 2 q := by
    rw [pow_succ] at hq_lt
    omega
  have hYq : Y * q ≤ p - 1 := by
    simpa [q, Nat.mul_comm] using Nat.div_mul_le_self (p - 1) Y
  have hp_lt : p - 1 < (q + 1) * Y := by
    exact (Nat.div_lt_iff_lt_mul hY).mp (Nat.lt_succ_self q)
  rw [Finset.mem_Ioc]
  constructor
  · dsimp only [scaledDyadicBase]
    change Y * 2 ^ Nat.log 2 q < p
    have : Y * 2 ^ Nat.log 2 q ≤ p - 1 :=
      (Nat.mul_le_mul_left Y hbase_le).trans hYq
    omega
  · dsimp only [scaledDyadicBase]
    change p ≤ 2 * (Y * 2 ^ Nat.log 2 q)
    have hp_le : p ≤ (q + 1) * Y := by omega
    calc
      p ≤ (q + 1) * Y := hp_le
      _ ≤ (2 * 2 ^ Nat.log 2 q) * Y := Nat.mul_le_mul_right Y hq_succ
      _ = 2 * (Y * 2 ^ Nat.log 2 q) := by ring

/-- A set below `U` occupies at most `1+log₂(U-1)` scaled dyadic blocks. -/
lemma card_scaledDyadicKeys_le_log
    (Y : ℕ) {s : Finset ℕ} {U : ℕ} (hU : ∀ p ∈ s, p ≤ U) :
    (scaledDyadicKeys Y s).card ≤ Nat.log 2 (U - 1) + 1 := by
  classical
  let exponents : Finset ℕ :=
    s.image (fun p ↦ Nat.log 2 ((p - 1) / Y))
  have hkeys : scaledDyadicKeys Y s =
      exponents.image (fun j ↦ Y * 2 ^ j) := by
    ext P
    simp only [scaledDyadicKeys, scaledDyadicBase, exponents, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Nat.log 2 ((p - 1) / Y), ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨j, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  have hexponents : exponents ⊆ Finset.range (Nat.log 2 (U - 1) + 1) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    rw [Finset.mem_range]
    have hsub : p - 1 ≤ U - 1 := Nat.sub_le_sub_right (hU p hp) 1
    have hdiv : (p - 1) / Y ≤ U - 1 :=
      (Nat.div_le_self _ _).trans hsub
    exact Nat.lt_succ_of_le (Nat.log_mono_right hdiv)
  calc
    (scaledDyadicKeys Y s).card =
        (exponents.image (fun j ↦ Y * 2 ^ j)).card := by rw [hkeys]
    _ ≤ exponents.card := Finset.card_image_le
    _ ≤ (Finset.range (Nat.log 2 (U - 1) + 1)).card :=
      Finset.card_le_card hexponents
    _ = Nat.log 2 (U - 1) + 1 := Finset.card_range _

/-- Union bound after the scaled dyadic decomposition of a prime window. -/
theorem prefixRatio_primeWindowEvent_le_sum_scaledDyadic
    (ξ : ℕ → ℕ) (Y U N : ℕ) (hY : 0 < Y) :
    prefixRatio (primeWindowEvent ξ Y U) N ≤
      ∑ P ∈ scaledDyadicKeys Y (primeWindow Y U),
        prefixRatio (primeWindowEvent ξ P (2 * P)) N := by
  classical
  unfold prefixRatio prefixCount
  let keys := scaledDyadicKeys Y (primeWindow Y U)
  let A := (Finset.range N).filter (primeWindowEvent ξ Y U)
  let B : ℕ → Finset ℕ := fun P ↦
    (Finset.range N).filter (primeWindowEvent ξ P (2 * P))
  have hsub : A ⊆ keys.biUnion B := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    rcases hn'.2 with ⟨hn0, p, hp, hpY, hpU, hpdvd⟩
    have hpwin : p ∈ primeWindow Y U :=
      mem_primeWindow.mpr ⟨hp, hpY, hpU⟩
    let P := scaledDyadicBase Y p
    have hPkey : P ∈ keys := by
      exact Finset.mem_image.mpr ⟨p, hpwin, rfl⟩
    have hpblock := Finset.mem_Ioc.mp
      (mem_Ioc_scaledDyadicBase_two_mul hY hpY)
    refine Finset.mem_biUnion.mpr ⟨P, hPkey, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨hn'.1, ⟨hn0, p, hp, hpblock.1, hpblock.2, hpdvd⟩⟩
  have hcard : A.card ≤ ∑ P ∈ keys, (B P).card := calc
    A.card ≤ (keys.biUnion B).card := Finset.card_le_card hsub
    _ ≤ ∑ P ∈ keys, (B P).card := Finset.card_biUnion_le
  have hreal : (A.card : ℝ) ≤ ∑ P ∈ keys, ((B P).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (A.card : ℝ) / N ≤ (∑ P ∈ keys, ((B P).card : ℝ)) / N :=
      div_le_div_of_nonneg_right hreal (Nat.cast_nonneg N)
    _ = ∑ P ∈ keys, ((B P).card : ℝ) / N := by rw [Finset.sum_div]

/-- Quantitative high-prime estimate after scaled dyadic decomposition. -/
theorem powerFloorGCD_largePrime_sqrt_prefixRatio_le
    (α : ℝ) (hα : 1 < α) (N : ℕ) (hN : 0 < N)
    (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C)
    (hdisc : MonomialIntervalPowerSaving (α - 1) (α + 1) η C) :
    prefixRatio (primeWindowEvent (powerFloorGCD α) N.sqrt N) N ≤
      (Nat.log 2 (N - 1) + 1 : ℕ) *
        (((N.sqrt + 1 : ℕ) : ℝ)⁻¹ +
          C * ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)) := by
  let keys := scaledDyadicKeys N.sqrt (primeWindow N.sqrt N)
  have hY : 0 < N.sqrt := Nat.sqrt_pos.2 hN
  have hcover := prefixRatio_primeWindowEvent_le_sum_scaledDyadic
    (powerFloorGCD α) N.sqrt N N hY
  have hkey : ∀ P ∈ keys, N.sqrt ≤ P := by
    intro P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    dsimp only [scaledDyadicBase]
    simpa using Nat.le_mul_of_pos_right N.sqrt (by positivity : 0 < 2 ^ Nat.log 2 ((p - 1) / N.sqrt))
  have hterm : ∀ P ∈ keys,
      prefixRatio (primeWindowEvent (powerFloorGCD α) P (2 * P)) N ≤
        (((N.sqrt + 1 : ℕ) : ℝ)⁻¹ +
          C * ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)) := by
    intro P hPmem
    have hYP := hkey P hPmem
    have hP1 : 1 ≤ P := hY.trans_le hYP
    have hNP : N ≤ (P + 1) ^ 2 := by
      have hsqrt := Nat.lt_succ_sqrt' N
      have hs : N.sqrt + 1 ≤ P + 1 := Nat.add_le_add_right hYP 1
      exact hsqrt.le.trans (Nat.pow_le_pow_left hs 2)
    have hblock := powerFloorGCD_dyadicBlock_prefixRatio_le
      α hα P N hP1 hN hNP η C hC hdisc
    have hbase : ((N.sqrt + 1 : ℕ) : ℝ) ≤ ((P + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hYP 1
    have hinv : ((P + 1 : ℕ) : ℝ)⁻¹ ≤ ((N.sqrt + 1 : ℕ) : ℝ)⁻¹ :=
      inv_anti₀ (by positivity) hbase
    have hrpow : ((P + 1 : ℕ) : ℝ) ^ (-η) ≤
        ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η) := by
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
    exact hblock.trans (add_le_add hinv (mul_le_mul_of_nonneg_left hrpow hC))
  have hsum :
      (∑ P ∈ keys,
        prefixRatio (primeWindowEvent (powerFloorGCD α) P (2 * P)) N) ≤
        (keys.card : ℝ) *
          (((N.sqrt + 1 : ℕ) : ℝ)⁻¹ +
            C * ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)) := by
    calc
      (∑ P ∈ keys,
          prefixRatio (primeWindowEvent (powerFloorGCD α) P (2 * P)) N)
          ≤ ∑ _P ∈ keys,
              (((N.sqrt + 1 : ℕ) : ℝ)⁻¹ +
                C * ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)) :=
            Finset.sum_le_sum hterm
      _ = (keys.card : ℝ) *
            (((N.sqrt + 1 : ℕ) : ℝ)⁻¹ +
              C * ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hcardNat : keys.card ≤ Nat.log 2 (N - 1) + 1 := by
    apply card_scaledDyadicKeys_le_log N.sqrt
    intro p hp
    exact (mem_primeWindow.mp hp).2.2
  have hcard : (keys.card : ℝ) ≤ (Nat.log 2 (N - 1) + 1 : ℕ) := by
    exact_mod_cast hcardNat
  have hfactor0 : 0 ≤ (((N.sqrt + 1 : ℕ) : ℝ)⁻¹ +
      C * ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)) := by positivity
  exact hcover.trans (hsum.trans (mul_le_mul_of_nonneg_right hcard hfactor0))

/-- A logarithmic number of square-root-scale dyadic blocks times any fixed
negative power of their left endpoint tends to zero. -/
lemma tendsto_natLog_mul_sqrtSucc_rpow_neg
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ ↦
      (Nat.log 2 (N - 1) + 1 : ℕ) *
        (((N.sqrt + 1 : ℕ) : ℝ) ^ (-η))) atTop (nhds 0) := by
  let δ : ℝ := η / 4
  let K : ℝ := (δ * Real.log 2)⁻¹ + 1
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : Tendsto (fun N : ℕ ↦ K * (N : ℝ) ^ (-δ)) atTop
      (nhds 0) := by
    have := (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
    simpa using this.const_mul K
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦ by positivity
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hNm1 : 0 < N - 1 := by omega
    have hNm1N : (N - 1 : ℕ) ≤ N := Nat.sub_le N 1
    have hlogMono : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast hNm1N)
    have hnatlog : (Nat.log 2 (N - 1) : ℝ) ≤
        Real.log (N : ℝ) / Real.log 2 := by
      calc
        (Nat.log 2 (N - 1) : ℝ) ≤
            Real.logb (2 : ℝ) (((N - 1 : ℕ) : ℝ)) :=
          Real.natLog_le_logb (N - 1) 2
        _ = Real.log ((N - 1 : ℕ) : ℝ) / Real.log 2 := by rw [Real.logb]
        _ ≤ Real.log (N : ℝ) / Real.log 2 :=
          div_le_div_of_nonneg_right hlogMono hlog2.le
    have hlogPow := Real.log_natCast_le_rpow_div N hδ
    have hnatlogPow : (Nat.log 2 (N - 1) : ℝ) ≤
        (δ * Real.log 2)⁻¹ * (N : ℝ) ^ δ := by
      calc
        (Nat.log 2 (N - 1) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := hnatlog
        _ ≤ ((N : ℝ) ^ δ / δ) / Real.log 2 := by
          gcongr
        _ = (δ * Real.log 2)⁻¹ * (N : ℝ) ^ δ := by field_simp
    have hNpow1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num)
        (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)) hδ.le
    have hcount : ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ≤
        K * (N : ℝ) ^ δ := by
      push_cast
      dsimp only [K]
      nlinarith [mul_nonneg (inv_nonneg.mpr
        (mul_nonneg hδ.le hlog2.le))
          (Real.rpow_nonneg (Nat.cast_nonneg N) δ)]
    have hsqrt : Real.sqrt (N : ℝ) ≤ ((N.sqrt + 1 : ℕ) : ℝ) :=
      by simpa only [Nat.cast_add, Nat.cast_one] using
        (Real.real_sqrt_lt_nat_sqrt_succ (a := N)).le
    have hsqrt0 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hrpow : (((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)) ≤
        (N : ℝ) ^ (-(η / 2)) := by
      calc
        (((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)) ≤
            Real.sqrt (N : ℝ) ^ (-η) :=
          Real.rpow_le_rpow_of_nonpos hsqrt0 hsqrt (by linarith)
        _ = (N : ℝ) ^ (-(η / 2)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          congr 1
          ring
    have hleft0 : 0 ≤ ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpref0 : 0 ≤ K * (N : ℝ) ^ δ :=
      mul_nonneg hK0 (Real.rpow_nonneg (Nat.cast_nonneg N) δ)
    calc
      ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) *
            ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η)
          ≤ (K * (N : ℝ) ^ δ) * (N : ℝ) ^ (-(η / 2)) := by
            exact mul_le_mul hcount hrpow
              (Real.rpow_nonneg (by positivity) _) hpref0
      _ = K * (N : ℝ) ^ (-δ) := by
        have hNr : (0 : ℝ) < N := by positivity
        rw [mul_assoc, ← Real.rpow_add hNr]
        congr 2
        dsimp only [δ]
        ring
  · exact hpow

/-- The high-prime square-root tail tends to zero under interval power
saving for the switched monomial. -/
theorem powerFloorGCD_largePrime_sqrt_tendsto_of_intervalPowerSaving
    (α : ℝ) (hα : 1 < α) (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C)
    (hdisc : MonomialIntervalPowerSaving (α - 1) (α + 1) η C) :
    Tendsto (fun N ↦ prefixRatio
      (primeWindowEvent (powerFloorGCD α) N.sqrt N) N)
      atTop (nhds 0) := by
  have hone := tendsto_natLog_mul_sqrtSucc_rpow_neg 1 (by norm_num)
  have heta := tendsto_natLog_mul_sqrtSucc_rpow_neg η hη
  have hmajor : Tendsto (fun N : ℕ ↦
      (Nat.log 2 (N - 1) + 1 : ℕ) *
        (((N.sqrt + 1 : ℕ) : ℝ)⁻¹ +
          C * ((N.sqrt + 1 : ℕ) : ℝ) ^ (-η))) atTop (nhds 0) := by
    have hscaled := heta.const_mul C
    convert hone.add hscaled using 1
    · funext N
      rw [Real.rpow_neg_one]
      ring
    · simp
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦ by
      unfold prefixRatio
      positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact powerFloorGCD_largePrime_sqrt_prefixRatio_le
      α hα N hN η C hη hC hdisc
  · exact hmajor

/-- Split a prime-window event at an arbitrary hyperbola cutoff. -/
lemma primeWindowEvent_subset_split (ξ : ℕ → ℕ) (D Y U : ℕ) :
    {n | primeWindowEvent ξ D U n} ⊆
      {n | primeWindowEvent ξ D Y n} ∪
        {n | primeWindowEvent ξ Y U n} := by
  rintro n ⟨hn, p, hp, hDp, hpU, hpdvd⟩
  by_cases hpY : p ≤ Y
  · exact Or.inl ⟨hn, p, hp, hDp, hpY, hpdvd⟩
  · exact Or.inr ⟨hn, p, hp, lt_of_not_ge hpY, hpU, hpdvd⟩

/-- Cardinal form of the hyperbola split. -/
theorem prefixCount_primeWindowEvent_le_split (ξ : ℕ → ℕ)
    (D Y U N : ℕ) :
    prefixCount (primeWindowEvent ξ D U) N ≤
      prefixCount (primeWindowEvent ξ D Y) N +
        prefixCount (primeWindowEvent ξ Y U) N := by
  classical
  unfold prefixCount
  let A := (Finset.range N).filter (primeWindowEvent ξ D U)
  let B := (Finset.range N).filter (primeWindowEvent ξ D Y)
  let C := (Finset.range N).filter (primeWindowEvent ξ Y U)
  have hsub : A ⊆ B ∪ C := by
    intro n hnA
    simp only [A, Finset.mem_filter] at hnA
    rcases primeWindowEvent_subset_split ξ D Y U hnA.2 with hnB | hnC
    · change primeWindowEvent ξ D Y n at hnB
      exact Finset.mem_union_left C (by simp [B, hnA.1, hnB])
    · change primeWindowEvent ξ Y U n at hnC
      exact Finset.mem_union_right B (by simp [C, hnA.1, hnC])
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le B C)

/-- Ratio form of the hyperbola split. -/
theorem prefixRatio_primeWindowEvent_le_split (ξ : ℕ → ℕ)
    (D Y U N : ℕ) :
    prefixRatio (primeWindowEvent ξ D U) N ≤
      prefixRatio (primeWindowEvent ξ D Y) N +
        prefixRatio (primeWindowEvent ξ Y U) N := by
  rw [prefixRatio, prefixRatio, prefixRatio]
  have hnat := prefixCount_primeWindowEvent_le_split ξ D Y U N
  have hreal : (prefixCount (primeWindowEvent ξ D U) N : ℝ) ≤
      (prefixCount (primeWindowEvent ξ D Y) N : ℝ) +
        prefixCount (primeWindowEvent ξ Y U) N := by
    exact_mod_cast hnat
  calc
    (prefixCount (primeWindowEvent ξ D U) N : ℝ) / N
        ≤ ((prefixCount (primeWindowEvent ξ D Y) N : ℝ) +
          prefixCount (primeWindowEvent ξ Y U) N) / N :=
      div_le_div_of_nonneg_right hreal (Nat.cast_nonneg N)
    _ = (prefixCount (primeWindowEvent ξ D Y) N : ℝ) / N +
          (prefixCount (primeWindowEvent ξ Y U) N : ℝ) / N := by ring

/-- Abstract hyperbola-tail assembly.  The first input controls the sum of
local divisor counts below `Y N`; the second controls all witnesses above
`Y N`.  This is the exact interface delivered by the two applications of
uniform monomial discrepancy in the superlinear proof. -/
theorem largePrime_tail_of_hyperbola_bounds
    (ξ : ℕ → ℕ) (hξ : ∀ n, ξ n ∣ n) (Y : ℕ → ℕ)
    (hsmall : ∀ ε > 0, ∃ D₀, ∀ D ≥ D₀,
      ∀ᶠ N : ℕ in atTop,
        (∑ p ∈ primeWindow D (Y N),
          prefixRatio (localDivisorEvent ξ p) N) < ε)
    (hlarge : Tendsto
      (fun N ↦ prefixRatio (primeWindowEvent ξ (Y N) N) N)
      atTop (nhds 0)) :
    ∀ ε > 0, ∃ D₀, ∀ D ≥ D₀,
      ∀ᶠ N : ℕ in atTop, prefixRatio (largePrimeEvent ξ D) N < ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨D₀, hD₀⟩ := hsmall (ε / 2) hhalf
  refine ⟨D₀, fun D hD ↦ ?_⟩
  have hL : ∀ᶠ N : ℕ in atTop,
      prefixRatio (primeWindowEvent ξ (Y N) N) N < ε / 2 := by
    exact hlarge.eventually (Iio_mem_nhds hhalf)
  filter_upwards [hD₀ D hD, hL] with N hS hL
  have hfinite : prefixRatio (largePrimeEvent ξ D) N =
      prefixRatio (primeWindowEvent ξ D N) N := by
    unfold prefixRatio prefixCount
    rw [filter_largePrimeEvent_eq_filter_primeWindowEvent ξ hξ D N]
  rw [hfinite]
  calc
    prefixRatio (primeWindowEvent ξ D N) N
        ≤ prefixRatio (primeWindowEvent ξ D (Y N)) N +
            prefixRatio (primeWindowEvent ξ (Y N) N) N :=
      prefixRatio_primeWindowEvent_le_split ξ D (Y N) N N
    _ ≤ (∑ p ∈ primeWindow D (Y N),
          prefixRatio (localDivisorEvent ξ p) N) +
            prefixRatio (primeWindowEvent ξ (Y N) N) N := by
      gcongr
      exact prefixRatio_primeWindowEvent_le_sum_local ξ D (Y N) N
    _ < ε := by linarith

/-- The final superlinear sieve assembly once the fixed-divisor
equidistribution and the two hyperbola estimates have been proved by the
monomial-discrepancy module. -/
theorem superlinear_exactOne_tendsto_of_discrepancy_inputs
    (α : ℝ)
    (hlocal : ∀ d, 0 < d →
      Tendsto (prefixRatio (localDivisorEvent (powerFloorGCD α) d)) atTop
        (nhds ((d : ℝ)⁻¹ ^ 2)))
    (Y : ℕ → ℕ)
    (hsmall : ∀ ε > 0, ∃ D₀, ∀ D ≥ D₀,
      ∀ᶠ N : ℕ in atTop,
        (∑ p ∈ primeWindow D (Y N),
          prefixRatio (localDivisorEvent (powerFloorGCD α) p) N) < ε)
    (hlarge : Tendsto
      (fun N ↦ prefixRatio
        (primeWindowEvent (powerFloorGCD α) (Y N) N) N)
      atTop (nhds 0)) :
    Tendsto (prefixRatio (exactOneEvent (powerFloorGCD α))) atTop
      (nhds (6 / Real.pi ^ 2)) := by
  apply exactOne_tendsto_of_localDivisor_and_largePrime (powerFloorGCD α) hlocal
  exact largePrime_tail_of_hyperbola_bounds (powerFloorGCD α)
    (powerFloorGCD_dvd_index α) Y hsmall hlarge

/-- Complete superlinear sieve theorem from the two uniform monomial
power-saving inputs.  Prefix discrepancy for exponent `α` controls local
divisors up to `sqrt N`; interval discrepancy for exponent `α-1` controls
the hyperbola-switched dyadic blocks above `sqrt N`. -/
theorem superlinear_exactOne_tendsto_of_powerSaving
    (α : ℝ) (hα : 1 < α)
    (η₁ C₁ : ℝ) (hη₁0 : 0 < η₁) (hη₁1 : η₁ < 1) (hC₁ : 0 ≤ C₁)
    (hprefix : MonomialPrefixPowerSaving α (α - 1) η₁ C₁)
    (η₂ C₂ : ℝ) (hη₂ : 0 < η₂) (hC₂ : 0 ≤ C₂)
    (hinterval : MonomialIntervalPowerSaving (α - 1) (α + 1) η₂ C₂) :
    Tendsto (prefixRatio (exactOneEvent (powerFloorGCD α))) atTop
      (nhds (6 / Real.pi ^ 2)) := by
  apply superlinear_exactOne_tendsto_of_discrepancy_inputs α
    (Y := fun N ↦ N.sqrt)
  · intro d hd
    exact powerFloorGCD_local_tendsto_of_monomialPrefixPowerSaving
      α hα d hd η₁ C₁ hη₁0 hC₁ hprefix
  · exact powerFloorGCD_smallPrime_hyperbola_of_prefixPowerSaving
      α hα η₁ C₁ hη₁0 hη₁1 hC₁ hprefix
  · exact powerFloorGCD_largePrime_sqrt_tendsto_of_intervalPowerSaving
      α hα η₂ C₂ hη₂ hC₂ hinterval

end Erdos1149
