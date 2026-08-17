import Mathlib
import ErdosProblems.Erdos697.Erdos697Cover

/-!
# A density-zero bound for increasing totients

This file isolates the elementary divisibility argument for the `o(N)` part
of Erdős Problem 49.  The input is only that Euler's totient is strictly
increasing on a finite set.  The output is uniform in that finite set.

The proof uses the fact that almost every integer has arbitrarily many
distinct prime divisors.  Each odd prime divisor contributes a factor `2` to
the totient.  Thus, outside a set of arbitrarily small density, all totients
are divisible by a prescribed power of two.  Strict increase makes the
totient values distinct, and there are only `N / 2^k + 1` multiples of
`2^k` below `N`.
-/

open Filter Set Topology
open scoped BigOperators

namespace Erdos49.Density

noncomputable section

/-- The selected prime divisors from the primes below `M`. -/
def selectedPrimes (M n : ℕ) : Finset ℕ :=
  ((Finset.range M).filter Nat.Prime).filter fun p ↦ p ∣ n

/-- Integers having at most `k` prime divisors below `M`. -/
def fewSelectedPrimes (k M : ℕ) : Set ℕ :=
  {n | (selectedPrimes M n).card ≤ k}

/-- The Bernoulli probability which occurs as the density of
`fewSelectedPrimes k M`. -/
def fewSelectedDensity (k M : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ :
      Finset (Finset ↑((Finset.range M).filter Nat.Prime))).filter
        (fun S ↦ S.card ≤ k),
    Erdos697.Bernoulli.weight Finset.univ
      (fun p : ↑((Finset.range M).filter Nat.Prime) ↦
        1 / (p.1 : ℝ)) S

/-- The mean number of selected primes in the finite Bernoulli model. -/
def selectedPrimeMean (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range M).filter Nat.Prime, 1 / (p : ℝ)

/-- Every collection of `k` distinct odd prime divisors of `n` contributes
at least `2^k` to Euler's product for `φ(n)`. -/
lemma pow_two_dvd_totient_of_odd_primeFactors
    {n k : ℕ} {s : Finset ℕ}
    (hs : s ⊆ n.primeFactors)
    (hsodd : ∀ p ∈ s, p ≠ 2)
    (hk : k ≤ s.card) :
    2 ^ k ∣ Nat.totient n := by
  have htwo_each : ∀ p ∈ s, 2 ∣ p - 1 := by
    intro p hp
    exact even_iff_two_dvd.mp
      ((Nat.prime_of_mem_primeFactors (hs hp)).even_sub_one (hsodd p hp))
  have htwo_prod : 2 ^ s.card ∣ ∏ p ∈ s, (p - 1) := by
    simpa using
      (Finset.prod_dvd_prod_of_dvd (s := s) (fun _ ↦ 2) (fun p ↦ p - 1)
        htwo_each)
  have hsmall_prod : (∏ p ∈ s, (p - 1)) ∣
      ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_dvd_prod_of_subset s n.primeFactors (fun p ↦ p - 1) hs
  have hpow : 2 ^ k ∣ 2 ^ s.card := pow_dvd_pow 2 hk
  rw [Nat.totient_eq_div_primeFactors_mul]
  exact hpow.trans (htwo_prod.trans (hsmall_prod.trans (dvd_mul_left _ _)))

/-- More than `k` selected prime divisors force `2^k ∣ φ(n)`.  The
one possible selected even prime is discarded. -/
lemma pow_two_dvd_totient_of_many_selected {k M n : ℕ}
    (hcard : k < (selectedPrimes M n).card) :
    2 ^ k ∣ Nat.totient n := by
  by_cases hn : n = 0
  · simp [hn]
  let s := (selectedPrimes M n).erase 2
  have hs : s ⊆ n.primeFactors := by
    intro p hp
    have hpselected : p ∈ selectedPrimes M n :=
      (Finset.mem_erase.mp hp).2
    have hpdata := Finset.mem_filter.mp hpselected
    have hpprime := (Finset.mem_filter.mp hpdata.1).2
    exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdata.2, hn⟩
  have hsodd : ∀ p ∈ s, p ≠ 2 := by
    intro p hp
    exact (Finset.mem_erase.mp hp).1
  have hk : k ≤ s.card := by
    by_cases htwo : 2 ∈ selectedPrimes M n
    · rw [show s.card = (selectedPrimes M n).card - 1 by
          simp [s, Finset.card_erase_of_mem htwo]]
      omega
    · simp [s, Finset.erase_eq_of_notMem htwo]
      omega
  exact pow_two_dvd_totient_of_odd_primeFactors hs hsodd hk

/-- The exact natural density of the finite-prime exceptional set, expressed
as a Bernoulli lower-tail probability. -/
lemma fewSelectedPrimes_hasDensity (k M : ℕ) :
    (fewSelectedPrimes k M).HasDensity (fewSelectedDensity k M) := by
  let P := (Finset.range M).filter Nat.Prime
  let q : ↑P → ℕ := fun p ↦ p.1
  have hq : ∀ i, 0 < q i := fun i ↦
    (Finset.mem_filter.mp i.2).2.pos
  have hpair : Pairwise (Function.onFun Nat.Coprime q) := by
    intro p r hpr
    have hp := (Finset.mem_filter.mp p.2).2
    have hr := (Finset.mem_filter.mp r.2).2
    exact hp.coprime_iff_not_dvd.mpr fun hd ↦
      hpr (Subtype.ext ((Nat.prime_dvd_prime_iff_eq hp hr).mp hd))
  have hacop : ∀ i, Nat.Coprime 1 (q i) := fun _ ↦ Nat.coprime_one_left _
  have h := Erdos697.Cover.eventSet_hasDensity
    (I := ↑P) 1 (by norm_num) q hq hpair hacop
    (fun S : Finset ↑P ↦ S.card ≤ k)
  convert h using 1
  · ext n
    simp only [fewSelectedPrimes, Set.mem_ofPred_eq,
      Erdos697.Cover.eventSet, one_dvd, true_and]
    have hcard :
        ((P.filter fun p ↦ p ∣ n).card) =
          ((P.attach.filter fun p ↦ p.1 ∣ n).card) := by
      have hfilter := Finset.filter_attach (fun p : ℕ ↦ p ∣ n) P
      rw [hfilter]
      simp
    change ((P.filter fun p ↦ p ∣ n).card ≤ k) ↔
      ((P.attach.filter fun p ↦ p.1 ∣ n).card ≤ k)
    rw [hcard]
  · simp [fewSelectedDensity, P, q]

/-- The reciprocal-prime mean tends to infinity.  This is the only analytic
input needed for the density-zero argument. -/
lemma selectedPrimeMean_tendsto_atTop :
    Tendsto selectedPrimeMean atTop atTop := by
  have hnonsum : ¬ Summable
      (fun p : ℕ ↦ if p.Prime then (1 / (p : ℝ)) else 0) := by
    intro h
    apply not_summable_one_div_on_primes
    convert h using 1
    ext p
    simp [Set.indicator]
  have hsum : Tendsto
      (fun M : ℕ ↦ ∑ p ∈ (Finset.range M).filter Nat.Prime,
        (1 / (p : ℝ))) atTop atTop := by
    convert (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun p : ℕ ↦ by split_ifs <;> positivity)).mp hnonsum using 1
    funext M
    simp [Finset.sum_filter]
  change Tendsto
    (fun M : ℕ ↦ ∑ p ∈ (Finset.range M).filter Nat.Prime,
      1 / (p : ℝ)) atTop atTop
  exact hsum

/-- For each fixed `k`, the density of integers having at most `k` selected
prime divisors tends to zero as the prime cutoff tends to infinity. -/
lemma fewSelectedDensity_tendsto_zero (k : ℕ) :
    Tendsto (fewSelectedDensity k) atTop (nhds 0) := by
  let c : ℝ :=
    (1 / 2 : ℝ) * ((1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ))) +
      (1 / (1 + ((1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)))) - 1)
  have hc : c < 0 := by
    exact Erdos697.Bernoulli.lower_exponent_neg (by norm_num) (by norm_num)
  have hmean := selectedPrimeMean_tendsto_atTop
  have hexp : Tendsto (fun M ↦ Real.exp (c * selectedPrimeMean M))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (hmean.const_mul_atTop_of_neg hc)
  apply squeeze_zero' (g := fun M ↦ Real.exp (c * selectedPrimeMean M))
  · exact Eventually.of_forall fun M ↦ by
      unfold fewSelectedDensity
      apply Finset.sum_nonneg
      intro S hS
      apply Erdos697.Bernoulli.weight_nonneg
      · intro p hp
        positivity
      · intro p hp
        have hpPrime := (Finset.mem_filter.mp p.2).2
        have hpOne : (1 : ℝ) ≤ p.1 := by exact_mod_cast hpPrime.one_le
        exact (div_le_one (by positivity)).2 hpOne
      · apply Finset.mem_powerset.mpr
        intro p hp
        simpa using p.property
  · filter_upwards [hmean.eventually_ge_atTop (2 * (k + 1 : ℝ))] with M hM
    let P := (Finset.range M).filter Nat.Prime
    let p : ↑P → ℝ := fun q ↦ 1 / (q.1 : ℝ)
    have hp0 : ∀ q ∈ (Finset.univ : Finset ↑P), 0 ≤ p q := by
      intro q hq
      positivity
    have hp1 : ∀ q ∈ (Finset.univ : Finset ↑P), p q ≤ 1 := by
      intro q hq
      have hqPrime := (Finset.mem_filter.mp q.2).2
      have hqOne : (1 : ℝ) ≤ q.1 := by exact_mod_cast hqPrime.one_le
      exact (div_le_one (by positivity)).2 hqOne
    have hK : ((k + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * selectedPrimeMean M := by
      norm_num [Nat.cast_add] at hM ⊢
      linarith
    have htail := Erdos697.Bernoulli.lower_tail_chernoff
      (Finset.univ : Finset ↑P) p hp0 hp1
      (K := k + 1) (EW := selectedPrimeMean M) (r := (1 / 2 : ℝ))
      (by
        exact (Finset.sum_attach P
          (fun q : ℕ ↦ 1 / (q : ℝ))).symm)
      (by norm_num) (by norm_num) hK
    change (∑ T ∈ (Finset.univ : Finset (Finset ↑P)).filter
        (fun T ↦ T.card ≤ k),
      Erdos697.Bernoulli.weight (Finset.univ : Finset ↑P) p T) ≤
        Real.exp (c * selectedPrimeMean M)
    rw [show (Finset.univ : Finset (Finset ↑P)) =
        (Finset.univ : Finset ↑P).powerset by
      ext T
      simp only [Finset.mem_univ, Finset.mem_powerset, true_iff]
      intro q hq
      simpa using q.property]
    simpa [Nat.lt_succ_iff, c] using htail
  · exact hexp

end

end Erdos49.Density
