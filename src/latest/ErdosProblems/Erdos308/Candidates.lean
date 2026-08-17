import ErdosProblems.Erdos285.Dispersion
import ErdosProblems.Erdos285.PrimePowers
import Mathlib.NumberTheory.Chebyshev

/-!
# The four-prime candidate family in Martin's Lemma 12

This file constructs the candidate multipliers used in the large-prime-power
elimination step.  For a scale `t`, the source primes lie in `(c*t,t]`, with
the prime below the prime power being eliminated removed.  Candidate
multipliers are products of four-element subsets of that prime band.

The construction is deliberately separated from the modular dispersion
argument.  Its exported facts are unconditional: exact cardinality, unique
factorisation, the product interval, coprimality to the eliminated prime
power, and a sharp description of all prime factors.  A final existence
theorem extracts a candidate family of any prescribed cardinality allowed by
the prime-number-theorem count.
-/

namespace Erdos308.Candidates

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285.PrimePowers

/-- The nonnegative fourth root, expressed using two square roots so that its
fourth-power identity is elementary. -/
def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

lemma fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x := Real.sqrt_nonneg _

lemma fourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < fourthRoot x := by
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)

lemma fourthRoot_lt_one {x : ℝ} (hx1 : x < 1) : fourthRoot x < 1 := by
  apply (Real.sqrt_lt' (by norm_num)).2
  apply (Real.sqrt_lt' (by norm_num)).2
  simpa using hx1

lemma fourthRoot_mono {x y : ℝ} (hxy : x ≤ y) : fourthRoot x ≤ fourthRoot y := by
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy)

lemma fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : fourthRoot x ^ 4 = x := by
  rw [show fourthRoot x ^ 4 = (Real.sqrt (Real.sqrt x) ^ 2) ^ 2 by
      simp only [fourthRoot]; ring,
    Real.sq_sqrt (Real.sqrt_nonneg x), Real.sq_sqrt hx]

/-- Primes in the half-open real interval `(c*t,t]`. -/
def primeBand (c t : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊t⌋₊ \ Nat.primesLE ⌊c * t⌋₊

/-- The prime band with the base prime of the current prime power removed. -/
def candidatePrimes (p : ℕ) (c t : ℝ) : Finset ℕ :=
  (primeBand c t).erase p

/-- Products of four distinct primes from the candidate band. -/
def rawCandidates (p : ℕ) (c t : ℝ) : Finset ℕ :=
  ((candidatePrimes p c t).powersetCard 4).image fun S ↦ S.prod id

lemma candidatePrimes_mono_lowerEndpoint {p : ℕ} {c d t : ℝ}
    (hcd : c ≤ d) (ht : 0 ≤ t) :
    candidatePrimes p d t ⊆ candidatePrimes p c t := by
  intro r hr
  rw [candidatePrimes, Finset.mem_erase] at hr ⊢
  refine ⟨hr.1, ?_⟩
  rw [primeBand, Finset.mem_sdiff] at hr ⊢
  refine ⟨hr.2.1, ?_⟩
  intro hrc
  apply hr.2.2
  exact Nat.primesLE_mono
    (Nat.floor_mono (mul_le_mul_of_nonneg_right hcd ht)) hrc

lemma rawCandidates_mono_lowerEndpoint {p : ℕ} {c d t : ℝ}
    (hcd : c ≤ d) (ht : 0 ≤ t) :
    rawCandidates p d t ⊆ rawCandidates p c t := by
  intro n hn
  rw [rawCandidates, Finset.mem_image] at hn ⊢
  obtain ⟨S, hS, rfl⟩ := hn
  refine ⟨S, ?_, rfl⟩
  rw [Finset.mem_powersetCard] at hS ⊢
  exact ⟨hS.1.trans (candidatePrimes_mono_lowerEndpoint hcd ht), hS.2⟩

lemma mem_primeBand {c t : ℝ} {r : ℕ} (_hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : r ∈ primeBand c t) :
    r.Prime ∧ c * t < r ∧ (r : ℝ) ≤ t := by
  rw [primeBand, Finset.mem_sdiff] at hr
  have hrUpper := Nat.mem_primesLE.mp hr.1
  have hrLower : ⌊c * t⌋₊ < r := by
    simpa [Nat.mem_primesLE, hrUpper.2] using hr.2
  refine ⟨hrUpper.2, Nat.lt_of_floor_lt hrLower, ?_⟩
  exact (Nat.cast_le.mpr hrUpper.1).trans (Nat.floor_le ht)

lemma mem_candidatePrimes {p r : ℕ} {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : r ∈ candidatePrimes p c t) :
    r.Prime ∧ r ≠ p ∧ c * t < r ∧ (r : ℝ) ≤ t := by
  rw [candidatePrimes, Finset.mem_erase] at hr
  have hband := mem_primeBand hc ht hr.2
  exact ⟨hband.1, hr.1, hband.2.1, hband.2.2⟩

lemma candidatePrime_pos {p r : ℕ} {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : r ∈ candidatePrimes p c t) : 0 < r :=
  (mem_candidatePrimes hc ht hr).1.pos

private lemma product_of_primes_factors_toFinset {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    (S.prod id).primeFactorsList.toFinset = S := by
  have hprod : (S.sort (· ≤ ·)).prod = S.prod id := by
    calc
      (S.sort (· ≤ ·)).prod = (S.sort (· ≤ ·)).toFinset.prod id := by
        simpa using (List.prod_toFinset id (S.sort_nodup (· ≤ ·))).symm
      _ = S.prod id := by rw [Finset.sort_toFinset]
  have hprime : ∀ p ∈ S.sort (· ≤ ·), p.Prime := by
    intro p hp
    exact hS p ((Finset.mem_sort (· ≤ ·)).mp hp)
  have hperm : List.Perm (S.sort (· ≤ ·)) (S.prod id).primeFactorsList :=
    Nat.primeFactorsList_unique hprod hprime
  exact (List.toFinset_eq_of_perm _ _ hperm).symm.trans (Finset.sort_toFinset _ _)

lemma prod_injective_on_candidatePrimeSubsets (p : ℕ) (c t : ℝ) :
    Set.InjOn (fun S : Finset ℕ ↦ S.prod id) (candidatePrimes p c t).powerset := by
  intro A hA B hB hprod
  have hAprime : ∀ r ∈ A, r.Prime := by
    intro r hr
    have hr' := Finset.mem_powerset.mp hA hr
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp
      (Finset.mem_erase.mp hr').2).1).2
  have hBprime : ∀ r ∈ B, r.Prime := by
    intro r hr
    have hr' := Finset.mem_powerset.mp hB hr
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp
      (Finset.mem_erase.mp hr').2).1).2
  change A.prod id = B.prod id at hprod
  calc
    A = (A.prod id).primeFactorsList.toFinset :=
      (product_of_primes_factors_toFinset hAprime).symm
    _ = (B.prod id).primeFactorsList.toFinset := by rw [hprod]
    _ = B := product_of_primes_factors_toFinset hBprime

lemma rawCandidates_card (p : ℕ) (c t : ℝ) :
    (rawCandidates p c t).card = Nat.choose (candidatePrimes p c t).card 4 := by
  rw [rawCandidates, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard 4 (candidatePrimes p c t)
  · apply (prod_injective_on_candidatePrimeSubsets p c t).mono
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1

lemma rawCandidates_card_lower (p : ℕ) (c t : ℝ) :
    ((((candidatePrimes p c t).card + 1 - 4 : ℕ) : ℝ) ^ 4) /
        ((Nat.factorial 4 : ℕ) : ℝ) ≤
      (rawCandidates p c t).card := by
  rw [rawCandidates_card]
  exact Nat.pow_le_choose 4 (candidatePrimes p c t).card

lemma mem_rawCandidates_source {p n : ℕ} {c t : ℝ}
    (hn : n ∈ rawCandidates p c t) :
    ∃ S ⊆ candidatePrimes p c t, S.card = 4 ∧ n = S.prod id := by
  rw [rawCandidates, Finset.mem_image] at hn
  obtain ⟨S, hS, rfl⟩ := hn
  exact ⟨S, (Finset.mem_powersetCard.mp hS).1,
    (Finset.mem_powersetCard.mp hS).2, rfl⟩

lemma rawCandidate_isKPrimeProductAway {p ν n : ℕ} {c t : ℝ}
    (hp : p.Prime) (hn : n ∈ rawCandidates p c t) :
    Erdos285.Dispersion.IsKPrimeProductAway 4 (p ^ ν) n := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  refine ⟨S, hcard, ?_, rfl⟩
  intro r hr
  have hrC := Finset.mem_erase.mp (hS hr)
  have hrPrime : r.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hrC.2).1).2
  refine ⟨hrPrime, ?_⟩
  exact hrPrime.coprime_iff_not_dvd.mp
    (Nat.Coprime.pow_right ν ((Nat.coprime_primes hrPrime hp).2 hrC.1))

lemma rawCandidate_coprime_primePow {p ν n : ℕ} {c t : ℝ}
    (hp : p.Prime) (hn : n ∈ rawCandidates p c t) :
    Nat.Coprime n (p ^ ν) :=
  Erdos285.Dispersion.isKPrimeProductAway_coprime
    (rawCandidate_isKPrimeProductAway hp hn)

lemma rawCandidate_pos {p n : ℕ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hn : n ∈ rawCandidates p c t) : 0 < n := by
  obtain ⟨S, hS, -, rfl⟩ := mem_rawCandidates_source hn
  exact Finset.prod_pos fun r hr ↦ candidatePrime_pos hc ht (hS hr)

lemma rawCandidate_upper {p n : ℕ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hn : n ∈ rawCandidates p c t) :
    (n : ℝ) ≤ t ^ 4 := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  push_cast
  calc
    ∏ r ∈ S, (r : ℝ) ≤ ∏ _r ∈ S, t := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
        (fun r hr ↦ (mem_candidatePrimes hc ht (hS hr)).2.2.2)
    _ = t ^ 4 := by simp [Finset.prod_const, hcard]

lemma rawCandidate_upper_strict {p n : ℕ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (hn : n ∈ rawCandidates p c t) :
    (n : ℝ) < t ^ 4 := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  push_cast
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r, hr⟩ := hSne
  have hEraseCard : (S.erase r).card = 3 := by
    rw [Finset.card_erase_of_mem hr, hcard]
  have hErase : (S.erase r).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨s, hsErase⟩ := hErase
  have hs : s ∈ S := Finset.mem_of_mem_erase hsErase
  have hsr : s ≠ r := (Finset.mem_erase.mp hsErase).1
  have hrle := (mem_candidatePrimes hc ht.le (hS hr)).2.2.2
  have hsle := (mem_candidatePrimes hc ht.le (hS hs)).2.2.2
  have hstrict : ∃ u ∈ S, (u : ℝ) < t := by
    by_cases hrt : (r : ℝ) < t
    · exact ⟨r, hr, hrt⟩
    · have hre : (r : ℝ) = t := le_antisymm hrle (le_of_not_gt hrt)
      have hst : (s : ℝ) < t := by
        by_contra hnst
        have hse : (s : ℝ) = t := le_antisymm hsle (le_of_not_gt hnst)
        apply hsr
        exact_mod_cast hse.trans hre.symm
      exact ⟨s, hs, hst⟩
  calc
    ∏ u ∈ S, (u : ℝ) < ∏ _u ∈ S, t := by
      apply Finset.prod_lt_prod
      · intro u hu
        exact_mod_cast (mem_candidatePrimes hc ht.le (hS hu)).1.pos
      · intro u hu
        exact (mem_candidatePrimes hc ht.le (hS hu)).2.2.2
      · exact hstrict
    _ = t ^ 4 := by simp [Finset.prod_const, hcard]

lemma rawCandidate_lower {p n : ℕ} {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) (hn : n ∈ rawCandidates p c t) :
    (c * t) ^ 4 < (n : ℝ) := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  push_cast
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hprod : (c * t) ^ S.card < ∏ r ∈ S, (r : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_lt_prod_of_nonempty
      (fun _ _ ↦ mul_pos hc ht)
      (fun r hr ↦ (mem_candidatePrimes hc.le ht.le (hS hr)).2.2.1) hSne
  simpa [hcard] using hprod

/-! ## Extracting a prescribed candidate family -/

theorem exists_rawCandidates_subset_card_eq {p C : ℕ} {c t : ℝ}
    (hC : C ≤ (rawCandidates p c t).card) :
    ∃ M ⊆ rawCandidates p c t, M.card = C :=
  Finset.exists_subset_card_eq hC

lemma rawCandidate_squarefree {p n : ℕ} {c t : ℝ}
    (hn : n ∈ rawCandidates p c t) : Squarefree n := by
  obtain ⟨S, hS, -, rfl⟩ := mem_rawCandidates_source hn
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro r hr s hs hrs
    have hrC := Finset.mem_erase.mp (hS hr)
    have hsC := Finset.mem_erase.mp (hS hs)
    have hrPrime : r.Prime :=
      (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hrC.2).1).2
    have hsPrime : s.Prime :=
      (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hsC.2).1).2
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hrPrime hsPrime).2 hrs)
  · intro r hr
    have hrC := Finset.mem_erase.mp (hS hr)
    exact ((Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hrC.2).1).2).squarefree

lemma rawCandidate_primeFactors_eq {p n : ℕ} {c t : ℝ}
    (hn : n ∈ rawCandidates p c t) :
    ∃ S ⊆ candidatePrimes p c t, S.card = 4 ∧
      n = S.prod id ∧ n.primeFactors = S := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  refine ⟨S, hS, hcard, rfl, ?_⟩
  exact Nat.primeFactors_prod fun r hr ↦ by
    have hrC := Finset.mem_erase.mp (hS hr)
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hrC.2).1).2

lemma rawCandidate_primeFactors_lt {p ν n : ℕ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (htq : t ≤ (p ^ ν : ℕ))
    (hn : n ∈ rawCandidates p c t) :
    ∀ r ∈ n.primeFactors, r < p ^ ν := by
  obtain ⟨S, hS, -, -, hfac⟩ := rawCandidate_primeFactors_eq hn
  intro r hr
  rw [hfac] at hr
  have hrData := mem_candidatePrimes hc ht (hS hr)
  have hrleR : (r : ℝ) ≤ (p ^ ν : ℕ) := hrData.2.2.2.trans htq
  have hrle : r ≤ p ^ ν := by exact_mod_cast hrleR
  have hrne : r ≠ p ^ ν := by
    intro hre
    have hqprime : (p ^ ν).Prime := by simpa [← hre] using hrData.1
    have hνone : ν = 1 := hqprime.eq_one_of_pow
    subst ν
    apply hrData.2.1
    simpa using hre
  exact lt_of_le_of_ne hrle hrne

/-- The current prime power is the largest exact prime-power part of every
displayed denominator `p^ν*n`, provided the prime band lies below it. -/
lemma largestPrimePowerPart_primePow_mul_rawCandidate
    {p ν n : ℕ} {c t : ℝ}
    (hp : p.Prime) (hν : 0 < ν) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (htq : t ≤ (p ^ ν : ℕ)) (hn : n ∈ rawCandidates p c t) :
    largestPrimePowerPart (p ^ ν * n) = p ^ ν := by
  let q := p ^ ν
  have hqpos : 0 < q := pow_pos hp.pos ν
  have hqpp : IsPrimePow q :=
    (isPrimePow_pow_iff hν.ne').2 hp.isPrimePow
  have hcop : Nat.Coprime q n :=
    (rawCandidate_coprime_primePow hp hn).symm
  have hqmem : q ∈ primePowerParts (q * n) := by
    apply (mem_primePowerParts (mul_ne_zero hqpos.ne' (rawCandidate_pos hc ht hn).ne')).2
    refine ⟨hqpp, Nat.dvd_mul_right q n, ?_⟩
    simpa [Nat.mul_div_cancel_left n hqpos] using hcop
  apply Nat.le_antisymm
  · rw [largestPrimePowerPart_le_iff]
    intro ℓ hℓ
    have hspec := (mem_primePowerParts
      (mul_ne_zero hqpos.ne' (rawCandidate_pos hc ht hn).ne')).1 hℓ
    rcases hcop.isPrimePow_dvd_mul hspec.1 |>.1 hspec.2.1 with hdivq | hdivn
    · exact Nat.le_of_dvd hqpos hdivq
    · have hℓprime : ℓ.Prime := Nat.squarefree_and_prime_pow_iff_prime.mp
        ⟨(rawCandidate_squarefree hn).squarefree_of_dvd hdivn, hspec.1⟩
      have hℓfac : ℓ ∈ n.primeFactors :=
        hℓprime.mem_primeFactors hdivn (rawCandidate_pos hc ht hn).ne'
      exact (rawCandidate_primeFactors_lt hc ht htq hn ℓ hℓfac).le
  · exact le_largestPrimePowerPart hqmem

/-- The LCM of an arbitrary subfamily is squarefree: taking an LCM does not
reintroduce the multiplicities that would occur in the product of all
candidates. -/
lemma candidateFamily_lcm_squarefree {p : ℕ} {c t : ℝ} {M : Finset ℕ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hM : M ⊆ rawCandidates p c t) :
    Squarefree (M.lcm id) := by
  have hnonzero : ∀ m ∈ M, id m ≠ 0 := by
    intro m hm
    exact (rawCandidate_pos hc ht (hM hm)).ne'
  have hL0 : M.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr hnonzero
  apply Nat.squarefree_of_factorization_le_one hL0
  intro r
  rw [Finset.factorization_lcm hnonzero]
  refine Finset.sup_le_iff.mpr ?_
  intro m hm
  exact (rawCandidate_squarefree (hM hm)).natFactorization_le_one r

/-- Every prime power dividing the candidate LCM is in fact one of its source
primes, and therefore lies below the eliminated prime power once the source
band does. -/
lemma primePower_dvd_candidateFamily_lcm_lt
    {p ν ℓ : ℕ} {c t : ℝ} {M : Finset ℕ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (htq : t ≤ (p ^ ν : ℕ))
    (hM : M ⊆ rawCandidates p c t)
    (hℓpp : IsPrimePow ℓ) (hℓdvd : ℓ ∣ M.lcm id) : ℓ < p ^ ν := by
  have hLsquare := candidateFamily_lcm_squarefree hc ht hM
  have hℓprime : ℓ.Prime := Nat.squarefree_and_prime_pow_iff_prime.mp
    ⟨hLsquare.squarefree_of_dvd hℓdvd, hℓpp⟩
  have hprod : ℓ ∣ M.prod id := hℓdvd.trans (Finset.lcm_dvd_prod M id)
  obtain ⟨m, hm, hℓm⟩ := hℓprime.prime.exists_mem_finset_dvd hprod
  have hℓfac : ℓ ∈ m.primeFactors :=
    hℓprime.mem_primeFactors hℓm (rawCandidate_pos hc ht (hM hm)).ne'
  exact rawCandidate_primeFactors_lt hc ht htq (hM hm) ℓ hℓfac

/-- Combine a pre-existing prime-power bound for an old denominator quotient
with the candidate-LCM bound.  The coprime factorization of an LCM is used
here; unlike replacing the LCM by a product, it cannot spuriously add prime
exponents shared by the two sides. -/
lemma primePower_dvd_lcm_candidateFamily_lt
    {A p ν ℓ : ℕ} {c t : ℝ} {M : Finset ℕ}
    (hA0 : A ≠ 0) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (htq : t ≤ (p ^ ν : ℕ)) (hM : M ⊆ rawCandidates p c t)
    (hA : ∀ d : ℕ, IsPrimePow d → d ∣ A → d < p ^ ν)
    (hℓpp : IsPrimePow ℓ) (hℓdvd : ℓ ∣ Nat.lcm A (M.lcm id)) :
    ℓ < p ^ ν := by
  have hnonzero : ∀ m ∈ M, id m ≠ 0 := by
    intro m hm
    exact (rawCandidate_pos hc ht (hM hm)).ne'
  have hL0 : M.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr hnonzero
  have hdecomp := Nat.factorizationLCMLeft_mul_factorizationLCMRight hA0 hL0
  have hcop := Nat.coprime_factorizationLCMLeft_factorizationLCMRight A (M.lcm id)
  have hsplit : ℓ ∣ Nat.factorizationLCMLeft A (M.lcm id) ∨
      ℓ ∣ Nat.factorizationLCMRight A (M.lcm id) := by
    apply (hcop.isPrimePow_dvd_mul hℓpp).1
    rwa [hdecomp]
  rcases hsplit with hleft | hright
  · exact hA ℓ hℓpp (hleft.trans (Nat.factorizationLCMLeft_dvd_left A (M.lcm id)))
  · exact primePower_dvd_candidateFamily_lcm_lt hc ht htq hM hℓpp
      (hright.trans (Nat.factorizationLCMRight_dvd_right A (M.lcm id)))

/-- Candidate properties at the scale used in Lemma 12.  The lower prime-band
ratio is the fourth root of `ξ`; hence products of four band primes lie in
`(ξ*x/q,x/q]`. -/
theorem rawCandidate_elimination_properties
    {ξ : ℝ} {x p ν n : ℕ}
    (hξ : 0 < ξ) (_hξ1 : ξ < 1) (hx : 0 < x) (hp : p.Prime)
    (hn : n ∈ rawCandidates p (fourthRoot ξ)
      (fourthRoot ((x : ℝ) / (p ^ ν : ℕ)))) :
    Erdos285.Dispersion.IsKPrimeProductAway 4 (p ^ ν) n ∧
      Nat.Coprime n (p ^ ν) ∧
      ξ * x < ((p ^ ν) * n : ℕ) ∧
      (((p ^ ν) * n : ℕ) : ℝ) ≤ x ∧
      Squarefree n := by
  let q : ℕ := p ^ ν
  let c : ℝ := fourthRoot ξ
  let t : ℝ := fourthRoot ((x : ℝ) / q)
  have hqpos : 0 < q := pow_pos hp.pos ν
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hxq : 0 < (x : ℝ) / q := div_pos hxR hqR
  have hc : 0 < c := fourthRoot_pos hξ
  have ht : 0 < t := fourthRoot_pos hxq
  have hc4 : c ^ 4 = ξ := fourthRoot_pow_four hξ.le
  have ht4 : t ^ 4 = (x : ℝ) / q := fourthRoot_pow_four hxq.le
  have hn' : n ∈ rawCandidates p c t := by simpa [c, t, q] using hn
  have hnLower := rawCandidate_lower hc ht hn'
  have hnUpper := rawCandidate_upper hc.le ht.le hn'
  rw [mul_pow, hc4, ht4] at hnLower
  rw [ht4] at hnUpper
  have hLower : ξ * x < ((q * n : ℕ) : ℝ) := by
    push_cast
    calc
      ξ * (x : ℝ) = (q : ℝ) * (ξ * ((x : ℝ) / q)) := by
        field_simp [hqR.ne']
      _ < (q : ℝ) * n := mul_lt_mul_of_pos_left hnLower hqR
  have hUpper : (((q * n : ℕ) : ℝ)) ≤ x := by
    push_cast
    calc
      (q : ℝ) * n ≤ (q : ℝ) * ((x : ℝ) / q) :=
        mul_le_mul_of_nonneg_left hnUpper hqR.le
      _ = x := by field_simp [hqR.ne']
  refine ⟨?_, ?_, ?_, ?_, rawCandidate_squarefree hn'⟩
  · simpa [q, c, t] using rawCandidate_isKPrimeProductAway (p := p) (ν := ν) hp hn'
  · simpa [q, c, t] using rawCandidate_coprime_primePow (p := p) (ν := ν) hp hn'
  · simpa [q] using hLower
  · simpa [q] using hUpper

lemma rawCandidate_lt_eliminationScale
    {x p ν n : ℕ} {ξ : ℝ} (hx : 0 < x) (hp : p.Prime)
    (hn : n ∈ rawCandidates p (fourthRoot ξ)
      (fourthRoot ((x : ℝ) / (p ^ ν : ℕ)))) :
    (n : ℝ) < (x : ℝ) / (p ^ ν : ℕ) := by
  have hqpos : (0 : ℝ) < (p ^ ν : ℕ) := by
    exact_mod_cast pow_pos hp.pos ν
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hxq : 0 < (x : ℝ) / (p ^ ν : ℕ) := div_pos hxR hqpos
  have h := rawCandidate_upper_strict (fourthRoot_nonneg ξ)
    (fourthRoot_pos hxq) hn
  rwa [fourthRoot_pow_four hxq.le] at h

/-- Extract exactly `C` multipliers and retain every structural property used
by the dispersion and elimination arguments. -/
theorem exists_eliminationCandidateFamily
    {ξ : ℝ} {x p ν C : ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hx : 0 < x) (hp : p.Prime)
    (hC : C ≤ (rawCandidates p (fourthRoot ξ)
      (fourthRoot ((x : ℝ) / (p ^ ν : ℕ)))).card) :
    ∃ M : Finset ℕ,
      M.card = C ∧
      M ⊆ rawCandidates p (fourthRoot ξ)
        (fourthRoot ((x : ℝ) / (p ^ ν : ℕ))) ∧
      (∀ n ∈ M,
        Erdos285.Dispersion.IsKPrimeProductAway 4 (p ^ ν) n) ∧
      (∀ n ∈ M, Nat.Coprime n (p ^ ν)) ∧
      (∀ n ∈ M, ξ * x < (((p ^ ν) * n : ℕ) : ℝ) ∧
        (((p ^ ν) * n : ℕ) : ℝ) ≤ x) ∧
      (∀ n ∈ M, Squarefree n) := by
  obtain ⟨M, hM, hMcard⟩ := exists_rawCandidates_subset_card_eq hC
  refine ⟨M, hMcard, hM, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact (rawCandidate_elimination_properties hξ hξ1 hx hp (hM hn)).1
  · intro n hn
    exact (rawCandidate_elimination_properties hξ hξ1 hx hp (hM hn)).2.1
  · intro n hn
    exact ⟨(rawCandidate_elimination_properties hξ hξ1 hx hp (hM hn)).2.2.1,
      (rawCandidate_elimination_properties hξ hξ1 hx hp (hM hn)).2.2.2.1⟩
  · intro n hn
    exact (rawCandidate_elimination_properties hξ hξ1 hx hp (hM hn)).2.2.2.2

end

end Erdos308.Candidates

#print axioms Erdos308.Candidates.rawCandidates_card
#print axioms Erdos308.Candidates.primePower_dvd_lcm_candidateFamily_lt
