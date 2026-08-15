/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.NumberTheory.SelbergSieve

/-!
# Lower-bound sieve infrastructure for Erdős problem 387

Mathlib's `SelbergSieve` file supplies the upper-bound half of the abstract
sieve but does not define lower Möbius weights.  This file proves the exact
dual inequality.  It also records the elementary Bonferroni calculation
behind the odd Brun truncation.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega
open scoped ArithmeticFunction.omega

open Finset Real Nat ArithmeticFunction

namespace BoundingSieve

variable {s : BoundingSieve}

/-- A lower Möbius weight has divisor sum at most the indicator of `1`. -/
def IsLowerMoebius (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, muMinus d ≤ if n = 1 then 1 else 0

/-- It is enough to verify the lower-Möbius inequality on divisors of the
sieve's squarefree prime product. -/
def IsLowerMoebiusOnProdPrimes (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∣ s.prodPrimes →
    ∑ d ∈ n.divisors, muMinus d ≤ if n = 1 then 1 else 0

/-- Localized upper Möbius weights.  As for lower weights, the abstract
sieve only ever evaluates the divisor sum on divisors of its squarefree
prime product. -/
def IsUpperMoebiusOnProdPrimes (muPlus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∣ s.prodPrimes →
    (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d

theorem IsLowerMoebius.onProdPrimes {muMinus : ℕ → ℝ}
    (h : IsLowerMoebius muMinus) : s.IsLowerMoebiusOnProdPrimes muMinus :=
  fun n _ => h n

theorem IsUpperMoebius.onProdPrimes {muPlus : ℕ → ℝ}
    (h : IsUpperMoebius muPlus) : s.IsUpperMoebiusOnProdPrimes muPlus :=
  fun n _ => h n

/-- Every lower Möbius weight gives a lower bound for the sifted sum. -/
theorem sum_le_siftedSum_of_lowerMoebius (muMinus : ℕ → ℝ)
    (h : s.IsLowerMoebiusOnProdPrimes muMinus) :
    (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) ≤ s.siftedSum := by
  have hrearrange :
      (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) =
        ∑ n ∈ s.support,
          s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muMinus d := by
    calc
      (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) =
          ∑ n ∈ s.support, ∑ d ∈ divisors s.prodPrimes,
            if d ∣ n then s.weights n * muMinus d else 0 := by
        rw [sum_comm]
        simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]
      _ = ∑ n ∈ s.support,
          s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muMinus d := by
        apply sum_congr rfl
        intro n _
        rw [mul_sum, ← sum_filter]
        congr 1
        rw [← divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero
          (Nat.gcd_dvd_left _ _)]
        ext d
        simp +contextual [dvd_gcd_iff]
  rw [hrearrange, siftedSum_eq_sum_support_mul_ite]
  apply sum_le_sum
  intro n hn
  gcongr
  exact h (Nat.gcd s.prodPrimes n) (Nat.gcd_dvd_left _ _)

/-- Main-term/error-term form of the abstract lower-bound sieve. -/
theorem totalMass_mainSum_sub_errSum_le_siftedSum
    (muMinus : ℕ → ℝ) (h : s.IsLowerMoebiusOnProdPrimes muMinus) :
    s.totalMass * s.mainSum muMinus - s.errSum muMinus ≤ s.siftedSum := by
  have hidentity :
      (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) =
        s.totalMass * s.mainSum muMinus +
          ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
    rw [mainSum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro d _
    rw [multSum_eq_main_err]
    ring
  have herror :
      -s.errSum muMinus ≤
        ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
    rw [errSum, ← Finset.sum_neg_distrib]
    apply sum_le_sum
    intro d hd
    rw [← abs_mul]
    exact neg_abs_le (muMinus d * s.rem d)
  have hlower := sum_le_siftedSum_of_lowerMoebius (s := s) muMinus h
  rw [hidentity] at hlower
  linarith

/-- Every localized upper Möbius weight gives an upper bound for the sifted
sum. -/
theorem siftedSum_le_sum_of_upperMoebiusOnProdPrimes
    (muPlus : ℕ → ℝ) (h : s.IsUpperMoebiusOnProdPrimes muPlus) :
    s.siftedSum ≤
      ∑ d ∈ divisors s.prodPrimes, muPlus d * s.multSum d := by
  calc
    s.siftedSum ≤
        ∑ n ∈ s.support,
          s.weights n *
            ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muPlus d := by
      rw [s.siftedSum_eq_sum_support_mul_ite]
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact h (Nat.gcd s.prodPrimes n) (Nat.gcd_dvd_left _ _)
    _ = ∑ n ∈ s.support, ∑ d ∈ divisors s.prodPrimes,
          if d ∣ n then s.weights n * muPlus d else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mul_sum, ← Finset.sum_filter]
      congr 1
      rw [← divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero
        (Nat.gcd_dvd_left _ _)]
      ext d
      simp +contextual [dvd_gcd_iff]
    _ = ∑ d ∈ divisors s.prodPrimes, muPlus d * s.multSum d := by
      rw [Finset.sum_comm]
      simp_rw [BoundingSieve.multSum, ← Finset.sum_filter, mul_sum,
        mul_comm]

/-- Main-term/error-term form of the localized abstract upper-bound sieve. -/
theorem siftedSum_le_totalMass_mainSum_add_errSum
    (muPlus : ℕ → ℝ) (h : s.IsUpperMoebiusOnProdPrimes muPlus) :
    s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus := by
  calc
    s.siftedSum ≤
        ∑ d ∈ divisors s.prodPrimes, muPlus d * s.multSum d :=
      s.siftedSum_le_sum_of_upperMoebiusOnProdPrimes muPlus h
    _ = s.totalMass * s.mainSum muPlus +
          ∑ d ∈ divisors s.prodPrimes, muPlus d * s.rem d := by
      rw [BoundingSieve.mainSum, mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      rw [s.multSum_eq_main_err]
      ring
    _ ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus := by
      rw [BoundingSieve.errSum]
      gcongr _ + ∑ d ∈ _, ?_ with d
      rw [← abs_mul]
      exact le_abs_self (muPlus d * s.rem d)

end BoundingSieve

namespace Erdos387

open scoped BigOperators

/-- The number of distinct prime factors is the cardinality of the natural
prime-factor finset. -/
theorem cardDistinctFactors_eq_primeFactors_card (n : ℕ) :
    ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply]
  exact (List.card_toFinset n.primeFactorsList).symm

/-- Divisors of a squarefree number are exactly products of subsets of its
prime factors. -/
theorem divisors_eq_image_prod_primeFactorSubsets {q : ℕ} (hq : Squarefree q) :
    q.divisors = q.primeFactors.powerset.image
      (fun T : Finset ℕ => ∏ p ∈ T, p) := by
  classical
  ext d
  constructor
  · intro hd
    have hd' := Nat.mem_divisors.mp hd
    rw [Finset.mem_image]
    refine ⟨d.primeFactors, Finset.mem_powerset.mpr
      (Nat.primeFactors_mono hd'.1 hq.ne_zero), ?_⟩
    exact Nat.prod_primeFactors_of_squarefree
      (hq.squarefree_of_dvd hd'.1)
  · intro hd
    rw [Finset.mem_image] at hd
    obtain ⟨T, hT, rfl⟩ := hd
    rw [Nat.mem_divisors]
    refine ⟨?_, hq.ne_zero⟩
    calc
      ∏ p ∈ T, p ∣ ∏ p ∈ q.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ _
          (Finset.mem_powerset.mp hT)
      _ = q := Nat.prod_primeFactors_of_squarefree hq

/-- Products of two subsets of a fixed prime-factor set agree only when the
subsets agree. -/
theorem prod_primeFactorSubsets_injOn (q : ℕ) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p)
      (q.primeFactors.powerset : Set (Finset ℕ)) := by
  classical
  intro A hA B hB hab
  have hprimeA : ∀ p ∈ A, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_powerset.mp hA hp)
  have hprimeB : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_powerset.mp hB hp)
  have hpfA := Nat.primeFactors_prod hprimeA
  have hpfB := Nat.primeFactors_prod hprimeB
  exact hpfA.symm.trans ((congrArg Nat.primeFactors hab).trans hpfB)

/-- A product of a subset of prime factors is squarefree, and its distinct
prime-factor count is the size of the subset. -/
theorem prod_primeFactorSubset_squarefree_card {q : ℕ}
    {T : Finset ℕ} (hT : T ∈ q.primeFactors.powerset) :
    Squarefree (∏ p ∈ T, p) ∧ ω (∏ p ∈ T, p) = T.card := by
  have hprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_powerset.mp hT hp)
  have hpf := Nat.primeFactors_prod hprime
  constructor
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp r hr hne
      change IsRelPrime p r
      rw [← Nat.coprime_iff_isRelPrime]
      exact (coprime_primes (hprime p hp) (hprime r hr)).mpr hne
    · intro p hp
      exact (hprime p hp).squarefree
  · rw [cardDistinctFactors_eq_primeFactors_card, hpf]

/-- The alternating binomial sum obtained by truncating inclusion--exclusion
after level `L`. -/
def brunTruncation (L m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (L + 1), (-1 : ℤ) ^ j * m.choose j

/-- Grouping the subset expansion by cardinality gives the same truncated
alternating binomial sum, even when `L` exceeds `m`. -/
theorem sum_range_choose_ite_eq_brunTruncation (L m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℤ) * if j ≤ L then (-1 : ℤ) ^ j else 0) =
      brunTruncation L m := by
  classical
  by_cases hLm : L ≤ m
  · simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter :
        (Finset.range (m + 1)).filter (fun j => j ≤ L) =
          Finset.range (L + 1) := by
      ext j
      simp
      omega
    rw [hfilter, brunTruncation]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · have hmL : m < L := Nat.lt_of_not_ge hLm
    have hleft :
        (∑ j ∈ Finset.range (m + 1),
            (m.choose j : ℤ) * if j ≤ L then (-1 : ℤ) ^ j else 0) =
          ∑ j ∈ Finset.range (m + 1),
            (-1 : ℤ) ^ j * m.choose j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos]
      · ring
      · have hjm : j ≤ m := by simpa using (Finset.mem_range.mp hj)
        exact hjm.trans hmL.le
    rw [hleft, brunTruncation]
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmL.le))
    intro j hjL hjm
    have hmj : m < j := by
      have : m + 1 ≤ j := by
        simpa only [Finset.mem_range, Nat.not_lt] using hjm
      omega
    rw [Nat.choose_eq_zero_of_lt hmj]
    simp

/-- The truncated Möbius divisor sum of a squarefree number is exactly its
odd/even Brun binomial truncation. -/
theorem truncated_moebius_divisorSum_eq_brunTruncation
    {q L : ℕ} (hq : Squarefree q) :
    (∑ d ∈ q.divisors,
        if ω d ≤ L then (μ d : ℤ) else 0) =
      brunTruncation L q.primeFactors.card := by
  classical
  rw [divisors_eq_image_prod_primeFactorSubsets hq,
    Finset.sum_image (prod_primeFactorSubsets_injOn q)]
  have hterms :
      (∑ T ∈ q.primeFactors.powerset,
          if ω (∏ p ∈ T, p) ≤ L then (μ (∏ p ∈ T, p) : ℤ) else 0) =
        ∑ T ∈ q.primeFactors.powerset,
          if T.card ≤ L then (-1 : ℤ) ^ T.card else 0 := by
    apply Finset.sum_congr rfl
    intro T hT
    obtain ⟨hSq, hcard⟩ := prod_primeFactorSubset_squarefree_card hT
    have hOmega : Ω (∏ p ∈ T, p) = T.card := by
      calc
        Ω (∏ p ∈ T, p) = ω (∏ p ∈ T, p) :=
          ((ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
            hSq.ne_zero).mpr hSq).symm
        _ = T.card := hcard
    rw [hcard, ArithmeticFunction.moebius_apply_of_squarefree hSq, hOmega]
  rw [hterms]
  have hgroup := Finset.sum_powerset_apply_card
    (x := q.primeFactors)
    (f := fun j => if j ≤ L then (-1 : ℤ) ^ j else 0)
  rw [hgroup]
  simp only [nsmul_eq_mul']
  simpa [mul_comm] using
    sum_range_choose_ite_eq_brunTruncation L q.primeFactors.card

/-- For a nonempty family of bad events, the odd Brun truncation is
nonpositive.  This is the numerical Bonferroni inequality. -/
theorem brunTruncation_nonpos_of_odd {L m : ℕ}
    (hL : Odd L) (hm : 0 < m) : brunTruncation L m ≤ 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [brunTruncation, Int.alternating_sum_range_choose_eq_choose,
    hL.neg_one_pow]
  simp

/-- The even Bonferroni truncation is nonnegative. -/
theorem brunTruncation_nonneg_of_even {L m : ℕ}
    (hL : Even L) : 0 ≤ brunTruncation L m := by
  by_cases hm : m = 0
  · subst m
    rw [brunTruncation, Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0)]
      simp
    · simp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [brunTruncation, Int.alternating_sum_range_choose_eq_choose,
    hL.neg_one_pow]
  simp

/-- With no bad event, every Brun truncation equals one. -/
@[simp] theorem brunTruncation_zero (L : ℕ) : brunTruncation L 0 = 1 := by
  rw [brunTruncation, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0)]
    simp
  · simp

/-- Pointwise lower-bound form: an odd Brun truncation is bounded above by
the indicator that no bad event occurs. -/
theorem brunTruncation_le_zeroIndicator {L m : ℕ} (hL : Odd L) :
    brunTruncation L m ≤ if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [if_neg hm]
    exact brunTruncation_nonpos_of_odd hL (Nat.pos_of_ne_zero hm)

/-- Pointwise upper-bound form of the even Bonferroni inequality. -/
theorem zeroIndicator_le_brunTruncation {L m : ℕ} (hL : Even L) :
    (if m = 0 then 1 else 0) ≤ brunTruncation L m := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [if_neg hm]
    exact brunTruncation_nonneg_of_even hL

/-- The standard Brun lower weight: retain the Möbius function only through
`L` distinct prime factors. -/
def brunLowerWeight (L d : ℕ) : ℝ :=
  if ω d ≤ L then (μ d : ℝ) else 0

/-- The standard even Brun upper weight. -/
def brunUpperWeight (L d : ℕ) : ℝ :=
  if ω d ≤ L then (μ d : ℝ) else 0

/-- Odd Brun weights satisfy the lower-Möbius inequality on every divisor of
the squarefree prime product in an abstract sieve. -/
theorem brunLowerWeight_isLowerOnProdPrimes
    (s : BoundingSieve) {L : ℕ} (hL : Odd L) :
    s.IsLowerMoebiusOnProdPrimes (brunLowerWeight L) := by
  intro n hnP
  have hnSq : Squarefree n := s.squarefree_of_dvd_prodPrimes hnP
  by_cases hn1 : n = 1
  · subst n
    simp [brunLowerWeight]
  rw [if_neg hn1]
  have hsumInt := truncated_moebius_divisorSum_eq_brunTruncation
    (L := L) hnSq
  have hsumReal :
      (∑ d ∈ n.divisors, brunLowerWeight L d) =
        (brunTruncation L n.primeFactors.card : ℝ) := by
    unfold brunLowerWeight
    exact_mod_cast hsumInt
  rw [hsumReal]
  have hnLarge : 1 < n := by
    have hn0 := hnSq.ne_zero
    omega
  have hcardPos : 0 < n.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hnLarge)
  exact_mod_cast brunTruncation_nonpos_of_odd hL hcardPos

/-- Even Brun weights satisfy the localized upper-Möbius inequality. -/
theorem brunUpperWeight_isUpperOnProdPrimes
    (s : BoundingSieve) {L : ℕ} (hL : Even L) :
    s.IsUpperMoebiusOnProdPrimes (brunUpperWeight L) := by
  intro n hnP
  have hnSq : Squarefree n := s.squarefree_of_dvd_prodPrimes hnP
  by_cases hn1 : n = 1
  · subst n
    simp [brunUpperWeight]
  rw [if_neg hn1]
  have hsumInt := truncated_moebius_divisorSum_eq_brunTruncation
    (L := L) hnSq
  have hsumReal :
      (∑ d ∈ n.divisors, brunUpperWeight L d) =
        (brunTruncation L n.primeFactors.card : ℝ) := by
    unfold brunUpperWeight
    exact_mod_cast hsumInt
  rw [hsumReal]
  have hnLarge : 1 < n := by
    have hn0 := hnSq.ne_zero
    omega
  have hcardPos : 0 < n.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hnLarge)
  exact_mod_cast brunTruncation_nonneg_of_even
    (m := n.primeFactors.card) hL

/-- Ready-to-use lower-bound Brun sieve inequality. -/
theorem brunLowerBound (s : BoundingSieve) {L : ℕ} (hL : Odd L) :
    s.totalMass * s.mainSum (brunLowerWeight L) -
        s.errSum (brunLowerWeight L) ≤ s.siftedSum :=
  s.totalMass_mainSum_sub_errSum_le_siftedSum
    (brunLowerWeight L) (brunLowerWeight_isLowerOnProdPrimes s hL)

/-- Ready-to-use upper-bound Brun sieve inequality. -/
theorem brunUpperBound (s : BoundingSieve) {L : ℕ} (hL : Even L) :
    s.siftedSum ≤
      s.totalMass * s.mainSum (brunUpperWeight L) +
        s.errSum (brunUpperWeight L) :=
  s.siftedSum_le_totalMass_mainSum_add_errSum
    (brunUpperWeight L) (brunUpperWeight_isUpperOnProdPrimes s hL)

end Erdos387
