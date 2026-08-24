/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos360.LowerSieveSet

/-!
# The target-prime loss in the structured lower sieve

The quotients rejected by `targetCoprimeDyadicQuotients` have two genuinely
different sources.  A prime divisor of the target at most the sieve cutoff
is part of the ordinary (unfiltered) small-prime sieve.  A prime divisor
above the cutoff is an elementary union-bound error.  Keeping these two
sources separate is essential: the whole bad set is not a small error when,
for example, the target is even.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The dyadic interval sifted by *all* primes up to `r`, including the
target primes omitted from `missingPrimeProduct`. -/
def allPrimeDyadicQuotients (r X : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun q ↦ Nat.Coprime q (primorial r)

@[simp] lemma mem_allPrimeDyadicQuotients {r X q : ℕ} :
    q ∈ allPrimeDyadicQuotients r X ↔
      X < q ∧ q ≤ 2 * X ∧ Nat.Coprime q (primorial r) := by
  simp [allPrimeDyadicQuotients, and_assoc]

/-- The same dyadic interval sifted only by odd primes at most `r`.  This is
the exact candidate set to which the existing one-shift beta sieve applies
with lower endpoint `2`. -/
def oddPrimeDyadicQuotients (r X : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun q ↦
    Nat.Coprime q (Erdos387.sievePrimeProduct 2 (r + 1))

@[simp] lemma mem_oddPrimeDyadicQuotients {r X q : ℕ} :
    q ∈ oddPrimeDyadicQuotients r X ↔
      X < q ∧ q ≤ 2 * X ∧
        Nat.Coprime q (Erdos387.sievePrimeProduct 2 (r + 1)) := by
  simp [oddPrimeDyadicQuotients, and_assoc]

lemma oddPrimeDyadicQuotients_eq_siftedShiftCandidates (r X : ℕ) :
    oddPrimeDyadicQuotients r X =
      Erdos851.ShiftSieve.siftedShiftCandidates {0} X 2 (r + 1) := by
  ext q
  simp [oddPrimeDyadicQuotients,
    Erdos851.ShiftSieve.siftedShiftCandidates,
    Erdos851.ShiftSieve.shiftedProduct, Nat.coprime_comm]

/-- Even survivors of the odd-prime sieve.  Removing these enforces the
prime `2` which is intentionally absent from the library's beta sieve. -/
def evenOddPrimeDyadicQuotients (r X : ℕ) : Finset ℕ :=
  (oddPrimeDyadicQuotients r X).filter Even

@[simp] lemma mem_evenOddPrimeDyadicQuotients {r X q : ℕ} :
    q ∈ evenOddPrimeDyadicQuotients r X ↔
      q ∈ oddPrimeDyadicQuotients r X ∧ Even q := by
  simp [evenOddPrimeDyadicQuotients]

lemma coprime_primorial_of_oddPrime_of_not_even
    {r q : ℕ} (hqOddSieve :
      Nat.Coprime q (Erdos387.sievePrimeProduct 2 (r + 1)))
    (hqNotEven : ¬Even q) : Nat.Coprime q (primorial r) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  obtain ⟨p, hpprime, hpgcd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpq : p ∣ q := hpgcd.trans (Nat.gcd_dvd_left q (primorial r))
  have hpPrimorial : p ∣ primorial r :=
    hpgcd.trans (Nat.gcd_dvd_right q (primorial r))
  have hpr : p ≤ r := hpprime.dvd_primorial_iff.mp hpPrimorial
  by_cases hp2 : p = 2
  · subst p
    exact hqNotEven (even_iff_two_dvd.mpr hpq)
  · have hp2le : 2 ≤ p := hpprime.two_le
    have hpgt2 : 2 < p := by omega
    have hpSieve : p ∈ Erdos387.sievePrimes 2 (r + 1) :=
      Erdos387.mem_sievePrimes.mpr ⟨hpprime, hpgt2, by omega⟩
    have hpProd : p ∣ Erdos387.sievePrimeProduct 2 (r + 1) := by
      unfold Erdos387.sievePrimeProduct
      exact Finset.dvd_prod_of_mem id hpSieve
    have hpCop : Nat.Coprime p
        (Erdos387.sievePrimeProduct 2 (r + 1)) :=
      Nat.Coprime.of_dvd_left hpq hqOddSieve
    exact hpprime.ne_one (hpCop.eq_one_of_dvd hpProd)

lemma oddPrimeDyadicQuotients_subset_allPrime_union_even (r X : ℕ) :
    oddPrimeDyadicQuotients r X ⊆
      allPrimeDyadicQuotients r X ∪
        evenOddPrimeDyadicQuotients r X := by
  intro q hq
  obtain ⟨hXq, hq2X, hqOddSieve⟩ :=
    mem_oddPrimeDyadicQuotients.mp hq
  by_cases hqEven : Even q
  · exact Finset.mem_union_right _
      (mem_evenOddPrimeDyadicQuotients.mpr ⟨hq, hqEven⟩)
  · exact Finset.mem_union_left _
      (mem_allPrimeDyadicQuotients.mpr
        ⟨hXq, hq2X,
          coprime_primorial_of_oddPrime_of_not_even hqOddSieve hqEven⟩)

/-- Division by two maps all even odd-prime survivors into the half-scale
dyadic interval, except for the single possible endpoint `X` when `X` is
odd. -/
lemma evenOddPrimeDyadicQuotients_card_le_half_add_one (r X : ℕ) :
    (evenOddPrimeDyadicQuotients r X).card ≤
      (oddPrimeDyadicQuotients r (X / 2)).card + 1 := by
  let F := (evenOddPrimeDyadicQuotients r X).image fun q ↦ q / 2
  have hcard : (evenOddPrimeDyadicQuotients r X).card = F.card := by
    symm
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have haEven := (mem_evenOddPrimeDyadicQuotients.mp ha).2
    have hbEven := (mem_evenOddPrimeDyadicQuotients.mp hb).2
    change a / 2 = b / 2 at hab
    calc
      a = 2 * (a / 2) := (Nat.two_mul_div_two_of_even haEven).symm
      _ = 2 * (b / 2) := congrArg (2 * ·) hab
      _ = b := Nat.two_mul_div_two_of_even hbEven
  have hsub : F ⊆ oddPrimeDyadicQuotients r (X / 2) ∪ {X} := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hqOdd, hqEven⟩ :=
      mem_evenOddPrimeDyadicQuotients.mp hq
    obtain ⟨hXq, hq2X, hqCop⟩ :=
      mem_oddPrimeDyadicQuotients.mp hqOdd
    have hqeq : q = 2 * (q / 2) :=
      (Nat.two_mul_div_two_of_even hqEven).symm
    have hkLower : X / 2 < q / 2 := by omega
    have hkUpper : q / 2 ≤ X := by omega
    have hkCop : Nat.Coprime (q / 2)
        (Erdos387.sievePrimeProduct 2 (r + 1)) := by
      apply Nat.Coprime.of_dvd_left
        (Nat.div_dvd_of_dvd hqEven.two_dvd)
      exact hqCop
    by_cases hkDyadic : q / 2 ≤ 2 * (X / 2)
    · exact Finset.mem_union_left _
        (mem_oddPrimeDyadicQuotients.mpr
          ⟨hkLower, hkDyadic, hkCop⟩)
    · exact Finset.mem_union_right _ (by
        simp only [Finset.mem_singleton]
        omega)
  rw [hcard]
  calc
    F.card ≤ (oddPrimeDyadicQuotients r (X / 2) ∪ {X}).card :=
      Finset.card_le_card hsub
    _ ≤ (oddPrimeDyadicQuotients r (X / 2)).card + ({X} : Finset ℕ).card :=
      Finset.card_union_le _ _
    _ = (oddPrimeDyadicQuotients r (X / 2)).card + 1 := by simp

/-- Purely finite parity bridge from the library's odd-prime sieve to the
complete primorial sieve. -/
theorem oddPrime_card_le_allPrime_add_half_add_one (r X : ℕ) :
    (oddPrimeDyadicQuotients r X).card ≤
      (allPrimeDyadicQuotients r X).card +
        (oddPrimeDyadicQuotients r (X / 2)).card + 1 := by
  have hsub := Finset.card_le_card
    (oddPrimeDyadicQuotients_subset_allPrime_union_even r X)
  have hunion := Finset.card_union_le
    (allPrimeDyadicQuotients r X)
    (evenOddPrimeDyadicQuotients r X)
  have heven := evenOddPrimeDyadicQuotients_card_le_half_add_one r X
  omega

/-- End-to-end beta-sieve lower bound for the complete-prime dyadic set.
The factor `1/2` is obtained without a new sieve theorem: apply the existing
odd-prime beta sieve at scales `X` and `X/2`, then remove the even survivors
using `oddPrime_card_le_allPrime_add_half_add_one`. -/
theorem exists_allPrimeDyadicQuotients_card_lower_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ r X S : ℕ, 2 ≤ r → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := Erdos851.localEulerProduct
          Erdos851.oneShiftDensity 2 r
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := r ^ S
        (X : ℝ) * ((1 - eta) * V) - (D : ℝ) ^ 2 -
            (((X / 2 : ℕ) : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2) - 1 ≤
          ((allPrimeDyadicQuotients r X).card : ℝ) := by
  obtain ⟨A, hA, hbeta⟩ :=
    Erdos851.exists_oneShift_concrete_cardinality_bounds
  refine ⟨A, hA, ?_⟩
  intro r X S hr hS hlog
  dsimp only
  have hfull := hbeta 0 X 2 r S (by omega) (by norm_num) hr
    (by omega) hS hlog
  have hhalf := hbeta 0 (X / 2) 2 r S (by omega) (by norm_num) hr
    (by omega) hS hlog
  dsimp only at hfull hhalf
  rw [← oddPrimeDyadicQuotients_eq_siftedShiftCandidates] at hfull hhalf
  have hcardNat := oddPrime_card_le_allPrime_add_half_add_one r X
  have hcard : ((oddPrimeDyadicQuotients r X).card : ℝ) ≤
      ((allPrimeDyadicQuotients r X).card : ℝ) +
        ((oddPrimeDyadicQuotients r (X / 2)).card : ℝ) + 1 := by
    exact_mod_cast hcardNat
  linarith [hfull.1, hhalf.2]

/-- Quotients in the dyadic interval which have a target-prime divisor
strictly above the small-prime cutoff. -/
def largeTargetPrimeBadQuotients (n r X : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun q ↦
    ∃ p ∈ n.primeFactors, r < p ∧ p ∣ q

@[simp] lemma mem_largeTargetPrimeBadQuotients {n r X q : ℕ} :
    q ∈ largeTargetPrimeBadQuotients n r X ↔
      X < q ∧ q ≤ 2 * X ∧
        ∃ p ∈ n.primeFactors, r < p ∧ p ∣ q := by
  simp [largeTargetPrimeBadQuotients, and_assoc]

/-- A quotient which survives the complete small-prime sieve and has no
large target-prime divisor is coprime to the target. -/
lemma coprime_target_of_allPrime_of_not_large
    {n r q : ℕ} (hn : n ≠ 0)
    (hall : Nat.Coprime q (primorial r))
    (hlarge : ¬ ∃ p ∈ n.primeFactors, r < p ∧ p ∣ q) :
    Nat.Coprime q n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  obtain ⟨p, hpprime, hpgcd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpq : p ∣ q := hpgcd.trans (Nat.gcd_dvd_left q n)
  have hpn : p ∣ n := hpgcd.trans (Nat.gcd_dvd_right q n)
  have hpmem : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hpn, hn⟩
  by_cases hpr : p ≤ r
  · have hpPrimorial : p ∣ primorial r := hpprime.dvd_primorial_iff.mpr hpr
    have hpCop : Nat.Coprime p (primorial r) :=
      Nat.Coprime.of_dvd_left hpq hall
    exact hpprime.ne_one (hpCop.eq_one_of_dvd hpPrimorial)
  · exact hlarge ⟨p, hpmem, Nat.lt_of_not_ge hpr, hpq⟩

/-- Every completely small-prime-sifted quotient is either genuinely
target-coprime or belongs to the large-target-prime tail. -/
lemma allPrimeDyadicQuotients_subset_targetCoprime_union_large
    (n r X : ℕ) (hn : n ≠ 0) :
    allPrimeDyadicQuotients r X ⊆
      targetCoprimeDyadicQuotients n r X ∪
        largeTargetPrimeBadQuotients n r X := by
  intro q hq
  obtain ⟨hXq, hq2X, hqPrimorial⟩ :=
    mem_allPrimeDyadicQuotients.mp hq
  by_cases hlarge : ∃ p ∈ n.primeFactors, r < p ∧ p ∣ q
  · exact Finset.mem_union_right _
      (mem_largeTargetPrimeBadQuotients.mpr
        ⟨hXq, hq2X, hlarge⟩)
  · apply Finset.mem_union_left
    apply mem_targetCoprimeDyadicQuotients.mpr
    refine ⟨hXq, hq2X, ?_,
      coprime_target_of_allPrime_of_not_large hn hqPrimorial hlarge⟩
    exact Nat.Coprime.of_dvd_right
      (missingPrimeProduct_dvd_primorial n r) hqPrimorial

/-- Sharp finite accounting identity for the target-prime loss.  The part
caused by target primes at most `r` is exactly paid for by replacing the
filtered small-prime sieve with the complete one; only target primes above
`r` remain as an additive error. -/
theorem targetPrimeBadQuotients_card_add_allPrime_le
    (n r X : ℕ) (hn : n ≠ 0) :
    (targetPrimeBadQuotients n r X).card +
        (allPrimeDyadicQuotients r X).card ≤
      (relaxedDyadicQuotients n r X).card +
        (largeTargetPrimeBadQuotients n r X).card := by
  have hall := Finset.card_le_card
    (allPrimeDyadicQuotients_subset_targetCoprime_union_large n r X hn)
  have hunion := Finset.card_union_le
    (targetCoprimeDyadicQuotients n r X)
    (largeTargetPrimeBadQuotients n r X)
  have hsmall : (allPrimeDyadicQuotients r X).card ≤
      (targetCoprimeDyadicQuotients n r X).card +
        (largeTargetPrimeBadQuotients n r X).card :=
    hall.trans hunion
  have hpartition := targetCoprime_card_add_bad_card n r X
  omega

/-- Equivalent lower-bound interface: the complete small-prime sieve, minus
only the large-target-prime tail, injects into the exact target-coprime
quotient count.  This is the form used in the divisor sum. -/
theorem allPrime_card_sub_large_le_targetCoprime
    (n r X : ℕ) (hn : n ≠ 0) :
    ((allPrimeDyadicQuotients r X).card : ℝ) -
        ((largeTargetPrimeBadQuotients n r X).card : ℝ) ≤
      ((targetCoprimeDyadicQuotients n r X).card : ℝ) := by
  have hall := Finset.card_le_card
    (allPrimeDyadicQuotients_subset_targetCoprime_union_large n r X hn)
  have hunion := Finset.card_union_le
    (targetCoprimeDyadicQuotients n r X)
    (largeTargetPrimeBadQuotients n r X)
  have hnat : (allPrimeDyadicQuotients r X).card ≤
      (targetCoprimeDyadicQuotients n r X).card +
        (largeTargetPrimeBadQuotients n r X).card := hall.trans hunion
  have hreal : ((allPrimeDyadicQuotients r X).card : ℝ) ≤
      ((targetCoprimeDyadicQuotients n r X).card : ℝ) +
        ((largeTargetPrimeBadQuotients n r X).card : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Prime divisors of the target above the small-prime cutoff. -/
def largeTargetPrimeDivisors (n r : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p ↦ r < p

@[simp] lemma mem_largeTargetPrimeDivisors {n r p : ℕ} :
    p ∈ largeTargetPrimeDivisors n r ↔
      p ∈ n.primeFactors ∧ r < p := by
  simp [largeTargetPrimeDivisors]

/-- Multiples of one prime in the ambient dyadic interval. -/
def primeMultiplesInDyadic (p X : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun q ↦ p ∣ q

@[simp] lemma mem_primeMultiplesInDyadic {p X q : ℕ} :
    q ∈ primeMultiplesInDyadic p X ↔
      X < q ∧ q ≤ 2 * X ∧ p ∣ q := by
  simp [primeMultiplesInDyadic, and_assoc]

lemma largeTargetPrimeBadQuotients_eq_biUnion (n r X : ℕ) :
    largeTargetPrimeBadQuotients n r X =
      (largeTargetPrimeDivisors n r).biUnion fun p ↦
        primeMultiplesInDyadic p X := by
  ext q
  simp only [mem_largeTargetPrimeBadQuotients, Finset.mem_biUnion,
    mem_largeTargetPrimeDivisors, mem_primeMultiplesInDyadic]
  aesop

/-- Multiples of a positive integer in `(X,2X]` inject by division into
`(0,⌊2X/p⌋]`. -/
lemma card_primeMultiplesInDyadic_le (p X : ℕ) (hp : 0 < p) :
    (primeMultiplesInDyadic p X).card ≤ (2 * X) / p := by
  let F := (primeMultiplesInDyadic p X).image fun q ↦ q / p
  have hcard : (primeMultiplesInDyadic p X).card = F.card := by
    symm
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have hpa := (mem_primeMultiplesInDyadic.mp ha).2.2
    have hpb := (mem_primeMultiplesInDyadic.mp hb).2.2
    change a / p = b / p at hab
    calc
      a = p * (a / p) := (Nat.mul_div_cancel' hpa).symm
      _ = p * (b / p) := congrArg (p * ·) hab
      _ = b := Nat.mul_div_cancel' hpb
  have hsub : F ⊆ Finset.Ioc 0 ((2 * X) / p) := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hXq, hq2X, hpq⟩ := mem_primeMultiplesInDyadic.mp hq
    apply Finset.mem_Ioc.mpr
    have hqpos : 0 < q := by omega
    have hpqle : p ≤ q := Nat.le_of_dvd hqpos hpq
    refine ⟨Nat.div_pos hpqle hp, Nat.div_le_div_right hq2X⟩
  rw [hcard]
  exact (Finset.card_le_card hsub).trans (by simp)

/-- Union bound with the optimal elementary `⌊2X/p⌋` contribution for
each target prime above `r`. -/
theorem largeTargetPrimeBadQuotients_card_le_sum (n r X : ℕ) :
    (largeTargetPrimeBadQuotients n r X).card ≤
      ∑ p ∈ largeTargetPrimeDivisors n r, (2 * X) / p := by
  rw [largeTargetPrimeBadQuotients_eq_biUnion]
  refine (Finset.card_biUnion_le).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  exact card_primeMultiplesInDyadic_le p X
    (Nat.prime_of_mem_primeFactors
      (mem_largeTargetPrimeDivisors.mp hp).1).pos

/-- Coarser cutoff-only version of the large-prime tail estimate. -/
theorem largeTargetPrimeBadQuotients_card_le (n r X : ℕ) :
    (largeTargetPrimeBadQuotients n r X).card ≤
      n.primeFactors.card * ((2 * X) / (r + 1)) := by
  calc
    (largeTargetPrimeBadQuotients n r X).card ≤
        ∑ p ∈ largeTargetPrimeDivisors n r, (2 * X) / p :=
      largeTargetPrimeBadQuotients_card_le_sum n r X
    _ ≤ ∑ _p ∈ largeTargetPrimeDivisors n r,
          (2 * X) / (r + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.div_le_div_left
        (by simpa using (mem_largeTargetPrimeDivisors.mp hp).2)
        (by omega)
    _ = (largeTargetPrimeDivisors n r).card *
          ((2 * X) / (r + 1)) := by simp
    _ ≤ n.primeFactors.card * ((2 * X) / (r + 1)) := by
      exact Nat.mul_le_mul_right _
        (Finset.card_le_card (Finset.filter_subset _ _))

/-- Explicit real-valued upper bound on the bad set, directly compatible
with the subtraction in `exists_targetCoprimeDyadicQuotients_card_lower_bound`.
The complete-sieve cardinal is deliberately retained: its beta-sieve lower
bound cancels the large filtered main term with the correct local factors. -/
theorem targetPrimeBadQuotients_cast_le
    (n r X : ℕ) (hn : n ≠ 0) :
    ((targetPrimeBadQuotients n r X).card : ℝ) ≤
      ((relaxedDyadicQuotients n r X).card : ℝ) -
        ((allPrimeDyadicQuotients r X).card : ℝ) +
          ((n.primeFactors.card * ((2 * X) / (r + 1)) : ℕ) : ℝ) := by
  have haccount := targetPrimeBadQuotients_card_add_allPrime_le n r X hn
  have htail := largeTargetPrimeBadQuotients_card_le n r X
  have hnat : (targetPrimeBadQuotients n r X).card +
      (allPrimeDyadicQuotients r X).card ≤
        (relaxedDyadicQuotients n r X).card +
          n.primeFactors.card * ((2 * X) / (r + 1)) :=
    haccount.trans (Nat.add_le_add_left htail _)
  have hreal : ((targetPrimeBadQuotients n r X).card : ℝ) +
      ((allPrimeDyadicQuotients r X).card : ℝ) ≤
        ((relaxedDyadicQuotients n r X).card : ℝ) +
          ((n.primeFactors.card * ((2 * X) / (r + 1)) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Divisor-summed lower bound after the sharp target-prime accounting.
Unlike a direct union bound over every prime dividing the target, this has
the correct CFP main term: small target primes are absorbed by the complete
small-prime sieve, and only primes above `r` contribute an error. -/
theorem structuredTestSet_card_lower_bound_via_allPrime
    (n r y U : ℕ) (hn : n ≠ 0) :
    (∑ u ∈ boundedTargetDivisors n U,
      (((allPrimeDyadicQuotients r (y / u)).card : ℝ) -
        ((n.primeFactors.card *
          ((2 * (y / u)) / (r + 1)) : ℕ) : ℝ))) ≤
      ((structuredTestSet n r y U).card : ℝ) := by
  rw [card_structuredTestSet]
  norm_num only [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro u hu
  calc
    ((allPrimeDyadicQuotients r (y / u)).card : ℝ) -
          ((n.primeFactors.card *
            ((2 * (y / u)) / (r + 1)) : ℕ) : ℝ) ≤
        ((allPrimeDyadicQuotients r (y / u)).card : ℝ) -
          ((largeTargetPrimeBadQuotients n r (y / u)).card : ℝ) := by
      have htail := largeTargetPrimeBadQuotients_card_le n r (y / u)
      exact sub_le_sub_left (by exact_mod_cast htail) _
    _ ≤ ((targetCoprimeDyadicQuotients n r (y / u)).card : ℝ) :=
      allPrime_card_sub_large_le_targetCoprime n r (y / u) hn

/-- Fully explicit divisor-summed CFP lower-sieve interface.  The main term
is one half of the ordinary complete-prime Euler product (up to the
arbitrarily small beta-sieve relative error); the only target-dependent
error is the elementary large-prime tail. -/
theorem exists_structuredTestSet_completeSieve_card_lower_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ n r y U S : ℕ, n ≠ 0 → 2 ≤ r → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := Erdos851.localEulerProduct
          Erdos851.oneShiftDensity 2 r
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := r ^ S
        (∑ u ∈ boundedTargetDivisors n U,
          (((y / u : ℕ) : ℝ) * ((1 - eta) * V) - (D : ℝ) ^ 2 -
            ((((y / u) / 2 : ℕ) : ℝ) * ((1 + eta) * V) +
              (D : ℝ) ^ 2) - 1 -
            ((n.primeFactors.card *
              ((2 * (y / u)) / (r + 1)) : ℕ) : ℝ))) ≤
          ((structuredTestSet n r y U).card : ℝ) := by
  obtain ⟨A, hA, hallPrime⟩ :=
    exists_allPrimeDyadicQuotients_card_lower_bound
  refine ⟨A, hA, ?_⟩
  intro n r y U S hn hr hS hlog
  dsimp only
  refine (Finset.sum_le_sum (fun u hu ↦ ?_)).trans
    (structuredTestSet_card_lower_bound_via_allPrime n r y U hn)
  have huAll := hallPrime r (y / u) S hr hS hlog
  dsimp only at huAll
  linarith

end Erdos360
