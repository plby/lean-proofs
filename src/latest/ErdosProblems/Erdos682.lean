import Mathlib
import PrimeNumberTheoremAnd.Consequences
import Util.Density
import ErdosProblems.Erdos851.SieveSpecialization
import ErdosProblems.Erdos851.ConcreteBetaCardinality
import ErdosProblems.Erdos387.BrunMainTerm
import ErdosProblems.Erdos469

/-!
# Erdős Problem 682: rough numbers between consecutive primes

For the detailed mathematical proof and formalization plan, see `tex/682.tex`.

The prime sequence in this file is zero-indexed.  Thus `nthPrime 0 = 2`, and
`GoodGap n` is the literal assertion that the open interval between the `n`th
and `(n+1)`st primes contains an integer whose least prime factor is at least
the length of that prime gap.
-/

open Filter Set
open scoped Topology

namespace Erdos682

attribute [local instance] Classical.propDecidable

/-! ## Exact statement -/

/-- The `n`th prime, indexed from zero. -/
noncomputable abbrev nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- The length of the `n`th prime gap. -/
noncomputable abbrev gapLength (n : ℕ) : ℕ :=
  nthPrime (n + 1) - nthPrime n

/-- The `n`th prime gap contains a rough number in Erdős's sense. -/
def GoodGap (n : ℕ) : Prop :=
  ∃ m : ℕ,
    nthPrime n < m ∧ m < nthPrime (n + 1) ∧ gapLength n ≤ Nat.minFac m

/-- The `n`th prime gap is exceptional. -/
def ExceptionalGap (n : ℕ) : Prop :=
  ¬GoodGap n

/-- The set of good prime-gap indices. -/
def goodGapIndices : Set ℕ :=
  {n | GoodGap n}

/-- The set of exceptional prime-gap indices. -/
def exceptionalGapIndices : Set ℕ :=
  {n | ExceptionalGap n}

/-- Number of members of `S` among the first `N` natural numbers. -/
noncomputable def prefixCount (S : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (· ∈ S)).card

/-- Number of exceptional prime-gap indices below `N`. -/
noncomputable abbrev exceptionalPrefixCount (N : ℕ) : ℕ :=
  prefixCount exceptionalGapIndices N

/-- Number of members of `S` indexed by primes at most `X`. -/
noncomputable def primeScaleCount (S : Set ℕ) (X : ℕ) : ℕ :=
  prefixCount S (Nat.primeCounting X)

/-- Cumulative exceptional-gap count on the lower-prime scale. -/
noncomputable abbrev exceptionalPrimePrefixCount (X : ℕ) : ℕ :=
  primeScaleCount exceptionalGapIndices X

/-- Exceptional gaps whose lower prime lies in `[X, 2X]`.

The cutoff `n < 2 * X` loses nothing: the `n`th prime is at least `n + 2`.
-/
noncomputable def exceptionalDyadicGaps (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X)).filter fun n ↦
    X ≤ nthPrime n ∧ nthPrime n ≤ 2 * X ∧ ExceptionalGap n

/-- Number of exceptional gaps whose lower prime lies in `[X,2X]`. -/
noncomputable abbrev exceptionalDyadicCount (X : ℕ) : ℕ :=
  (exceptionalDyadicGaps X).card

/-! ## Prime-enumeration and logical normal forms -/

lemma nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.prime_nth_prime n

lemma nthPrime_lt_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  nthPrime_strictMono (Nat.lt_succ_self n)

lemma no_prime_between_nthPrime (n r : ℕ)
    (hleft : nthPrime n < r) (hright : r < nthPrime (n + 1)) :
    ¬Nat.Prime r := by
  intro hr
  have hrle : r ≤ nthPrime n := by
    exact Nat.le_nth_of_lt_nth_succ hright hr
  exact (not_lt_of_ge hrle) hleft

lemma exceptionalGap_iff (n : ℕ) :
    ExceptionalGap n ↔
      ∀ m : ℕ, nthPrime n < m → m < nthPrime (n + 1) →
        Nat.minFac m < gapLength n := by
  constructor
  · intro h m hm₁ hm₂
    by_contra hnot
    exact h ⟨m, hm₁, hm₂, Nat.le_of_not_gt hnot⟩
  · intro h ⟨m, hm₁, hm₂, hm₃⟩
    exact (not_lt_of_ge hm₃) (h m hm₁ hm₂)

/-! ## Rough-number interface -/

/-- An integer is `z`-rough when it has no prime divisor strictly below
`z`.  This is the form consumed by a combinatorial sieve. -/
def IsRough (z m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p < z → ¬p ∣ m

/-- Away from the exceptional value `m = 1`, the repository's sieve-theoretic
notion of `z`-roughness is exactly the least-prime-factor inequality occurring
in Erdős's question. -/
lemma isZRough_iff_le_minFac {z m : ℕ} (hm : m ≠ 1) :
    IsRough z m ↔ z ≤ Nat.minFac m := by
  constructor
  · intro h
    by_contra hz
    exact h (Nat.minFac m) (Nat.minFac_prime hm)
      (Nat.lt_of_not_ge hz) (Nat.minFac_dvd m)
  · intro h p hp hpz hpm
    exact (not_lt_of_ge
      (h.trans (Nat.minFac_le_of_dvd hp.two_le hpm))) hpz

/-- Sieve-ready normal form of the good-gap predicate. -/
lemma goodGap_iff_exists_rough (n : ℕ) :
    GoodGap n ↔
      ∃ m : ℕ, nthPrime n < m ∧ m < nthPrime (n + 1) ∧
        IsRough (gapLength n) m := by
  constructor
  · rintro ⟨m, hmleft, hmright, hmrough⟩
    refine ⟨m, hmleft, hmright, ?_⟩
    apply (isZRough_iff_le_minFac ?_).2 hmrough
    have hmTwo : 2 < m :=
      (nthPrime_prime n).two_le.trans_lt hmleft
    omega
  · rintro ⟨m, hmleft, hmright, hmrough⟩
    refine ⟨m, hmleft, hmright, ?_⟩
    apply (isZRough_iff_le_minFac ?_).1 hmrough
    have hmTwo : 2 < m :=
      (nthPrime_prime n).two_le.trans_lt hmleft
    omega

/-- Increasing the roughness cutoff strengthens the roughness condition. -/
lemma IsRough.mono_cutoff {z₁ z₂ m : ℕ} (hz : z₁ ≤ z₂)
    (h : IsRough z₂ m) : IsRough z₁ m := by
  intro p hp hpz
  exact h p hp (hpz.trans_le hz)

/-! ## Exact finite sieves for rough shifted integers

For the qualitative theorem it is enough to take the roughness cutoff to be
a fixed multiple of `log X`.  Full finite inclusion--exclusion then has only
`2 ^ π(z)` terms, an `X ^ o(1)` endpoint error.  The following constructor
is the full-prime analogue of `Erdos851.ShiftSieve.boundingSieve`; its extra
admissibility hypothesis handles the prime `2` explicitly. -/

open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega

namespace FullShiftSieve

open Erdos851.ShiftSieve

/-- Dyadic points for which every prime below `z` misses the product of the
selected shifted residuals. -/
def candidates (shifts : Finset ℕ) (X z : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun a ↦
    Nat.Coprime (Erdos387.sievePrimeProduct 1 z) (shiftedProduct shifts a)

theorem coprime_sieveProduct_iff_rough {z n : ℕ} :
    Nat.Coprime (Erdos387.sievePrimeProduct 1 z) n ↔ IsRough z n := by
  constructor
  · intro hcop p hp hpz hpn
    have hpMem : p ∈ Erdos387.sievePrimes 1 z :=
      Erdos387.mem_sievePrimes.mpr ⟨hp, hp.one_lt, hpz⟩
    have hpProd : p ∣ Erdos387.sievePrimeProduct 1 z := by
      exact Finset.dvd_prod_of_mem id hpMem
    have hpGcd : p ∣ Nat.gcd (Erdos387.sievePrimeProduct 1 z) n :=
      Nat.dvd_gcd hpProd hpn
    have hpOne : p ∣ 1 := by simpa [hcop.gcd_eq_one] using hpGcd
    exact hp.ne_one (Nat.dvd_one.mp hpOne)
  · intro hrough
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hgcd
    obtain ⟨p, hp, hpDvd⟩ := Nat.exists_prime_and_dvd hgcd
    have hpProd : p ∣ Erdos387.sievePrimeProduct 1 z :=
      hpDvd.trans (Nat.gcd_dvd_left _ _)
    have hpMem := Erdos387.mem_sievePrimes.mp
      (Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpProd)
    exact hrough p hp hpMem.2.2
      (hpDvd.trans (Nat.gcd_dvd_right _ _))

theorem mem_candidates_iff {shifts : Finset ℕ} {X z a : ℕ} :
    a ∈ candidates shifts X z ↔
      a ∈ Finset.Ioc X (2 * X) ∧
        ∀ s ∈ shifts, IsRough z (a - s) := by
  rw [candidates, Finset.mem_filter]
  refine and_congr_right fun _ha ↦ ?_
  rw [shiftedProduct, Nat.coprime_prod_right_iff]
  constructor
  · intro h s hs
    exact coprime_sieveProduct_iff_rough.mp (h s hs)
  · intro h s hs
    exact coprime_sieveProduct_iff_rough.mpr (h s hs)

/-- The full small-prime bounding sieve. -/
noncomputable def boundingSieve (shifts : Finset ℕ)
    (hshifts : shifts.Nonempty) (X z : ℕ)
    (hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p) :
    BoundingSieve := by
  classical
  let I := Finset.Ioc X (2 * X)
  exact
    { support := I.image (shiftedProduct shifts)
      prodPrimes := Erdos387.sievePrimeProduct 1 z
      prodPrimes_squarefree := Erdos387.sievePrimeProduct_squarefree 1 z
      weights := fun q ↦
        ((I.filter fun a ↦ shiftedProduct shifts a = q).card : ℝ)
      weights_nonneg := fun _ ↦ by positivity
      totalMass := X
      nu := shiftNu shifts
      nu_mult := shiftNu_mult shifts
      nu_pos_of_prime := by
        intro p hp _hpDiv
        rw [shiftNu_prime hp]
        exact div_pos (by exact_mod_cast localNu_pos hshifts p)
          (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp hpDiv
        rw [shiftNu_prime hp]
        have hpMem :=
          Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpDiv
        have hpz : p < z := (Erdos387.mem_sievePrimes.mp hpMem).2.2
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hadmissible p hp hpz) }

@[simp] theorem boundingSieve_totalMass
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p} :
    (boundingSieve shifts hshifts X z hadmissible).totalMass = X := rfl

/-- The abstract multiple sum is the literal divisibility count. -/
theorem boundingSieve_multSum
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z d : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p} :
    (boundingSieve shifts hshifts X z hadmissible).multSum d =
      ((divisibleShiftCandidates shifts X d).card : ℝ) := by
  classical
  let I := Finset.Ioc X (2 * X)
  let f := shiftedProduct shifts
  rw [BoundingSieve.multSum]
  change (∑ q ∈ I.image f,
      if d ∣ q then ((I.filter fun a ↦ f a = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦ d ∣ q,
          (I.filter fun a ↦ f a = q).card) =
        (I.filter fun a ↦ d ∣ f a).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

/-- The abstract sifted sum is the literal full-prime candidate count. -/
theorem boundingSieve_siftedSum
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p} :
    (boundingSieve shifts hshifts X z hadmissible).siftedSum =
      ((candidates shifts X z).card : ℝ) := by
  classical
  let I := Finset.Ioc X (2 * X)
  let f := shiftedProduct shifts
  rw [BoundingSieve.siftedSum]
  change (∑ q ∈ I.image f,
      if Nat.Coprime (Erdos387.sievePrimeProduct 1 z) q then
        ((I.filter fun a ↦ f a = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦
          Nat.Coprime (Erdos387.sievePrimeProduct 1 z) q,
          (I.filter fun a ↦ f a = q).card) =
        (I.filter fun a ↦
          Nat.Coprime (Erdos387.sievePrimeProduct 1 z) (f a)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

/-- Exact interval endpoint discrepancy for the full small-prime sieve. -/
theorem boundingSieve_abs_rem_le_nuClasses
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z d : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hd : d ∣ Erdos387.sievePrimeProduct 1 z) :
    |(boundingSieve shifts hshifts X z hadmissible).rem d| ≤
      nuClasses shifts d := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree 1 z)
  rw [BoundingSieve.rem, boundingSieve_multSum,
    boundingSieve_totalMass]
  change
    |↑(divisibleShiftCandidates shifts X d).card -
        shiftNu shifts d * (X : ℝ)| ≤ (nuClasses shifts d : ℝ)
  rw [shiftNu_squarefree hsq]
  simpa [mul_div_assoc, mul_comm, mul_left_comm] using
    abs_card_divisibleShiftCandidates_sub_density
      (shifts := shifts) (X := X) (z := 1) (Y := z) hshiftX hd

theorem singleton_admissible (s z : ℕ) :
    ∀ p : ℕ, p.Prime → p < z → localNu {s} p < p := by
  intro p hp _hpz
  rw [localNu_singleton]
  exact hp.one_lt

/-- Two shifts in the same parity class form an admissible pair even when
the prime `2` is included in the sieve. -/
theorem pair_admissible_of_sameParity {s t z : ℕ}
    (hparity : s % 2 = t % 2) :
    ∀ p : ℕ, p.Prime → p < z → localNu {s, t} p < p := by
  intro p hp _hpz
  by_cases hp2 : p = 2
  · subst p
    rw [localNu_pair_eq_one_iff.mpr hparity]
    norm_num
  · exact (localNu_pair_le_two s t p).trans_lt
      (lt_of_le_of_ne hp.two_le (Ne.symm hp2))

/-- Opposite-parity pairs are removed completely by the prime `2`. -/
theorem candidates_pair_eq_empty_of_oppositeParity
    {s t X z : ℕ} (hsX : s ≤ X) (htX : t ≤ X)
    (hz : 2 < z) (hparity : s % 2 ≠ t % 2) :
    candidates {s, t} X z = ∅ := by
  classical
  ext a
  simp only [Finset.notMem_empty, iff_false]
  intro ha
  have haData := (mem_candidates_iff.mp ha)
  have haX : X < a := (Finset.mem_Ioc.mp haData.1).1
  have hsa : ∀ q ∈ ({s, t} : Finset ℕ), q ≤ a := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hsX.trans haX.le
    · exact htX.trans haX.le
  have hresidue : a % 2 = s % 2 ∨ a % 2 = t % 2 := by
    have ha2 := Nat.mod_lt a (by norm_num : 0 < 2)
    have hs2 := Nat.mod_lt s (by norm_num : 0 < 2)
    have ht2 := Nat.mod_lt t (by norm_num : 0 < 2)
    omega
  have htwoDvd : 2 ∣ shiftedProduct {s, t} a := by
    rw [prime_dvd_shiftedProduct_iff Nat.prime_two hsa]
    rcases hresidue with has | hat
    · exact ⟨s, by simp, has⟩
    · exact ⟨t, by simp, hat⟩
  have htwoMem : 2 ∈ Erdos387.sievePrimes 1 z :=
    Erdos387.mem_sievePrimes.mpr ⟨Nat.prime_two, by norm_num, hz⟩
  have htwoProd : 2 ∣ Erdos387.sievePrimeProduct 1 z :=
    Finset.dvd_prod_of_mem id htwoMem
  have hcop := (Finset.mem_filter.mp ha).2
  have htwoOne : 2 ∣ 1 := by
    have := Nat.dvd_gcd htwoProd htwoDvd
    simpa [hcop.gcd_eq_one] using this
  norm_num at htwoOne

/-- A squarefree sieve product has one divisor for every subset of its
prime factors. -/
theorem sieveProduct_divisors_card (z : ℕ) :
    (Erdos387.sievePrimeProduct 1 z).divisors.card =
      2 ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
  let P := Erdos387.sievePrimeProduct 1 z
  have hP : Squarefree P := Erdos387.sievePrimeProduct_squarefree 1 z
  rw [Erdos387.divisors_eq_image_prod_primeFactorSubsets hP,
    Finset.card_image_of_injOn (Erdos387.prod_primeFactorSubsets_injOn P),
    Finset.card_powerset]

/-- With at most two forbidden classes at every prime, the number of CRT
classes at every divisor of the sieve product is at most `2 ^ r`. -/
theorem nuClasses_le_two_pow_sieveCard
    {shifts : Finset ℕ} {z d : ℕ}
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2)
    (hd : d ∣ Erdos387.sievePrimeProduct 1 z) :
    nuClasses shifts d ≤
      2 ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
  have hPne : Erdos387.sievePrimeProduct 1 z ≠ 0 :=
    (Erdos387.sievePrimeProduct_pos 1 z).ne'
  have hsubset : d.primeFactors ⊆
      (Erdos387.sievePrimeProduct 1 z).primeFactors :=
    Nat.primeFactors_mono hd hPne
  calc
    nuClasses shifts d ≤ 2 ^ d.primeFactors.card := by
      unfold nuClasses
      simpa using Finset.prod_le_prod (fun p hp ↦ Nat.zero_le _)
        (fun p hp ↦ hlocal p)
    _ ≤ 2 ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (Finset.card_le_card hsubset)

/-- Full inclusion--exclusion has endpoint loss at most `4 ^ r` for a
one- or two-shift sieve with `r` small primes. -/
theorem errSum_le_four_pow_sieveCard
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2)
    (mu : ℕ → ℝ) (hmu : ∀ d : ℕ, |mu d| ≤ 1) :
    (boundingSieve shifts hshifts X z hadmissible).errSum mu ≤
      (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
  let P := Erdos387.sievePrimeProduct 1 z
  let r := P.primeFactors.card
  rw [BoundingSieve.errSum]
  calc
    (∑ d ∈ P.divisors,
        |mu d| * |(boundingSieve shifts hshifts X z hadmissible).rem d|) ≤
        ∑ _d ∈ P.divisors, ((2 ^ r : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : d ∣ P := (Nat.mem_divisors.mp hdmem).1
      have hrem := boundingSieve_abs_rem_le_nuClasses
        (shifts := shifts) (hshifts := hshifts) (X := X) (z := z)
        (hadmissible := hadmissible) hshiftX hd
      calc
        |mu d| * |(boundingSieve shifts hshifts X z hadmissible).rem d| ≤
            1 * (nuClasses shifts d : ℝ) :=
          mul_le_mul (hmu d) hrem (abs_nonneg _) (by norm_num)
        _ ≤ ((2 ^ r : ℕ) : ℝ) := by
          have hnat : nuClasses shifts d ≤ 2 ^ r := by
            dsimp [r, P]
            exact nuClasses_le_two_pow_sieveCard hlocal hd
          simpa only [one_mul] using (show
            (nuClasses shifts d : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) by
              exact_mod_cast hnat)
    _ = (P.divisors.card : ℝ) * (2 : ℝ) ^ r := by simp
    _ = (2 : ℝ) ^ r * (2 : ℝ) ^ r := by
      rw [sieveProduct_divisors_card]
      norm_cast
    _ = (2 : ℝ) ^ (r + r) := (pow_add 2 r r).symm
    _ = (2 : ℝ) ^ (2 * r) := by congr 1 <;> omega
    _ = ((2 : ℝ) ^ 2) ^ r := by rw [pow_mul]
    _ = (4 : ℝ) ^ r := by norm_num

/-- Exact lower fundamental estimate obtained by taking the odd Brun level
beyond the entire finite prime set. -/
theorem lower_cardinality_bound
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2) :
    let s := boundingSieve shifts hshifts X z hadmissible
    let r := (Erdos387.sievePrimeProduct 1 z).primeFactors.card
    (X : ℝ) * Erdos387.finiteEulerProduct
          (Erdos387.sievePrimeProduct 1 z).primeFactors
          (fun p ↦ shiftNu shifts p) - (4 : ℝ) ^ r ≤
      ((candidates shifts X z).card : ℝ) := by
  dsimp only
  let s := boundingSieve shifts hshifts X z hadmissible
  let r := (Erdos387.sievePrimeProduct 1 z).primeFactors.card
  let L := 2 * r + 1
  have hLodd : Odd L := by
    refine ⟨r, ?_⟩
    simp [L]
  have hcard : (Erdos387.sievePrimeProduct 1 z).primeFactors.card ≤ L := by
    dsimp [r, L]
    omega
  have hmain :=
    Erdos387.boundingSieve_mainSum_brunLowerWeight_eq_euler_of_card_le
      s hcard
  have herr := errSum_le_four_pow_sieveCard
    (shifts := shifts) (hshifts := hshifts) (X := X) (z := z)
      (hadmissible := hadmissible) hshiftX hlocal
      (Erdos387.brunLowerWeight L)
      (Erdos387.abs_brunLowerWeight_le_one L)
  have hlower := BoundingSieve.totalMass_mainSum_sub_errSum_le_siftedSum
    (s := s) (Erdos387.brunLowerWeight L)
      (Erdos387.brunLowerWeight_isLowerOnProdPrimes s hLodd)
  rw [hmain, show s.totalMass = X by rfl,
    show s.siftedSum = ((candidates shifts X z).card : ℝ) by
      exact boundingSieve_siftedSum] at hlower
  exact (sub_le_sub_left herr _).trans hlower

/-- Exact upper fundamental estimate at an even full-inclusion level. -/
theorem upper_cardinality_bound
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2) :
    let s := boundingSieve shifts hshifts X z hadmissible
    let r := (Erdos387.sievePrimeProduct 1 z).primeFactors.card
    ((candidates shifts X z).card : ℝ) ≤
      (X : ℝ) * Erdos387.finiteEulerProduct
          (Erdos387.sievePrimeProduct 1 z).primeFactors
          (fun p ↦ shiftNu shifts p) + (4 : ℝ) ^ r := by
  dsimp only
  let s := boundingSieve shifts hshifts X z hadmissible
  let r := (Erdos387.sievePrimeProduct 1 z).primeFactors.card
  let L := 2 * r
  have hLeven : Even L := ⟨r, by dsimp [L]; omega⟩
  have hcard : (Erdos387.sievePrimeProduct 1 z).primeFactors.card ≤ L := by
    dsimp [r, L]
    omega
  have hmain :=
    Erdos387.boundingSieve_mainSum_brunUpperWeight_eq_euler_of_card_le
      s hcard
  have herr := errSum_le_four_pow_sieveCard
    (shifts := shifts) (hshifts := hshifts) (X := X) (z := z)
      (hadmissible := hadmissible) hshiftX hlocal
      (Erdos387.brunUpperWeight L)
      (Erdos387.abs_brunUpperWeight_le_one L)
  have hupper := BoundingSieve.siftedSum_le_totalMass_mainSum_add_errSum
    (s := s) (Erdos387.brunUpperWeight L)
      (Erdos387.brunUpperWeight_isUpperOnProdPrimes s hLeven)
  rw [hmain, show s.totalMass = X by rfl,
    show s.siftedSum = ((candidates shifts X z).card : ℝ) by
      exact boundingSieve_siftedSum] at hupper
  change ((candidates shifts X z).card : ℝ) ≤
      (X : ℝ) * Erdos387.finiteEulerProduct
        (Erdos387.sievePrimeProduct 1 z).primeFactors
        (fun p ↦ shiftNu shifts p) +
      (boundingSieve shifts hshifts X z hadmissible).errSum
        (Erdos387.brunUpperWeight L) at hupper
  exact hupper.trans (add_le_add_right herr _)

/-- The endpoint loss for a level-`L` Brun truncation.  Only divisors with
at most `L` prime factors occur, so there are at most `z^L+1` possible
divisors and each carries at most `2^L` simultaneous residue classes. -/
noncomputable def brunEndpointError (z L : ℕ) : ℝ :=
  ((z ^ L + 1 : ℕ) : ℝ) * (2 : ℝ) ^ L

theorem errSum_brunWeight_le
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z L : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hz : 1 ≤ z) (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2)
    (mu : ℕ → ℝ) (hmu : ∀ d : ℕ, |mu d| ≤ 1)
    (hsupport : ∀ d : ℕ, ¬ d.primeFactors.card ≤ L → mu d = 0) :
    (boundingSieve shifts hshifts X z hadmissible).errSum mu ≤
      brunEndpointError z L := by
  let P := Erdos387.sievePrimeProduct 1 z
  let s := boundingSieve shifts hshifts X z hadmissible
  rw [BoundingSieve.errSum]
  calc
    (∑ d ∈ P.divisors, |mu d| * |s.rem d|) ≤
        ∑ d ∈ P.divisors,
          if d.primeFactors.card ≤ L then ((2 : ℝ) ^ L) else 0 := by
      apply Finset.sum_le_sum
      intro d hdmem
      by_cases hdL : d.primeFactors.card ≤ L
      · rw [if_pos hdL]
        have hd : d ∣ P := (Nat.mem_divisors.mp hdmem).1
        have hrem := boundingSieve_abs_rem_le_nuClasses
          (shifts := shifts) (hshifts := hshifts) (X := X) (z := z)
          (hadmissible := hadmissible) hshiftX hd
        have hnu : nuClasses shifts d ≤ 2 ^ L := by
          have hsq : Squarefree d :=
            Squarefree.squarefree_of_dvd hd
              (Erdos387.sievePrimeProduct_squarefree 1 z)
          calc
            nuClasses shifts d ≤ 2 ^ d.primeFactors.card := by
              unfold nuClasses
              simpa using Finset.prod_le_prod (fun p hp ↦ Nat.zero_le _)
                (fun p hp ↦ hlocal p)
            _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hdL
        calc
          |mu d| * |s.rem d| ≤ 1 * (nuClasses shifts d : ℝ) :=
            mul_le_mul (hmu d) hrem (abs_nonneg _) (by norm_num)
          _ ≤ (2 : ℝ) ^ L := by
            simpa only [one_mul] using (show
              (nuClasses shifts d : ℝ) ≤ (2 : ℝ) ^ L by
                exact_mod_cast hnu)
      · rw [if_neg hdL, hsupport d hdL]
        simp
    _ = (((P.divisors.filter fun d ↦ d.primeFactors.card ≤ L).card : ℕ) : ℝ) *
          (2 : ℝ) ^ L := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ ((z ^ L + 1 : ℕ) : ℝ) * (2 : ℝ) ^ L := by
      gcongr
      exact_mod_cast Erdos387.card_brunSupport_le (k := 1) hz
    _ = brunEndpointError z L := rfl

theorem errSum_brunLowerWeight_le
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z L : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hz : 1 ≤ z) (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2) :
    (boundingSieve shifts hshifts X z hadmissible).errSum
        (Erdos387.brunLowerWeight L) ≤ brunEndpointError z L := by
  apply errSum_brunWeight_le hz hshiftX hlocal
  · exact Erdos387.abs_brunLowerWeight_le_one L
  · intro d hd
    unfold Erdos387.brunLowerWeight
    rw [if_neg]
    simpa [Erdos387.cardDistinctFactors_eq_primeFactors_card] using hd

theorem errSum_brunUpperWeight_le
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z L : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hz : 1 ≤ z) (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2) :
    (boundingSieve shifts hshifts X z hadmissible).errSum
        (Erdos387.brunUpperWeight L) ≤ brunEndpointError z L := by
  apply errSum_brunWeight_le hz hshiftX hlocal
  · exact Erdos387.abs_brunUpperWeight_le_one L
  · intro d hd
    unfold Erdos387.brunUpperWeight
    rw [if_neg]
    simpa [Erdos387.cardDistinctFactors_eq_primeFactors_card] using hd

/-- Truncated-Brun lower cardinality bound, with the main-term tail left
explicit for later parameter selection. -/
theorem lower_cardinality_bound_brun
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z L : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hz : 1 ≤ z) (hL : Odd L)
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2) :
    let V := Erdos387.finiteEulerProduct
      (Erdos387.sievePrimeProduct 1 z).primeFactors
      (fun p ↦ shiftNu shifts p)
    let T := Erdos387.brunSubsetTail
      (Erdos387.sievePrimeProduct 1 z).primeFactors
      (fun p ↦ shiftNu shifts p) L
    (X : ℝ) * (V - T) - brunEndpointError z L ≤
      ((candidates shifts X z).card : ℝ) := by
  dsimp only
  let s := boundingSieve shifts hshifts X z hadmissible
  let V := Erdos387.finiteEulerProduct
    (Erdos387.sievePrimeProduct 1 z).primeFactors
    (fun p ↦ shiftNu shifts p)
  let T := Erdos387.brunSubsetTail
    (Erdos387.sievePrimeProduct 1 z).primeFactors
    (fun p ↦ shiftNu shifts p) L
  change (X : ℝ) * (V - T) - brunEndpointError z L ≤
    ((candidates shifts X z).card : ℝ)
  have hmainAbs :=
    Erdos387.boundingSieve_abs_mainSum_brunLowerWeight_sub_euler_le s L
  have hmain : V - T ≤ s.mainSum (Erdos387.brunLowerWeight L) := by
    change |s.mainSum (Erdos387.brunLowerWeight L) - V| ≤ T at hmainAbs
    linarith [abs_le.mp hmainAbs]
  have herr := errSum_brunLowerWeight_le
    (shifts := shifts) (hshifts := hshifts) (X := X) (z := z)
    (L := L) (hadmissible := hadmissible) hz hshiftX hlocal
  have hlower := s.totalMass_mainSum_sub_errSum_le_siftedSum
    (Erdos387.brunLowerWeight L)
    (Erdos387.brunLowerWeight_isLowerOnProdPrimes s hL)
  rw [show s.totalMass = X by rfl,
    show s.siftedSum = ((candidates shifts X z).card : ℝ) by
      exact boundingSieve_siftedSum] at hlower
  have hmul := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg X)
  exact (sub_le_sub hmul herr).trans hlower

/-- Truncated-Brun upper cardinality bound. -/
theorem upper_cardinality_bound_brun
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty} {X z L : ℕ}
    {hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p}
    (hz : 1 ≤ z) (hL : Even L)
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2) :
    let V := Erdos387.finiteEulerProduct
      (Erdos387.sievePrimeProduct 1 z).primeFactors
      (fun p ↦ shiftNu shifts p)
    let T := Erdos387.brunSubsetTail
      (Erdos387.sievePrimeProduct 1 z).primeFactors
      (fun p ↦ shiftNu shifts p) L
    ((candidates shifts X z).card : ℝ) ≤
      (X : ℝ) * (V + T) + brunEndpointError z L := by
  dsimp only
  let s := boundingSieve shifts hshifts X z hadmissible
  let V := Erdos387.finiteEulerProduct
    (Erdos387.sievePrimeProduct 1 z).primeFactors
    (fun p ↦ shiftNu shifts p)
  let T := Erdos387.brunSubsetTail
    (Erdos387.sievePrimeProduct 1 z).primeFactors
    (fun p ↦ shiftNu shifts p) L
  change ((candidates shifts X z).card : ℝ) ≤
    (X : ℝ) * (V + T) + brunEndpointError z L
  have hmainAbs :=
    Erdos387.boundingSieve_abs_mainSum_brunUpperWeight_sub_euler_le s L
  have hmain : s.mainSum (Erdos387.brunUpperWeight L) ≤ V + T := by
    change |s.mainSum (Erdos387.brunUpperWeight L) - V| ≤ T at hmainAbs
    linarith [abs_le.mp hmainAbs]
  have herr := errSum_brunUpperWeight_le
    (shifts := shifts) (hshifts := hshifts) (X := X) (z := z)
    (L := L) (hadmissible := hadmissible) hz hshiftX hlocal
  have hupper := s.siftedSum_le_totalMass_mainSum_add_errSum
    (Erdos387.brunUpperWeight L)
    (Erdos387.brunUpperWeight_isUpperOnProdPrimes s hL)
  rw [show s.totalMass = X by rfl,
    show s.siftedSum = ((candidates shifts X z).card : ℝ) by
      exact boundingSieve_siftedSum] at hupper
  have hmul := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg X)
  exact hupper.trans (add_le_add hmul herr)

theorem sieveProduct_primeFactors (z : ℕ) :
    (Erdos387.sievePrimeProduct 1 z).primeFactors =
      Erdos387.sievePrimes 1 z := by
  unfold Erdos387.sievePrimeProduct
  exact Nat.primeFactors_prod fun p hp ↦
    (Erdos387.mem_sievePrimes.mp hp).1

theorem sievePrimes_one_eq_primesThrough {z : ℕ} (hz : 2 ≤ z) :
    Erdos387.sievePrimes 1 z = Erdos469.primesThrough (z - 1) := by
  ext p
  rw [Erdos387.mem_sievePrimes, Erdos469.mem_primesThrough]
  constructor
  · rintro ⟨hp, _hpOne, hpz⟩
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, hpz⟩
    exact ⟨hp, hp.one_lt, by omega⟩

/-- The one-shift local mass for rough integers. -/
noncomputable def roughEulerMass (z : ℕ) : ℝ :=
  Erdos387.finiteEulerProduct
    (Erdos387.sievePrimeProduct 1 z).primeFactors
    (fun p ↦ shiftNu ({0} : Finset ℕ) p)

theorem roughEulerMass_eq_mertensProduct {z : ℕ} (hz : 2 ≤ z) :
    roughEulerMass z =
      (Erdos469.primesThrough (z - 1)).prod Erdos469.mertensLinearFactor := by
  rw [roughEulerMass, Erdos387.finiteEulerProduct,
    sieveProduct_primeFactors, sievePrimes_one_eq_primesThrough hz]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := (Erdos469.mem_primesThrough.mp hp).1
  rw [shiftNu_prime hpPrime, localNu_singleton]
  simp [Erdos469.mertensLinearFactor, zpow_neg, div_eq_mul_inv]

theorem roughEulerMass_bounds {z : ℕ} (hz : 3 ≤ z) :
    Erdos469.naturalLinearMertensLower / Real.log (z - 1 : ℕ) ≤
        roughEulerMass z ∧
      roughEulerMass z ≤
        Erdos469.naturalLinearMertensUpper / Real.log (z - 1 : ℕ) := by
  rw [roughEulerMass_eq_mertensProduct (by omega)]
  exact Erdos469.natural_linearMertensProduct_bounds (by omega)

/-- The primes below `z` split into `2` and the odd primes in `(2,z)`. -/
theorem sieveProduct_primeFactors_eq_insert_two_odd {z : ℕ} (hz : 3 ≤ z) :
    (Erdos387.sievePrimeProduct 1 z).primeFactors =
      insert 2 (Erdos851.sievePrimes 2 (z - 1)) := by
  rw [sieveProduct_primeFactors]
  ext p
  simp only [Erdos387.mem_sievePrimes, Erdos851.mem_sievePrimes,
    Finset.mem_insert]
  constructor
  · rintro ⟨hp, hp1, hpz⟩
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    · exact Or.inr ⟨by omega, by omega, hp⟩
  · rintro (rfl | ⟨hp2, hpz, hp⟩)
    · exact ⟨Nat.prime_two, by norm_num, by omega⟩
    · exact ⟨hp, hp.one_lt, by omega⟩

theorem two_not_mem_oddSievePrimes (y : ℕ) :
    2 ∉ Erdos851.sievePrimes 2 y := by
  simp [Erdos851.mem_sievePrimes]

/-- Removing the prime `2` doubles the one-shift Euler mass. -/
theorem odd_oneShiftEuler_eq_two_mul_roughEulerMass {z : ℕ} (hz : 3 ≤ z) :
    Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 (z - 1) =
      2 * roughEulerMass z := by
  rw [roughEulerMass, Erdos387.finiteEulerProduct,
    sieveProduct_primeFactors_eq_insert_two_odd hz,
    Finset.prod_insert (two_not_mem_oddSievePrimes (z - 1))]
  have htwo : shiftNu ({0} : Finset ℕ) 2 = (2 : ℝ)⁻¹ := by
    rw [shiftNu_prime Nat.prime_two, localNu_singleton]
    norm_num
  rw [htwo]
  simp only [Erdos851.localEulerProduct]
  have hodd :
      (∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
          (1 - shiftNu ({0} : Finset ℕ) p)) =
        ∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
          (1 - Erdos851.oneShiftDensity p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Erdos851.shiftNu_singleton_prime 0
      (Erdos851.mem_sievePrimes.mp hp).2.2]
  rw [hodd]
  ring

/-- The full two-shift Euler mass used by the exact moment sieve. -/
noncomputable def pairEulerMass (s t z : ℕ) : ℝ :=
  Erdos387.finiteEulerProduct
    (Erdos387.sievePrimeProduct 1 z).primeFactors
    (fun p ↦ shiftNu ({s, t} : Finset ℕ) p)

/-- For same-parity shifts, the prime `2` contributes `1/2`; the remaining
pair product is the square of the odd one-shift mass times its exact direct
correction. -/
theorem pairEulerMass_eq_two_mul_sq_mul_correction
    {s t z : ℕ} (hz : 3 ≤ z) (hparity : s % 2 = t % 2) :
    pairEulerMass s t z =
      2 * roughEulerMass z ^ 2 *
        ∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
          Erdos851.pairDirectCorrection (Nat.dist s t) p := by
  rw [pairEulerMass, Erdos387.finiteEulerProduct,
    sieveProduct_primeFactors_eq_insert_two_odd hz,
    Finset.prod_insert (two_not_mem_oddSievePrimes (z - 1))]
  have htwo : shiftNu ({s, t} : Finset ℕ) 2 = (2 : ℝ)⁻¹ := by
    rw [shiftNu_prime Nat.prime_two,
      localNu_pair_eq_one_iff.mpr hparity]
    norm_num
  rw [htwo]
  have hodd :
      (∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
          (1 - shiftNu ({s, t} : Finset ℕ) p)) =
        Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (Nat.dist s t)) 2 (z - 1) := by
    simp only [Erdos851.localEulerProduct]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Erdos851.shiftNu_pair_prime s t
      (Erdos851.mem_sievePrimes.mp hp).2.2]
  rw [hodd, Erdos851.pairShift_localEulerProduct_eq (Nat.dist s t)
    (by norm_num : 2 ≤ 2),
    odd_oneShiftEuler_eq_two_mul_roughEulerMass hz]
  ring

theorem singletonEulerMass (s z : ℕ) :
    Erdos387.finiteEulerProduct
        (Erdos387.sievePrimeProduct 1 z).primeFactors
        (fun p ↦ shiftNu ({s} : Finset ℕ) p) = roughEulerMass z := by
  unfold roughEulerMass Erdos387.finiteEulerProduct
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  change 1 - shiftNu ({s} : Finset ℕ) p =
    1 - shiftNu ({0} : Finset ℕ) p
  rw [Erdos851.shiftNu_singleton_prime s hpPrime,
    Erdos851.shiftNu_singleton_prime 0 hpPrime]

/-- A uniform local comparison for all admissible one- and two-shift
systems.  The deliberately coarse constant `18` handles the worst local
case `ν(3)=2`. -/
lemma one_add_two_shiftNu_le_harmonic_mul
    {shifts : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hadm : localNu shifts p < p) (hlocal : localNu shifts p ≤ 2) :
    1 + 2 * shiftNu shifts p ≤
      (1 + (18 : ℝ) / p) * (1 - shiftNu shifts p) := by
  rw [shiftNu_prime hp]
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcases : localNu shifts p = 0 ∨
      localNu shifts p = 1 ∨ localNu shifts p = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · rw [hzero]
    simp
    positivity
  · rw [hone]
    have hpTwoR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    field_simp
    ring_nf
    nlinarith
  · rw [htwo]
    have hp3 : 3 ≤ p := by omega
    have hpThreeR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    field_simp
    ring_nf
    nlinarith

/-- The complete powers-of-two moment of the local densities is at most a
fixed polynomial times the Euler product.  This elementary estimate is what
makes a logarithmic Brun depth sufficient. -/
theorem shiftMomentProduct_le_poly_mul_euler
    {shifts : Finset ℕ} {z : ℕ}
    (hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2) :
    (∏ p ∈ (Erdos387.sievePrimeProduct 1 z).primeFactors,
        (1 + 2 * shiftNu shifts p)) ≤
      (((z + 1 : ℕ) : ℝ) ^ 18) *
        Erdos387.finiteEulerProduct
          (Erdos387.sievePrimeProduct 1 z).primeFactors
          (fun p ↦ shiftNu shifts p) := by
  let P := (Erdos387.sievePrimeProduct 1 z).primeFactors
  have hP (p : ℕ) (hpP : p ∈ P) :
      p.Prime ∧ 0 < p ∧ p ≤ z := by
    have hp := Nat.prime_of_mem_primeFactors hpP
    have hpDvd := Nat.dvd_of_mem_primeFactors hpP
    have hpMem := Erdos387.mem_sievePrimes.mp
      (Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpDvd)
    exact ⟨hp, hp.pos, hpMem.2.2.le⟩
  have hfactorNonneg (p : ℕ) (hpP : p ∈ P) :
      0 ≤ 1 - shiftNu shifts p := by
    have hp := (hP p hpP).1
    rw [shiftNu_prime hp]
    exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast hp.pos)).mpr
      (by exact_mod_cast (hadmissible p hp
        (Erdos387.mem_sievePrimes.mp
          (Erdos387.prime_mem_sievePrimes_of_dvd_product hp
            (Nat.dvd_of_mem_primeFactors hpP))).2.2).le))
  calc
    (∏ p ∈ P, (1 + 2 * shiftNu shifts p)) ≤
        ∏ p ∈ P,
          ((1 + (18 : ℝ) / p) * (1 - shiftNu shifts p)) := by
      apply Finset.prod_le_prod
      · intro p hpP
        have hp := (hP p hpP).1
        rw [shiftNu_prime hp]
        positivity
      · intro p hpP
        have hp := (hP p hpP).1
        exact one_add_two_shiftNu_le_harmonic_mul hp
          (hadmissible p hp
            (Erdos387.mem_sievePrimes.mp
              (Erdos387.prime_mem_sievePrimes_of_dvd_product hp
                (Nat.dvd_of_mem_primeFactors hpP))).2.2)
          (hlocal p)
    _ = (∏ p ∈ P, (1 + (18 : ℝ) / p)) *
          Erdos387.finiteEulerProduct P (fun p ↦ shiftNu shifts p) := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ ≤ (((z + 1 : ℕ) : ℝ) ^ 18) *
          Erdos387.finiteEulerProduct P (fun p ↦ shiftNu shifts p) := by
      exact mul_le_mul_of_nonneg_right
        (Erdos387.prod_one_add_nat_div_le_pow P 18 z
          (fun p hp ↦ (hP p hp).2.1) (fun p hp ↦ (hP p hp).2.2))
        (by
          unfold Erdos387.finiteEulerProduct
          exact Finset.prod_nonneg hfactorNonneg)

/-- A numerical power-of-two comparison turns the polynomial moment bound
into an arbitrary relative Brun-tail bound. -/
theorem brunSubsetTail_le_eta_mul_euler
    {shifts : Finset ℕ} {z L : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hadmissible : ∀ p : ℕ, p.Prime → p < z → localNu shifts p < p)
    (hlocal : ∀ p : ℕ, localNu shifts p ≤ 2)
    (hpow : (((z + 1 : ℕ) : ℝ) ^ 18) ≤
      eta * (2 : ℝ) ^ (L + 1)) :
    Erdos387.brunSubsetTail
        (Erdos387.sievePrimeProduct 1 z).primeFactors
        (fun p ↦ shiftNu shifts p) L ≤
      eta * Erdos387.finiteEulerProduct
        (Erdos387.sievePrimeProduct 1 z).primeFactors
        (fun p ↦ shiftNu shifts p) := by
  let P := (Erdos387.sievePrimeProduct 1 z).primeFactors
  let V := Erdos387.finiteEulerProduct P (fun p ↦ shiftNu shifts p)
  let T := Erdos387.brunSubsetTail P (fun p ↦ shiftNu shifts p) L
  have hV : 0 ≤ V := by
    unfold V Erdos387.finiteEulerProduct
    apply Finset.prod_nonneg
    intro p hpP
    have hp := Nat.prime_of_mem_primeFactors hpP
    change 0 ≤ 1 - shiftNu shifts p
    rw [shiftNu_prime hp]
    have hpMem := Erdos387.mem_sievePrimes.mp
      (Erdos387.prime_mem_sievePrimes_of_dvd_product hp
        (Nat.dvd_of_mem_primeFactors hpP))
    exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast hp.pos)).mpr
      (by exact_mod_cast (hadmissible p hp hpMem.2.2).le))
  have htail := Erdos387.pow_two_mul_brunSubsetTail_le
    P (fun p ↦ shiftNu shifts p) L (by
      intro p hpP
      rw [shiftNu_prime (Nat.prime_of_mem_primeFactors hpP)]
      positivity)
  have hmoment := shiftMomentProduct_le_poly_mul_euler
    hadmissible hlocal
  have hpowpos : 0 < (2 : ℝ) ^ (L + 1) := by positivity
  change T ≤ eta * V
  apply (mul_le_mul_iff_of_pos_left hpowpos).mp
  calc
    (2 : ℝ) ^ (L + 1) * T ≤
        ∏ p ∈ P, (1 + 2 * shiftNu shifts p) := htail
    _ ≤ (((z + 1 : ℕ) : ℝ) ^ 18) * V := by
      simpa [P, V] using hmoment
    _ ≤ (eta * (2 : ℝ) ^ (L + 1)) * V :=
      mul_le_mul_of_nonneg_right hpow hV
    _ = (2 : ℝ) ^ (L + 1) * (eta * V) := by ring

end FullShiftSieve

/-! ## The exact ordinary-difference correction average -/

/-- Sum of the positive triangular weights supported on multiples of `q`.
This is the floor estimate behind the mean-one pair correction. -/
lemma triangular_multiples_le (K q : ℕ) (hq : 0 < q) :
    2 * (∑ d ∈ (Finset.Ico 1 K).filter (q ∣ ·), (K - d : ℝ)) ≤
      (K : ℝ) ^ 2 / q := by
  let n := (K - 1) / q
  have hset : (Finset.Ico 1 K).filter (q ∣ ·) =
      (Finset.Ioc 0 n).image (fun b ↦ q * b) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hd1, hdK⟩, hdvd⟩
      obtain ⟨b, rfl⟩ := hdvd
      refine ⟨b, ?_, rfl⟩
      constructor
      · by_contra hb
        simp only [Nat.not_lt, Nat.le_zero] at hb
        subst b
        simp at hd1
      · apply (Nat.le_div_iff_mul_le hq).2
        rw [Nat.mul_comm]
        omega
    · rintro ⟨b, ⟨hb0, hbn⟩, rfl⟩
      have hmul : q * b ≤ K - 1 := by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).1 hbn
      constructor
      · constructor
        · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hq.ne' hb0.ne')
        · have hmul' : b * q ≤ K - 1 := by simpa [Nat.mul_comm] using hmul
          have hprodpos : 0 < b * q := Nat.mul_pos hb0 hq
          have hKpos : 0 < K := hprodpos.trans_le (hmul'.trans (Nat.sub_le K 1))
          simpa [Nat.mul_comm] using
            hmul'.trans_lt (Nat.sub_lt hKpos (by norm_num))
      · exact dvd_mul_right q b
  have hinj : Set.InjOn (fun b : ℕ ↦ q * b) (↑(Finset.Ioc 0 n) : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hq hab
  rw [hset, Finset.sum_image hinj]
  have hsumCast :
      (∑ b ∈ Finset.Ioc 0 n, (b : ℝ)) =
        (n : ℝ) * (n + 1 : ℕ) / 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hIoc : Finset.Ioc 0 (n + 1) =
            insert (n + 1) (Finset.Ioc 0 n) := by
          ext b
          simp only [Finset.mem_Ioc, Finset.mem_insert]
          omega
        rw [hIoc, Finset.sum_insert (by simp), ih]
        push_cast
        ring
  have hsum :
      (∑ b ∈ Finset.Ioc 0 n, ((K : ℝ) - (q * b : ℕ))) =
        (n : ℝ) * K - (q : ℝ) * ((n : ℝ) * (n + 1 : ℕ) / 2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp_rw [Nat.cast_mul]
    rw [← Finset.mul_sum, hsumCast]
    have hcard : (Finset.Ioc 0 n).card = n := by simp
    rw [hcard]
    simp only [Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul]
  simpa only [Nat.cast_mul] using (show
    2 * (∑ b ∈ Finset.Ioc 0 n, ((K : ℝ) - (q * b : ℕ))) ≤
        (K : ℝ) ^ 2 / q by
    rw [hsum]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    rw [le_div_iff₀ hqR]
    have hnq : (n : ℝ) * q ≤ K := by
      exact_mod_cast (show n * q ≤ K by
        dsimp [n]
        exact (Nat.div_mul_le_self (K - 1) q).trans (Nat.sub_le K 1))
    have hn : (0 : ℝ) ≤ n := by positivity
    have hq0 : (0 : ℝ) ≤ q := hqR.le
    have hsquare : 0 ≤ ((K : ℝ) - (n : ℝ) * q) ^ 2 := sq_nonneg _
    norm_num [Nat.cast_add] at ⊢
    nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) hn])

noncomputable def pairCorrectionBase (p : ℕ) : ℝ :=
  1 - (((p : ℝ) - 1) ^ 2)⁻¹

noncomputable def pairCorrectionBump (p : ℕ) : ℝ :=
  (p : ℝ) / ((p : ℝ) - 1) ^ 2

lemma pairDirectCorrection_eq_bump_add_base {h p : ℕ} (hp2 : 2 < p) :
    Erdos851.pairDirectCorrection h p =
      (if p ∣ h then pairCorrectionBump p else 0) + pairCorrectionBase p := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpm1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  simp only [Erdos851.pairDirectCorrection, pairCorrectionBump,
    pairCorrectionBase]
  split_ifs
  · field_simp [hp0, hpm1]
    ring
  · ring

lemma pairCorrectionBase_nonneg {p : ℕ} (hp2 : 2 < p) :
    0 ≤ pairCorrectionBase p := by
  have h := Erdos851.pairDirectCorrection_nonneg (h := 1) hp2
  have hpnot : ¬p ∣ 1 := by
    intro hp
    exact (by omega : p ≠ 1) (Nat.dvd_one.mp hp)
  simpa [Erdos851.pairDirectCorrection, hpnot, pairCorrectionBase] using h

lemma pairCorrectionBump_nonneg (p : ℕ) : 0 ≤ pairCorrectionBump p := by
  unfold pairCorrectionBump
  positivity

lemma pairCorrection_expectedLocal {p : ℕ} (hp2 : 2 < p) :
    pairCorrectionBump p / p + pairCorrectionBase p = 1 := by
  have hpR : (0 : ℝ) < p := by positivity
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    positivity
  unfold pairCorrectionBump pairCorrectionBase
  field_simp [hpR.ne', hpm1]
  ring

lemma prod_bumpIndicator_eq
    {T : Finset ℕ} (hprime : ∀ p ∈ T, p.Prime) (d : ℕ) :
    (∏ p ∈ T, if p ∣ d then pairCorrectionBump p else 0) =
      if (∏ p ∈ T, p) ∣ d then
        ∏ p ∈ T, pairCorrectionBump p else 0 := by
  by_cases hprod : (∏ p ∈ T, p) ∣ d
  · rw [if_pos hprod]
    apply Finset.prod_congr rfl
    intro p hp
    have hpd : p ∣ d := (Finset.dvd_prod_of_mem id hp).trans hprod
    simp [hpd]
  · rw [if_neg hprod]
    have hnall : ¬∀ p ∈ T, p ∣ d := by
      intro hall
      exact hprod (Finset.prod_primes_dvd d
        (fun p hp ↦ (hprime p hp).prime) hall)
    push_neg at hnall
    obtain ⟨p, hpT, hpd⟩ := hnall
    apply Finset.prod_eq_zero hpT
    rw [if_neg hpd]

lemma pairCorrection_coeff_sum_eq_one
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (hp2 : ∀ p ∈ P, 2 < p) :
    (∑ T ∈ P.powerset,
        ((∏ p ∈ T, pairCorrectionBump p) /
          ((∏ p ∈ T, p : ℕ) : ℝ)) *
        ∏ p ∈ P \ T, pairCorrectionBase p) = 1 := by
  have hquot (T : Finset ℕ) (hT : T ⊆ P) :
      (∏ p ∈ T, pairCorrectionBump p) /
          ((∏ p ∈ T, p : ℕ) : ℝ) =
        ∏ p ∈ T, (pairCorrectionBump p / p) := by
    rw [Nat.cast_prod, Finset.prod_div_distrib]
  calc
    (∑ T ∈ P.powerset,
        ((∏ p ∈ T, pairCorrectionBump p) /
          ((∏ p ∈ T, p : ℕ) : ℝ)) *
        ∏ p ∈ P \ T, pairCorrectionBase p) =
        ∑ T ∈ P.powerset,
          (∏ p ∈ T, pairCorrectionBump p / p) *
            ∏ p ∈ P \ T, pairCorrectionBase p := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [hquot T (Finset.mem_powerset.mp hT)]
    _ = ∏ p ∈ P,
          (pairCorrectionBump p / p + pairCorrectionBase p) :=
      (Finset.prod_add _ _ P).symm
    _ = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      exact pairCorrection_expectedLocal (hp2 p hp)

lemma pairCorrectionProduct_eq_subsetSum
    (P : Finset ℕ) (hp2 : ∀ p ∈ P, 2 < p) (d : ℕ) :
    (∏ p ∈ P, Erdos851.pairDirectCorrection d p) =
      ∑ T ∈ P.powerset,
        (∏ p ∈ T, if p ∣ d then pairCorrectionBump p else 0) *
          ∏ p ∈ P \ T, pairCorrectionBase p := by
  calc
    (∏ p ∈ P, Erdos851.pairDirectCorrection d p) =
        ∏ p ∈ P,
          ((if p ∣ d then pairCorrectionBump p else 0) +
            pairCorrectionBase p) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact pairDirectCorrection_eq_bump_add_base (hp2 p hp)
    _ = _ := Finset.prod_add _ _ P

lemma weighted_bumpIndicator_le
    (T : Finset ℕ) (hprime : ∀ p ∈ T, p.Prime) (K : ℕ) :
    2 * (∑ d ∈ Finset.Ico 1 K, (K - d : ℝ) *
        ∏ p ∈ T, if p ∣ d then pairCorrectionBump p else 0) ≤
      (K : ℝ) ^ 2 *
        ((∏ p ∈ T, pairCorrectionBump p) /
          ((∏ p ∈ T, p : ℕ) : ℝ)) := by
  let q := ∏ p ∈ T, p
  let B := ∏ p ∈ T, pairCorrectionBump p
  have hq : 0 < q := by
    dsimp [q]
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.prod_nonneg fun p hp ↦ pairCorrectionBump_nonneg p
  have hrewrite :
      2 * (∑ d ∈ Finset.Ico 1 K, (K - d : ℝ) *
          ∏ p ∈ T, if p ∣ d then pairCorrectionBump p else 0) =
        B * (2 * ∑ d ∈ (Finset.Ico 1 K).filter (q ∣ ·), (K - d : ℝ)) := by
    simp_rw [prod_bumpIndicator_eq hprime]
    dsimp only [q, B]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hrewrite]
  calc
    B * (2 * ∑ d ∈ (Finset.Ico 1 K).filter (q ∣ ·), (K - d : ℝ)) ≤
        B * ((K : ℝ) ^ 2 / q) :=
      mul_le_mul_of_nonneg_left (triangular_multiples_le K q hq) hB
    _ = (K : ℝ) ^ 2 * (B / q) := by ring
    _ = _ := rfl

/-- The exact pair correction has mean at most one against the ordered
triangular difference weights. -/
theorem pairCorrection_triangular_sum_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hp2 : ∀ p ∈ P, 2 < p) (K : ℕ) :
    2 * (∑ d ∈ Finset.Ico 1 K, (K - d : ℝ) *
        ∏ p ∈ P, Erdos851.pairDirectCorrection d p) ≤ (K : ℝ) ^ 2 := by
  have hrewrite :
      2 * (∑ d ∈ Finset.Ico 1 K, (K - d : ℝ) *
          ∏ p ∈ P, Erdos851.pairDirectCorrection d p) =
        ∑ T ∈ P.powerset,
          (∏ p ∈ P \ T, pairCorrectionBase p) *
            (2 * (∑ d ∈ Finset.Ico 1 K, (K - d : ℝ) *
              ∏ p ∈ T,
                if p ∣ d then pairCorrectionBump p else 0)) := by
    simp_rw [pairCorrectionProduct_eq_subsetSum P hp2]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hrewrite]
  calc
    (∑ T ∈ P.powerset,
        (∏ p ∈ P \ T, pairCorrectionBase p) *
          (2 * (∑ d ∈ Finset.Ico 1 K, (K - d : ℝ) *
            ∏ p ∈ T,
              if p ∣ d then pairCorrectionBump p else 0))) ≤
        ∑ T ∈ P.powerset,
          (∏ p ∈ P \ T, pairCorrectionBase p) *
            ((K : ℝ) ^ 2 *
              ((∏ p ∈ T, pairCorrectionBump p) /
                ((∏ p ∈ T, p : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro T hT
      apply mul_le_mul_of_nonneg_left
      · apply weighted_bumpIndicator_le T
        intro p hp
        exact hprime p (Finset.mem_powerset.mp hT hp)
      · apply Finset.prod_nonneg
        intro p hp
        exact pairCorrectionBase_nonneg
          (hp2 p (Finset.sdiff_subset hp))
    _ = (K : ℝ) ^ 2 *
        (∑ T ∈ P.powerset,
          ((∏ p ∈ T, pairCorrectionBump p) /
            ((∏ p ∈ T, p : ℕ) : ℝ)) *
              ∏ p ∈ P \ T, pairCorrectionBase p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      ring
    _ = (K : ℝ) ^ 2 := by
      rw [pairCorrection_coeff_sum_eq_one P hprime hp2, mul_one]

/-- An unweighted initial segment of the ordinary-difference correction
has uniformly bounded mean. -/
theorem pairCorrection_Icc_four_mul_le_eight_mul
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hp2 : ∀ p ∈ P, 2 < p) {H : ℕ} (hH : 0 < H) :
    (∑ d ∈ Finset.Icc 1 (4 * H),
        ∏ p ∈ P, Erdos851.pairDirectCorrection d p) ≤ (8 * H : ℕ) := by
  let C : ℕ → ℝ := fun d ↦
    ∏ p ∈ P, Erdos851.pairDirectCorrection d p
  have hC (d : ℕ) : 0 ≤ C d := by
    dsimp [C]
    exact Finset.prod_nonneg fun p hp ↦
      Erdos851.pairDirectCorrection_nonneg (hp2 p hp)
  have hsub : Finset.Icc 1 (4 * H) ⊆ Finset.Ico 1 (8 * H) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [Finset.mem_Ico]
    omega
  have hone :
      (∑ d ∈ Finset.Icc 1 (4 * H), (4 * (H : ℝ)) * C d) ≤
        ∑ d ∈ Finset.Icc 1 (4 * H), (8 * H - d : ℝ) * C d := by
    apply Finset.sum_le_sum
    intro d hd
    have hd' := Finset.mem_Icc.mp hd
    have hw : (4 * H : ℝ) ≤ 8 * H - d := by
      have hdR : (d : ℝ) ≤ 4 * H := by exact_mod_cast hd'.2
      norm_num [Nat.cast_mul] at hdR ⊢
      linarith
    exact mul_le_mul_of_nonneg_right hw (hC d)
  have htwo :
      (∑ d ∈ Finset.Icc 1 (4 * H), (8 * H - d : ℝ) * C d) ≤
        ∑ d ∈ Finset.Ico 1 (8 * H), (8 * H - d : ℝ) * C d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro d hdBig hdSmall
    exact mul_nonneg (by
      have hd := Finset.mem_Ico.mp hdBig
      exact sub_nonneg.mpr (by exact_mod_cast hd.2.le)) (hC d)
  have htri := pairCorrection_triangular_sum_le P hprime hp2 (8 * H)
  have hmul :
      (8 * H : ℝ) * (∑ d ∈ Finset.Icc 1 (4 * H), C d) ≤
        (8 * H : ℝ) ^ 2 := by
    calc
      (8 * H : ℝ) * (∑ d ∈ Finset.Icc 1 (4 * H), C d) =
          2 * (∑ d ∈ Finset.Icc 1 (4 * H), (4 * (H : ℝ)) * C d) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        push_cast
        ring
      _ ≤ 2 * (∑ d ∈ Finset.Icc 1 (4 * H),
          (8 * H - d : ℝ) * C d) := mul_le_mul_of_nonneg_left hone (by norm_num)
      _ ≤ 2 * (∑ d ∈ Finset.Ico 1 (8 * H),
          (8 * H - d : ℝ) * C d) := mul_le_mul_of_nonneg_left htwo (by norm_num)
      _ ≤ (8 * H : ℝ) ^ 2 := by
        simpa only [C, Nat.cast_mul, Nat.cast_ofNat] using htri
  have hpos : (0 : ℝ) < 8 * H := by positivity
  have hcancel : (∑ d ∈ Finset.Icc 1 (4 * H), C d) ≤ (8 * H : ℝ) := by
    apply (mul_le_mul_iff_of_pos_left hpos).mp
    simpa only [pow_two] using hmul
  simpa only [C, Nat.cast_mul, Nat.cast_ofNat] using hcancel

/-- Odd-prime correction factors do not see the factor `2` in a
difference. -/
lemma pairDirectCorrection_two_mul {d p : ℕ} (hp : p.Prime)
    (hp2 : 2 < p) :
    Erdos851.pairDirectCorrection (2 * d) p =
      Erdos851.pairDirectCorrection d p := by
  have hdvd : p ∣ 2 * d ↔ p ∣ d := by
    constructor
    · intro h
      rcases hp.dvd_mul.mp h with htwo | hd
      · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) htwo
        omega
      · exact hd
    · intro hd
      exact dvd_mul_of_dvd_right hd 2
  simp only [Erdos851.pairDirectCorrection, hdvd]

lemma sum_range_reverse (f : ℕ → ℝ) (H : ℕ) :
    (∑ j ∈ Finset.range H, f (H - j)) =
      ∑ d ∈ Finset.Ioc 0 H, f d := by
  apply Finset.sum_bij'
      (fun j _ ↦ H - j) (fun d _ ↦ H - d)
  · intro j hj
    rw [Finset.mem_Ioc]
    have hjH := Finset.mem_range.mp hj
    omega
  · intro d hd
    rw [Finset.mem_range]
    have hd' := Finset.mem_Ioc.mp hd
    omega
  · intro j hj
    have hjH := Finset.mem_range.mp hj
    omega
  · intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    omega
  · intro j hj
    rfl

lemma triangularSum_succ (f : ℕ → ℝ) (H : ℕ) :
    (∑ d ∈ Finset.Ico 1 (H + 1), ((H + 1 - d : ℕ) : ℝ) * f d) =
      (∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * f d) +
        ∑ d ∈ Finset.Ioc 0 H, f d := by
  by_cases hH : H = 0
  · subst H
    simp
  have hHpos : 0 < H := Nat.pos_of_ne_zero hH
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ H)]
  have hinside :
      (∑ d ∈ Finset.Ico 1 H, ((H + 1 - d : ℕ) : ℝ) * f d) =
        (∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * f d) +
          ∑ d ∈ Finset.Ico 1 H, f d := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := Finset.mem_Ico.mp hd
    rw [show H + 1 - d = (H - d) + 1 by omega]
    push_cast
    ring
  rw [hinside]
  have hIoc : Finset.Ioc 0 H = insert H (Finset.Ico 1 H) := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_insert (by simp [hH])]
  simp
  ring

/-- Ordered unequal pairs from `[0,H)` are grouped by their positive
distance. -/
theorem ordered_dist_sum_eq_triangular (f : ℕ → ℝ) (H : ℕ) :
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        if i = j then 0 else f (Nat.dist i j)) =
      2 * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * f d := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ]
      simp_rw [Finset.sum_range_succ]
      have hcross₁ :
          (∑ i ∈ Finset.range H,
              (if i = H then 0 else f (Nat.dist i H))) =
            ∑ d ∈ Finset.Ioc 0 H, f d := by
        calc
          (∑ i ∈ Finset.range H,
              (if i = H then 0 else f (Nat.dist i H))) =
              ∑ i ∈ Finset.range H, f (H - i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiH := Finset.mem_range.mp hi
            rw [if_neg (by omega), Nat.dist_eq_sub_of_le (by omega)]
          _ = _ := sum_range_reverse f H
      have hcross₂ :
          (∑ j ∈ Finset.range H,
              (if H = j then 0 else f (Nat.dist H j))) =
            ∑ d ∈ Finset.Ioc 0 H, f d := by
        calc
          (∑ j ∈ Finset.range H,
              (if H = j then 0 else f (Nat.dist H j))) =
              ∑ j ∈ Finset.range H, f (H - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjH := Finset.mem_range.mp hj
            rw [if_neg (by omega), Nat.dist_eq_sub_of_le_right (by omega)]
          _ = _ := sum_range_reverse f H
      rw [Finset.sum_add_distrib]
      rw [hcross₁, hcross₂, ih, triangularSum_succ]
      simp only [if_true]
      ring

lemma sum_pair_diagonal_one { α : Type* } [DecidableEq α]
    (S : Finset α) :
    (∑ s ∈ S, ∑ t ∈ S, if s = t then (1 : ℝ) else 0) = S.card := by
  calc
    (∑ s ∈ S, ∑ t ∈ S, if s = t then (1 : ℝ) else 0) =
        ∑ _s ∈ S, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [hs]
    _ = S.card := by simp

lemma sum_pair_diagonal_const { α : Type* } [DecidableEq α]
    (S : Finset α) (B : ℝ) :
    (∑ s ∈ S, ∑ t ∈ S, if s = t then B else 0) =
      (S.card : ℝ) * B := by
  calc
    (∑ s ∈ S, ∑ t ∈ S, if s = t then B else 0) =
        ∑ _s ∈ S, B := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [hs]
    _ = (S.card : ℝ) * B := by simp

lemma sum_pair_mul { α : Type* } [DecidableEq α]
    (S : Finset α) (A : ℝ) (f : α → α → ℝ) :
    (∑ s ∈ S, ∑ t ∈ S, A * f s t) =
      A * ∑ s ∈ S, ∑ t ∈ S, f s t := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]

lemma sum_pair_if_diag { α : Type* } [DecidableEq α]
    (S : Finset α) (B A : ℝ) (f : α → α → ℝ) :
    (∑ s ∈ S, ∑ t ∈ S,
        if s = t then B else A * f s t) =
      (S.card : ℝ) * B + A *
        ∑ s ∈ S, ∑ t ∈ S, if s = t then 0 else f s t := by
  calc
    (∑ s ∈ S, ∑ t ∈ S,
        if s = t then B else A * f s t) =
        (∑ s ∈ S, ∑ t ∈ S,
          if s = t then B else 0) +
        ∑ s ∈ S, ∑ t ∈ S,
          A * (if s = t then 0 else f s t) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hst : s = t <;> simp [hst]
    _ = (S.card : ℝ) * B + A *
        ∑ s ∈ S, ∑ t ∈ S, if s = t then 0 else f s t := by
      rw [sum_pair_diagonal_const, sum_pair_mul]

lemma sum_pair_affine { α : Type* } [DecidableEq α]
    (S : Finset α) (A E : ℝ) (f : α → α → ℝ) :
    (∑ s ∈ S, ∑ t ∈ S, (A * f s t + E)) =
      A * (∑ s ∈ S, ∑ t ∈ S, f s t) +
        (S.card : ℝ) ^ 2 * E := by
  calc
    (∑ s ∈ S, ∑ t ∈ S, (A * f s t + E)) =
        (∑ s ∈ S, ∑ t ∈ S, A * f s t) +
          ∑ s ∈ S, ∑ _t ∈ S, E := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.sum_add_distrib]
    _ = A * (∑ s ∈ S, ∑ t ∈ S, f s t) +
        (S.card : ℝ) ^ 2 * E := by
      rw [sum_pair_mul]
      simp
      ring

/-- A block of equally spaced shifts.  The common parity is what makes the
full two-shift sieve admissible at the prime `2`. -/
def evenShifts (H : ℕ) : Finset ℕ :=
  (Finset.range H).image fun j ↦ 2 * j

/-- Reindex a sum over the even shift block by its half. -/
lemma sum_evenShifts_eq_range (f : ℕ → ℝ) (H : ℕ) :
    (∑ s ∈ evenShifts H, f s) = ∑ j ∈ Finset.range H, f (2 * j) := by
  rw [evenShifts, Finset.sum_image]
  intro i _hi j _hj hij
  change 2 * i = 2 * j at hij
  omega

@[simp] theorem evenShifts_card (H : ℕ) : (evenShifts H).card = H := by
  rw [evenShifts, Finset.card_image_of_injective (Finset.range H)]
  · exact Finset.card_range H
  · intro i j hij
    change 2 * i = 2 * j at hij
    omega

lemma evenShifts_nonempty {H : ℕ} (hH : 0 < H) :
    (evenShifts H).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have := congrArg Finset.card hempty
  simp [hH.ne'] at this

lemma evenShifts_le {H X s : ℕ} (hHX : 2 * H ≤ X)
    (hs : s ∈ evenShifts H) : s ≤ X := by
  rw [evenShifts, Finset.mem_image] at hs
  obtain ⟨j, hj, rfl⟩ := hs
  have hjH : j < H := Finset.mem_range.mp hj
  omega

lemma evenShifts_sameParity {H s t : ℕ}
    (hs : s ∈ evenShifts H) (ht : t ∈ evenShifts H) :
    s % 2 = t % 2 := by
  rw [evenShifts, Finset.mem_image] at hs ht
  obtain ⟨j, _hj, rfl⟩ := hs
  obtain ⟨k, _hk, rfl⟩ := ht
  simp

/-- The total off-diagonal direct-correction mass of the even shift block
is at most the square of its length. -/
theorem evenShifts_pairCorrection_offdiag_le (H z : ℕ) :
    (∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
        if s = t then 0 else
          ∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
            Erdos851.pairDirectCorrection (Nat.dist s t) p) ≤
      (H : ℝ) ^ 2 := by
  let P := Erdos851.sievePrimes 2 (z - 1)
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (Erdos851.mem_sievePrimes.mp hp).2.2
  have hp2 : ∀ p ∈ P, 2 < p := by
    intro p hp
    exact (Erdos851.mem_sievePrimes.mp hp).1
  rw [sum_evenShifts_eq_range]
  calc
    (∑ j ∈ Finset.range H, ∑ t ∈ evenShifts H,
        if 2 * j = t then 0 else
          ∏ p ∈ P,
            Erdos851.pairDirectCorrection (Nat.dist (2 * j) t) p) =
        ∑ j ∈ Finset.range H, ∑ k ∈ Finset.range H,
          if 2 * j = 2 * k then 0 else
            ∏ p ∈ P,
              Erdos851.pairDirectCorrection
                (Nat.dist (2 * j) (2 * k)) p := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sum_evenShifts_eq_range]
    _ = ∑ j ∈ Finset.range H, ∑ k ∈ Finset.range H,
          if j = k then 0 else
            ∏ p ∈ P,
              Erdos851.pairDirectCorrection (Nat.dist j k) p := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hjk : j = k
      · subst k
        simp
      · rw [if_neg (by omega), if_neg hjk, Nat.dist_mul_left]
        apply Finset.prod_congr rfl
        intro p hp
        exact pairDirectCorrection_two_mul (hprime p hp) (hp2 p hp)
    _ = 2 * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) *
          ∏ p ∈ P, Erdos851.pairDirectCorrection d p := by
      exact ordered_dist_sum_eq_triangular
        (fun d ↦ ∏ p ∈ P, Erdos851.pairDirectCorrection d p) H
    _ = 2 * ∑ d ∈ Finset.Ico 1 H, (H - d : ℝ) *
          ∏ p ∈ P, Erdos851.pairDirectCorrection d p := by
      apply congrArg (fun x : ℝ ↦ 2 * x)
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_sub (Finset.mem_Ico.mp hd).2.le]
    _ ≤ (H : ℝ) ^ 2 := pairCorrection_triangular_sum_le P hprime hp2 H

/-- Number of even shifts `0,2,...,2(H-1)` whose residual is `z`-rough.
The parity restriction incorporates the prime `2` without losing any rough
integers once `z>2`. -/
noncomputable def roughMultiplicity (z H a : ℕ) : ℕ := by
  classical
  exact ((evenShifts H).filter fun s ↦ IsRough z (a - s)).card

/-- First-moment expansion into singleton full-sieve counts. -/
theorem sum_roughMultiplicity_eq_singletonCounts (z H X : ℕ) :
    ∑ a ∈ Finset.Ioc X (2 * X), roughMultiplicity z H a =
      ∑ s ∈ evenShifts H, (FullShiftSieve.candidates {s} X z).card := by
  classical
  calc
    ∑ a ∈ Finset.Ioc X (2 * X), roughMultiplicity z H a =
        ∑ a ∈ Finset.Ioc X (2 * X),
          ∑ s ∈ evenShifts H, if IsRough z (a - s) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [roughMultiplicity, Finset.card_eq_sum_ones,
        Finset.sum_filter]
    _ = ∑ s ∈ evenShifts H,
          ∑ a ∈ Finset.Ioc X (2 * X),
            if IsRough z (a - s) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ s ∈ evenShifts H,
          (FullShiftSieve.candidates {s} X z).card := by
      apply Finset.sum_congr rfl
      intro s hs
      have hcandidates : FullShiftSieve.candidates {s} X z =
          (Finset.Ioc X (2 * X)).filter fun a ↦ IsRough z (a - s) := by
        ext a
        rw [FullShiftSieve.mem_candidates_iff]
        simp
      rw [hcandidates, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Pointwise square expansion of the rough multiplicity. -/
theorem roughMultiplicity_sq_eq_pairSum (z H a : ℕ) :
    roughMultiplicity z H a ^ 2 =
      ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
        if IsRough z (a - s) ∧ IsRough z (a - t) then 1 else 0 := by
  classical
  let F := (evenShifts H).filter fun s ↦ IsRough z (a - s)
  have hproduct : F ×ˢ F =
      ((evenShifts H) ×ˢ (evenShifts H)).filter fun st ↦
        IsRough z (a - st.1) ∧ IsRough z (a - st.2) := by
    ext st
    simp [F]
    tauto
  calc
    roughMultiplicity z H a ^ 2 = F.card ^ 2 := by
      simp only [roughMultiplicity, F]
    _ = (F ×ˢ F).card := by simp [pow_two]
    _ = (((evenShifts H) ×ˢ (evenShifts H)).filter fun st ↦
        IsRough z (a - st.1) ∧ IsRough z (a - st.2)).card := by
      rw [hproduct]
    _ = ∑ st ∈ (evenShifts H) ×ˢ (evenShifts H),
        if IsRough z (a - st.1) ∧ IsRough z (a - st.2)
          then 1 else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
        if IsRough z (a - s) ∧ IsRough z (a - t) then 1 else 0 := by
      simp only [Finset.sum_product]

/-- Second-moment expansion into pair full-sieve counts. -/
theorem sum_roughMultiplicity_sq_eq_pairCounts (z H X : ℕ) :
    ∑ a ∈ Finset.Ioc X (2 * X), roughMultiplicity z H a ^ 2 =
      ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
        (FullShiftSieve.candidates {s, t} X z).card := by
  classical
  calc
    ∑ a ∈ Finset.Ioc X (2 * X), roughMultiplicity z H a ^ 2 =
        ∑ a ∈ Finset.Ioc X (2 * X),
          ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
            if IsRough z (a - s) ∧ IsRough z (a - t) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact roughMultiplicity_sq_eq_pairSum z H a
    _ = ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
          ∑ a ∈ Finset.Ioc X (2 * X),
            if IsRough z (a - s) ∧ IsRough z (a - t) then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
    _ = ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
          (FullShiftSieve.candidates {s, t} X z).card := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      have hcandidates : FullShiftSieve.candidates {s, t} X z =
          (Finset.Ioc X (2 * X)).filter fun a ↦
            IsRough z (a - s) ∧ IsRough z (a - t) := by
        ext a
        rw [FullShiftSieve.mem_candidates_iff]
        simp [and_comm, and_left_comm, and_assoc]
      rw [hcandidates, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Exact full inclusion--exclusion gives the first-moment lower bound for
the even shift block. -/
theorem roughMultiplicity_firstMoment_lower {X H z : ℕ}
    (hH : 0 < H) (hHX : 2 * H ≤ X) :
    (H : ℝ) * ((X : ℝ) * FullShiftSieve.roughEulerMass z -
        (4 : ℝ) ^
          (Erdos387.sievePrimeProduct 1 z).primeFactors.card) ≤
      ∑ a ∈ Finset.Ioc X (2 * X), (roughMultiplicity z H a : ℝ) := by
  have hsbound (s : ℕ) (hs : s ∈ evenShifts H) :
      (X : ℝ) * FullShiftSieve.roughEulerMass z -
          (4 : ℝ) ^
            (Erdos387.sievePrimeProduct 1 z).primeFactors.card ≤
        ((FullShiftSieve.candidates {s} X z).card : ℝ) := by
    have h := FullShiftSieve.lower_cardinality_bound
      (shifts := ({s} : Finset ℕ)) (hshifts := by simp)
      (X := X) (z := z) (hadmissible := FullShiftSieve.singleton_admissible s z)
      (fun q hq ↦ by
        simp only [Finset.mem_singleton] at hq
        subst q
        exact evenShifts_le hHX hs)
      (fun p ↦ by rw [Erdos851.ShiftSieve.localNu_singleton]; omega)
    rw [FullShiftSieve.singletonEulerMass] at h
    exact h
  calc
    (H : ℝ) * ((X : ℝ) * FullShiftSieve.roughEulerMass z -
        (4 : ℝ) ^
          (Erdos387.sievePrimeProduct 1 z).primeFactors.card) =
        ∑ _s ∈ evenShifts H,
          ((X : ℝ) * FullShiftSieve.roughEulerMass z -
            (4 : ℝ) ^
              (Erdos387.sievePrimeProduct 1 z).primeFactors.card) := by
      rw [Finset.sum_const, evenShifts_card]
      simp only [nsmul_eq_mul]
    _ ≤ ∑ s ∈ evenShifts H,
          ((FullShiftSieve.candidates {s} X z).card : ℝ) := by
      exact Finset.sum_le_sum fun s hs ↦ hsbound s hs
    _ = ∑ a ∈ Finset.Ioc X (2 * X),
          (roughMultiplicity z H a : ℝ) := by
      exact_mod_cast
        (sum_roughMultiplicity_eq_singletonCounts z H X).symm

/-- A single diagonal pair costs at most the interval length, while an
off-diagonal same-parity pair is controlled by its exact two-shift Euler
mass and the common full-inclusion endpoint error. -/
lemma pairCandidates_upper {X H z s t : ℕ} (hz : 3 ≤ z)
    (hHX : 2 * H ≤ X) (hs : s ∈ evenShifts H) (ht : t ∈ evenShifts H) :
    ((FullShiftSieve.candidates {s, t} X z).card : ℝ) ≤
      (X : ℝ) *
        (if s = t then FullShiftSieve.roughEulerMass z else
          2 * FullShiftSieve.roughEulerMass z ^ 2 *
            ∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
              Erdos851.pairDirectCorrection (Nat.dist s t) p) +
        (4 : ℝ) ^
          (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
  by_cases hst : s = t
  · subst t
    have h := FullShiftSieve.upper_cardinality_bound
      (shifts := ({s} : Finset ℕ)) (hshifts := by simp)
      (X := X) (z := z) (hadmissible := FullShiftSieve.singleton_admissible s z)
      (fun q hq ↦ by
        simp only [Finset.mem_singleton] at hq
        subst q
        exact evenShifts_le hHX hs)
      (fun p ↦ by rw [Erdos851.ShiftSieve.localNu_singleton]; omega)
    rw [FullShiftSieve.singletonEulerMass] at h
    simpa using h
  · have hshiftX : ∀ q ∈ ({s, t} : Finset ℕ), q ≤ X := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact evenShifts_le hHX hs
      · exact evenShifts_le hHX ht
    have hparity := evenShifts_sameParity hs ht
    have h := FullShiftSieve.upper_cardinality_bound
      (shifts := ({s, t} : Finset ℕ)) (hshifts := by simp)
      (X := X) (z := z)
      (hadmissible := FullShiftSieve.pair_admissible_of_sameParity hparity)
      hshiftX (fun p ↦ Erdos851.ShiftSieve.localNu_pair_le_two s t p)
    change ((FullShiftSieve.candidates {s, t} X z).card : ℝ) ≤
      (X : ℝ) * FullShiftSieve.pairEulerMass s t z +
        (4 : ℝ) ^
          (Erdos387.sievePrimeProduct 1 z).primeFactors.card at h
    rw [FullShiftSieve.pairEulerMass_eq_two_mul_sq_mul_correction
      hz hparity] at h
    simpa only [if_neg hst] using h

/-- The resulting explicit second-moment bound.  The diagonal contributes
`H X V(z)`; the exact ordinary-difference average bounds the off-diagonal main
term by `2 X H² V(z)²`; full inclusion--exclusion contributes the final
`H² 4^r` endpoint term. -/
theorem roughMultiplicity_secondMoment_upper {X H z : ℕ}
    (hz : 3 ≤ z) (hHX : 2 * H ≤ X) :
    (∑ a ∈ Finset.Ioc X (2 * X),
        ((roughMultiplicity z H a ^ 2 : ℕ) : ℝ)) ≤
      (X : ℝ) *
          ((H : ℝ) * FullShiftSieve.roughEulerMass z +
            2 * FullShiftSieve.roughEulerMass z ^ 2 *
            (H : ℝ) ^ 2) +
        (H : ℝ) ^ 2 *
          (4 : ℝ) ^
            (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
  let C : ℕ → ℕ → ℝ := fun s t ↦
    ∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
      Erdos851.pairDirectCorrection (Nat.dist s t) p
  let O : ℝ := ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
    if s = t then 0 else C s t
  have hO : O ≤ (H : ℝ) ^ 2 := by
    dsimp only [O, C]
    exact evenShifts_pairCorrection_offdiag_le H z
  have hmain :
      (∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
          if s = t then FullShiftSieve.roughEulerMass z else
            (2 * FullShiftSieve.roughEulerMass z ^ 2) * C s t) =
        (H : ℝ) * FullShiftSieve.roughEulerMass z +
          2 * FullShiftSieve.roughEulerMass z ^ 2 * O := by
    rw [sum_pair_if_diag, evenShifts_card]
  calc
    (∑ a ∈ Finset.Ioc X (2 * X),
        ((roughMultiplicity z H a ^ 2 : ℕ) : ℝ)) =
        ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
          ((FullShiftSieve.candidates {s, t} X z).card : ℝ) := by
      exact_mod_cast sum_roughMultiplicity_sq_eq_pairCounts z H X
    _ ≤ ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
        ((X : ℝ) *
          (if s = t then FullShiftSieve.roughEulerMass z else
            (2 * FullShiftSieve.roughEulerMass z ^ 2) * C s t) +
          (4 : ℝ) ^
            (Erdos387.sievePrimeProduct 1 z).primeFactors.card) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro t ht
      simpa only [C, mul_assoc] using pairCandidates_upper hz hHX hs ht
    _ = (X : ℝ) *
          ((H : ℝ) * FullShiftSieve.roughEulerMass z +
            2 * FullShiftSieve.roughEulerMass z ^ 2 * O) +
        (H : ℝ) ^ 2 *
          (4 : ℝ) ^
            (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
      rw [sum_pair_affine, hmain, evenShifts_card]
    _ ≤ (X : ℝ) *
          ((H : ℝ) * FullShiftSieve.roughEulerMass z +
            2 * FullShiftSieve.roughEulerMass z ^ 2 *
            (H : ℝ) ^ 2) +
        (H : ℝ) ^ 2 *
          (4 : ℝ) ^
            (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
      have hX : (0 : ℝ) ≤ X := by positivity
      have hV : 0 ≤ 2 * FullShiftSieve.roughEulerMass z ^ 2 := by positivity
      gcongr

/-! ### Truncated-Brun versions of the rough-number moments -/

theorem roughMultiplicity_firstMoment_lower_brun
    {X H z L : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta) (hL : Odd L) (hz : 1 ≤ z)
    (hH : 0 < H) (hHX : 2 * H ≤ X)
    (hpow : (((z + 1 : ℕ) : ℝ) ^ 18) ≤
      eta * (2 : ℝ) ^ (L + 1)) :
    (H : ℝ) * ((X : ℝ) *
          ((1 - eta) * FullShiftSieve.roughEulerMass z) -
        FullShiftSieve.brunEndpointError z L) ≤
      ∑ a ∈ Finset.Ioc X (2 * X), (roughMultiplicity z H a : ℝ) := by
  have hsbound (s : ℕ) (hs : s ∈ evenShifts H) :
      (X : ℝ) * ((1 - eta) * FullShiftSieve.roughEulerMass z) -
          FullShiftSieve.brunEndpointError z L ≤
        ((FullShiftSieve.candidates {s} X z).card : ℝ) := by
    let T := Erdos387.brunSubsetTail
      (Erdos387.sievePrimeProduct 1 z).primeFactors
      (fun p ↦ Erdos851.ShiftSieve.shiftNu ({s} : Finset ℕ) p) L
    have htail : T ≤ eta * FullShiftSieve.roughEulerMass z := by
      have h := FullShiftSieve.brunSubsetTail_le_eta_mul_euler
        (shifts := ({s} : Finset ℕ)) heta
        (FullShiftSieve.singleton_admissible s z)
        (fun p ↦ by rw [Erdos851.ShiftSieve.localNu_singleton]; omega)
        hpow
      rw [FullShiftSieve.singletonEulerMass] at h
      exact h
    have hcard := FullShiftSieve.lower_cardinality_bound_brun
      (shifts := ({s} : Finset ℕ)) (hshifts := by simp)
      (X := X) (z := z) (L := L)
      (hadmissible := FullShiftSieve.singleton_admissible s z)
      hz hL (fun q hq ↦ by
        simp only [Finset.mem_singleton] at hq
        subst q
        exact evenShifts_le hHX hs)
      (fun p ↦ by rw [Erdos851.ShiftSieve.localNu_singleton]; omega)
    rw [FullShiftSieve.singletonEulerMass] at hcard
    dsimp only [T] at htail
    have hXnonneg : (0 : ℝ) ≤ X := by positivity
    calc
      (X : ℝ) * ((1 - eta) * FullShiftSieve.roughEulerMass z) -
            FullShiftSieve.brunEndpointError z L =
          (X : ℝ) * (FullShiftSieve.roughEulerMass z -
            eta * FullShiftSieve.roughEulerMass z) -
              FullShiftSieve.brunEndpointError z L := by ring
      _ ≤ (X : ℝ) * (FullShiftSieve.roughEulerMass z - T) -
            FullShiftSieve.brunEndpointError z L := by
        gcongr
      _ ≤ ((FullShiftSieve.candidates {s} X z).card : ℝ) := hcard
  calc
    (H : ℝ) * ((X : ℝ) *
          ((1 - eta) * FullShiftSieve.roughEulerMass z) -
        FullShiftSieve.brunEndpointError z L) =
        ∑ _s ∈ evenShifts H,
          ((X : ℝ) * ((1 - eta) * FullShiftSieve.roughEulerMass z) -
            FullShiftSieve.brunEndpointError z L) := by
      rw [Finset.sum_const, evenShifts_card]
      simp only [nsmul_eq_mul]
    _ ≤ ∑ s ∈ evenShifts H,
        ((FullShiftSieve.candidates {s} X z).card : ℝ) :=
      Finset.sum_le_sum fun s hs ↦ hsbound s hs
    _ = ∑ a ∈ Finset.Ioc X (2 * X),
        (roughMultiplicity z H a : ℝ) := by
      exact_mod_cast (sum_roughMultiplicity_eq_singletonCounts z H X).symm

lemma pairCandidates_upper_brun
    {X H z L s t : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta) (hL : Even L) (hz : 3 ≤ z)
    (hHX : 2 * H ≤ X) (hs : s ∈ evenShifts H)
    (ht : t ∈ evenShifts H)
    (hpow : (((z + 1 : ℕ) : ℝ) ^ 18) ≤
      eta * (2 : ℝ) ^ (L + 1)) :
    ((FullShiftSieve.candidates {s, t} X z).card : ℝ) ≤
      (X : ℝ) * (1 + eta) *
        (if s = t then FullShiftSieve.roughEulerMass z else
          2 * FullShiftSieve.roughEulerMass z ^ 2 *
            ∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
              Erdos851.pairDirectCorrection (Nat.dist s t) p) +
        FullShiftSieve.brunEndpointError z L := by
  by_cases hst : s = t
  · subst t
    have hshiftX : ∀ q ∈ ({s} : Finset ℕ), q ≤ X := by
      intro q hq
      simp only [Finset.mem_singleton] at hq
      subst q
      exact evenShifts_le hHX hs
    let T := Erdos387.brunSubsetTail
      (Erdos387.sievePrimeProduct 1 z).primeFactors
      (fun p ↦ Erdos851.ShiftSieve.shiftNu ({s} : Finset ℕ) p) L
    have htail : T ≤ eta * FullShiftSieve.roughEulerMass z := by
      have h := FullShiftSieve.brunSubsetTail_le_eta_mul_euler
        (shifts := ({s} : Finset ℕ)) heta
        (FullShiftSieve.singleton_admissible s z)
        (fun p ↦ by rw [Erdos851.ShiftSieve.localNu_singleton]; omega)
        hpow
      rw [FullShiftSieve.singletonEulerMass] at h
      exact h
    have hcard := FullShiftSieve.upper_cardinality_bound_brun
      (shifts := ({s} : Finset ℕ)) (hshifts := by simp)
      (X := X) (z := z) (L := L)
      (hadmissible := FullShiftSieve.singleton_admissible s z)
      (by omega) hL hshiftX
      (fun p ↦ by rw [Erdos851.ShiftSieve.localNu_singleton]; omega)
    rw [FullShiftSieve.singletonEulerMass] at hcard
    dsimp only [T] at htail
    have hXnonneg : (0 : ℝ) ≤ X := by positivity
    have hresult :
        ((FullShiftSieve.candidates {s} X z).card : ℝ) ≤
          (X : ℝ) * (1 + eta) * FullShiftSieve.roughEulerMass z +
            FullShiftSieve.brunEndpointError z L := by
      calc
      ((FullShiftSieve.candidates {s} X z).card : ℝ) ≤
          (X : ℝ) * (FullShiftSieve.roughEulerMass z + T) +
            FullShiftSieve.brunEndpointError z L := hcard
      _ ≤ (X : ℝ) * (1 + eta) * FullShiftSieve.roughEulerMass z +
            FullShiftSieve.brunEndpointError z L := by
        have := mul_le_mul_of_nonneg_left htail hXnonneg
        nlinarith
    simpa using hresult
  · have hshiftX : ∀ q ∈ ({s, t} : Finset ℕ), q ≤ X := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact evenShifts_le hHX hs
      · exact evenShifts_le hHX ht
    have hparity := evenShifts_sameParity hs ht
    let V := FullShiftSieve.pairEulerMass s t z
    let T := Erdos387.brunSubsetTail
      (Erdos387.sievePrimeProduct 1 z).primeFactors
      (fun p ↦ Erdos851.ShiftSieve.shiftNu ({s, t} : Finset ℕ) p) L
    have htail : T ≤ eta * V := by
      exact FullShiftSieve.brunSubsetTail_le_eta_mul_euler heta
        (FullShiftSieve.pair_admissible_of_sameParity hparity)
        (fun p ↦ Erdos851.ShiftSieve.localNu_pair_le_two s t p) hpow
    have hcard := FullShiftSieve.upper_cardinality_bound_brun
      (shifts := ({s, t} : Finset ℕ)) (hshifts := by simp)
      (X := X) (z := z) (L := L)
      (hadmissible := FullShiftSieve.pair_admissible_of_sameParity hparity)
      (by omega) hL hshiftX
      (fun p ↦ Erdos851.ShiftSieve.localNu_pair_le_two s t p)
    change ((FullShiftSieve.candidates {s, t} X z).card : ℝ) ≤
      (X : ℝ) * (V + T) + FullShiftSieve.brunEndpointError z L at hcard
    have hXnonneg : (0 : ℝ) ≤ X := by positivity
    dsimp only [V] at hcard htail
    rw [FullShiftSieve.pairEulerMass_eq_two_mul_sq_mul_correction
      hz hparity] at hcard htail
    simp only [if_neg hst]
    have := mul_le_mul_of_nonneg_left htail hXnonneg
    nlinarith

theorem roughMultiplicity_secondMoment_upper_brun
    {X H z L : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta) (hL : Even L) (hz : 3 ≤ z)
    (hHX : 2 * H ≤ X)
    (hpow : (((z + 1 : ℕ) : ℝ) ^ 18) ≤
      eta * (2 : ℝ) ^ (L + 1)) :
    (∑ a ∈ Finset.Ioc X (2 * X),
        ((roughMultiplicity z H a ^ 2 : ℕ) : ℝ)) ≤
      (X : ℝ) * (1 + eta) *
          ((H : ℝ) * FullShiftSieve.roughEulerMass z +
            2 * FullShiftSieve.roughEulerMass z ^ 2 * (H : ℝ) ^ 2) +
        (H : ℝ) ^ 2 * FullShiftSieve.brunEndpointError z L := by
  let C : ℕ → ℕ → ℝ := fun s t ↦
    ∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
      Erdos851.pairDirectCorrection (Nat.dist s t) p
  let O : ℝ := ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
    if s = t then 0 else C s t
  have hO : O ≤ (H : ℝ) ^ 2 := by
    dsimp only [O, C]
    exact evenShifts_pairCorrection_offdiag_le H z
  have hmain :
      (∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
          if s = t then FullShiftSieve.roughEulerMass z else
            (2 * FullShiftSieve.roughEulerMass z ^ 2) * C s t) =
        (H : ℝ) * FullShiftSieve.roughEulerMass z +
          2 * FullShiftSieve.roughEulerMass z ^ 2 * O := by
    rw [sum_pair_if_diag, evenShifts_card]
  calc
    (∑ a ∈ Finset.Ioc X (2 * X),
        ((roughMultiplicity z H a ^ 2 : ℕ) : ℝ)) =
        ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
          ((FullShiftSieve.candidates {s, t} X z).card : ℝ) := by
      exact_mod_cast sum_roughMultiplicity_sq_eq_pairCounts z H X
    _ ≤ ∑ s ∈ evenShifts H, ∑ t ∈ evenShifts H,
        ((X : ℝ) * (1 + eta) *
          (if s = t then FullShiftSieve.roughEulerMass z else
            (2 * FullShiftSieve.roughEulerMass z ^ 2) * C s t) +
          FullShiftSieve.brunEndpointError z L) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro t ht
      simpa only [C, mul_assoc] using
        pairCandidates_upper_brun heta hL hz hHX hs ht hpow
    _ = (X : ℝ) * (1 + eta) *
          ((H : ℝ) * FullShiftSieve.roughEulerMass z +
            2 * FullShiftSieve.roughEulerMass z ^ 2 * O) +
        (H : ℝ) ^ 2 * FullShiftSieve.brunEndpointError z L := by
      rw [sum_pair_affine, hmain, evenShifts_card]
    _ ≤ (X : ℝ) * (1 + eta) *
          ((H : ℝ) * FullShiftSieve.roughEulerMass z +
            2 * FullShiftSieve.roughEulerMass z ^ 2 * (H : ℝ) ^ 2) +
        (H : ℝ) ^ 2 * FullShiftSieve.brunEndpointError z L := by
      have hX : (0 : ℝ) ≤ X := by positivity
      have hetaOne : 0 ≤ 1 + eta := by linarith
      have hV : 0 ≤ 2 * FullShiftSieve.roughEulerMass z ^ 2 := by positivity
      gcongr

lemma lower_sq_le_card_pos_mul_upper
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : ι → ℕ) {L U : ℝ}
    (hL : 0 ≤ L)
    (hfirst : L ≤ ∑ i ∈ S, (R i : ℝ))
    (hsecond : (∑ i ∈ S, (R i : ℝ) ^ 2) ≤ U) :
    L ^ 2 ≤ ((S.filter fun i ↦ 0 < R i).card : ℝ) * U := by
  have hfilter :
      S.filter (fun i ↦ (R i : ℝ) ≠ 0) =
        S.filter fun i ↦ 0 < R i := by
    ext i
    simp [Nat.pos_iff_ne_zero]
  let T := S.filter fun i ↦ (R i : ℝ) ≠ 0
  have hsum : (∑ i ∈ T, (R i : ℝ)) = ∑ i ∈ S, (R i : ℝ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiS hiT
    simp only [Finset.mem_filter, hiS, true_and, not_not] at hiT
    exact_mod_cast hiT
  have hsumSq : (∑ i ∈ T, (R i : ℝ) ^ 2) =
      ∑ i ∈ S, (R i : ℝ) ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiS hiT
    simp only [Finset.mem_filter, hiS, true_and, not_not] at hiT
    simp [hiT]
  have hcs : (∑ i ∈ S, (R i : ℝ)) ^ 2 ≤
      ((S.filter fun i ↦ (R i : ℝ) ≠ 0).card : ℝ) *
        ∑ i ∈ S, (R i : ℝ) ^ 2 := by
    calc
      (∑ i ∈ S, (R i : ℝ)) ^ 2 =
          (∑ i ∈ T, (R i : ℝ)) ^ 2 := by rw [hsum]
      _ ≤ (T.card : ℝ) * ∑ i ∈ T, (R i : ℝ) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ = ((S.filter fun i ↦ (R i : ℝ) ≠ 0).card : ℝ) *
          ∑ i ∈ S, (R i : ℝ) ^ 2 := by rw [hsumSq]
  rw [hfilter] at hcs
  calc
    L ^ 2 ≤ (∑ i ∈ S, (R i : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hL hfirst 2
    _ ≤ ((S.filter fun i ↦ 0 < R i).card : ℝ) *
          ∑ i ∈ S, (R i : ℝ) ^ 2 := hcs
    _ ≤ ((S.filter fun i ↦ 0 < R i).card : ℝ) * U :=
      mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg _)

lemma one_sub_six_mul_le_positiveSupport
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : ι → ℕ)
    {η avg X : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 6)
    (havg : 0 < avg) (hlarge : 1 ≤ η * avg)
    (hX : 0 < X)
    (hfirst : (1 - η) * avg * X ≤ ∑ i ∈ S, (R i : ℝ))
    (hsecond : (∑ i ∈ S, (R i : ℝ) ^ 2) ≤
      (1 + 2 * η) * avg ^ 2 * X + avg * X) :
    (1 - 6 * η) * X ≤ ((S.filter fun i ↦ 0 < R i).card : ℝ) := by
  let L : ℝ := (1 - η) * avg * X
  let U : ℝ := (1 + 2 * η) * avg ^ 2 * X + avg * X
  have hL : 0 ≤ L := by
    dsimp [L]
    have : 0 ≤ 1 - η := by linarith
    positivity
  have hU : 0 < U := by
    dsimp [U]
    have hcoef : 0 < 1 + 2 * η := by linarith
    positivity
  have hpaley : L ^ 2 ≤
      ((S.filter fun i ↦ 0 < R i).card : ℝ) * U :=
    lower_sq_le_card_pos_mul_upper S R hL hfirst hsecond
  have havgAbsorb : avg ≤ η * avg ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hlarge havg.le]
  have hUbound : U ≤ (1 + 3 * η) * avg ^ 2 * X := by
    dsimp [U]
    nlinarith [mul_le_mul_of_nonneg_right havgAbsorb hX.le]
  have hcoef : (1 - 6 * η) * (1 + 3 * η) ≤ (1 - η) ^ 2 := by
    nlinarith [sq_nonneg η]
  have hnumeric : (1 - 6 * η) * X * U ≤ L ^ 2 := by
    have htarget : 0 ≤ 1 - 6 * η := by linarith
    calc
      (1 - 6 * η) * X * U ≤
          (1 - 6 * η) * X * ((1 + 3 * η) * avg ^ 2 * X) :=
        mul_le_mul_of_nonneg_left hUbound (mul_nonneg htarget hX.le)
      _ = ((1 - 6 * η) * (1 + 3 * η)) * avg ^ 2 * X ^ 2 := by ring
      _ ≤ (1 - η) ^ 2 * avg ^ 2 * X ^ 2 := by
        have havgSq :
            ((1 - 6 * η) * (1 + 3 * η)) * avg ^ 2 ≤
              (1 - η) ^ 2 * avg ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg avg)
        exact mul_le_mul_of_nonneg_right havgSq (sq_nonneg X)
      _ = L ^ 2 := by dsimp [L]; ring
  have hmul : (1 - 6 * η) * X * U ≤
      ((S.filter fun i ↦ 0 < R i).card : ℝ) * U :=
    hnumeric.trans hpaley
  exact (mul_le_mul_iff_of_pos_right hU).mp hmul

/-- Dyadic points hit by at least one rough residual from the even shift
block. -/
noncomputable def roughPositivePoints (X H z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X)).filter fun a ↦
    0 < roughMultiplicity z H a

/-- A finite Paley--Zygmund estimate specialized to the exact sieve moments
above.  The two displayed endpoint-error hypotheses are the only losses
from full inclusion--exclusion. -/
theorem roughPositivePoints_lower {X H z : ℕ} {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 6)
    (hX : 0 < X) (hH : 0 < H) (hz : 3 ≤ z) (hHX : 2 * H ≤ X)
    (hlarge : 1 ≤ η *
      (2 * (H : ℝ) * FullShiftSieve.roughEulerMass z))
    (herrFirst :
      (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card ≤
        η * (X : ℝ) * FullShiftSieve.roughEulerMass z)
    (herrSecond :
      (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card ≤
        4 * η * (X : ℝ) * FullShiftSieve.roughEulerMass z ^ 2) :
    (1 - 6 * η) * ((X : ℝ) / 2) ≤
      ((roughPositivePoints X H z).card : ℝ) := by
  let V := FullShiftSieve.roughEulerMass z
  let E : ℝ :=
    (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card
  let avg : ℝ := 2 * (H : ℝ) * V
  let halfX : ℝ := (X : ℝ) / 2
  have hlog : 0 < Real.log (z - 1 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < z - 1)
  have hV : 0 < V := by
    dsimp [V]
    exact (div_pos Erdos469.naturalLinearMertensLower_pos hlog).trans_le
      (FullShiftSieve.roughEulerMass_bounds hz).1
  have havg : 0 < avg := by dsimp [avg]; positivity
  have hhalfX : 0 < halfX := by dsimp [halfX]; positivity
  have hfirst :
      (1 - η) * avg * halfX ≤
        ∑ a ∈ Finset.Ioc X (2 * X), (roughMultiplicity z H a : ℝ) := by
    apply le_trans ?_ (roughMultiplicity_firstMoment_lower hH hHX)
    dsimp [avg, halfX, V, E] at ⊢ herrFirst
    have hHℝ : (0 : ℝ) ≤ H := by positivity
    nlinarith
  have hsecond :
      (∑ a ∈ Finset.Ioc X (2 * X),
          (roughMultiplicity z H a : ℝ) ^ 2) ≤
        (1 + 2 * η) * avg ^ 2 * halfX + avg * halfX := by
    have hbase := roughMultiplicity_secondMoment_upper hz hHX
    simp only [Nat.cast_pow] at hbase
    apply hbase.trans
    dsimp [avg, halfX, V, E] at ⊢ herrSecond
    have hXℝ : (0 : ℝ) ≤ X := by positivity
    have hHℝ : (0 : ℝ) ≤ H := by positivity
    nlinarith [sq_nonneg (H : ℝ), sq_nonneg (FullShiftSieve.roughEulerMass z)]
  have hsupport := one_sub_six_mul_le_positiveSupport
    (Finset.Ioc X (2 * X)) (fun a ↦ roughMultiplicity z H a)
    hη hηsmall havg (by simpa [avg, V] using hlarge) hhalfX hfirst hsecond
  simpa only [roughPositivePoints] using hsupport

/-- The same Paley--Zygmund conclusion using logarithmically truncated Brun
weights.  The tail parameter is `η/4`; the two explicit endpoint losses are
kept separate because the lower and upper truncation levels have opposite
parity. -/
theorem roughPositivePoints_lower_brun
    {X H z Lminus Lplus : ℕ} {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 6)
    (hX : 0 < X) (hH : 0 < H) (hz : 3 ≤ z) (hHX : 2 * H ≤ X)
    (hLminus : Odd Lminus) (hLplus : Even Lplus)
    (hpowMinus : (((z + 1 : ℕ) : ℝ) ^ 18) ≤
      (η / 4) * (2 : ℝ) ^ (Lminus + 1))
    (hpowPlus : (((z + 1 : ℕ) : ℝ) ^ 18) ≤
      (η / 4) * (2 : ℝ) ^ (Lplus + 1))
    (hlarge : 1 ≤ η *
      (2 * (H : ℝ) * FullShiftSieve.roughEulerMass z))
    (herrFirst : FullShiftSieve.brunEndpointError z Lminus ≤
      (η / 2) * (X : ℝ) * FullShiftSieve.roughEulerMass z)
    (herrSecond : FullShiftSieve.brunEndpointError z Lplus ≤
      η * (X : ℝ) * FullShiftSieve.roughEulerMass z ^ 2) :
    (1 - 6 * η) * ((X : ℝ) / 2) ≤
      ((roughPositivePoints X H z).card : ℝ) := by
  let V := FullShiftSieve.roughEulerMass z
  let avg : ℝ := 2 * (H : ℝ) * V
  let halfX : ℝ := (X : ℝ) / 2
  have hlog : 0 < Real.log (z - 1 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < z - 1)
  have hV : 0 < V := by
    dsimp [V]
    exact (div_pos Erdos469.naturalLinearMertensLower_pos hlog).trans_le
      (FullShiftSieve.roughEulerMass_bounds hz).1
  have havg : 0 < avg := by dsimp [avg]; positivity
  have hhalfX : 0 < halfX := by dsimp [halfX]; positivity
  have htau : (0 : ℝ) ≤ η / 4 := by positivity
  have hfirstBase := roughMultiplicity_firstMoment_lower_brun
    htau hLminus (by omega : 1 ≤ z) hH hHX hpowMinus
  have hfirst :
      (1 - η) * avg * halfX ≤
        ∑ a ∈ Finset.Ioc X (2 * X), (roughMultiplicity z H a : ℝ) := by
    apply le_trans ?_ hfirstBase
    dsimp [avg, halfX, V] at ⊢ herrFirst
    have hHr : (0 : ℝ) ≤ H := by positivity
    nlinarith
  have hsecondBase := roughMultiplicity_secondMoment_upper_brun
    htau hLplus hz hHX hpowPlus
  have hsecond :
      (∑ a ∈ Finset.Ioc X (2 * X),
          (roughMultiplicity z H a : ℝ) ^ 2) ≤
        (1 + 2 * η) * avg ^ 2 * halfX + avg * halfX := by
    have hcast :
        (∑ a ∈ Finset.Ioc X (2 * X),
          (roughMultiplicity z H a : ℝ) ^ 2) =
        ∑ a ∈ Finset.Ioc X (2 * X),
          ((roughMultiplicity z H a ^ 2 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      norm_num [Nat.cast_pow]
    rw [hcast]
    let mu : ℝ := (H : ℝ) * FullShiftSieve.roughEulerMass z
    have hXr : (0 : ℝ) ≤ X := by positivity
    have hHr : (0 : ℝ) ≤ H := by positivity
    have hηle : (0 : ℝ) ≤ η := hη.le
    have hV0 : (0 : ℝ) ≤ FullShiftSieve.roughEulerMass z := hV.le
    have hmu0 : 0 ≤ mu := by dsimp [mu]; positivity
    have hlargeMu : 1 ≤ (2 * η) * mu := by
      dsimp [mu]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hlarge
    have htwoη : 2 * η ≤ 1 := by linarith
    have hmuOne : 1 ≤ mu := by
      have hmul : (2 * η) * mu ≤ 1 * mu :=
        mul_le_mul_of_nonneg_right htwoη hmu0
      nlinarith [hlargeMu]
    have hmule : mu ≤ mu ^ 2 := by nlinarith [sq_nonneg (mu - 1)]
    have hηmule : η * mu ≤ η * mu ^ 2 :=
      mul_le_mul_of_nonneg_left hmule hηle
    have herrMul : (H : ℝ) ^ 2 *
        FullShiftSieve.brunEndpointError z Lplus ≤
      η * (X : ℝ) * mu ^ 2 := by
      have := mul_le_mul_of_nonneg_left herrSecond (sq_nonneg (H : ℝ))
      dsimp [mu]
      nlinarith [sq_nonneg (FullShiftSieve.roughEulerMass z)]
    calc
      (∑ a ∈ Finset.Ioc X (2 * X),
          ((roughMultiplicity z H a ^ 2 : ℕ) : ℝ)) ≤
          (X : ℝ) * (1 + η / 4) *
            ((H : ℝ) * FullShiftSieve.roughEulerMass z +
              2 * FullShiftSieve.roughEulerMass z ^ 2 * (H : ℝ) ^ 2) +
            (H : ℝ) ^ 2 *
              FullShiftSieve.brunEndpointError z Lplus := hsecondBase
      _ ≤ (X : ℝ) * (1 + η / 4) * (mu + 2 * mu ^ 2) +
            η * (X : ℝ) * mu ^ 2 := by
        have hid :
            (H : ℝ) * FullShiftSieve.roughEulerMass z +
                2 * FullShiftSieve.roughEulerMass z ^ 2 * (H : ℝ) ^ 2 =
              mu + 2 * mu ^ 2 := by dsimp [mu]; ring
        rw [hid]
        exact add_le_add_right herrMul _
      _ ≤ (1 + 2 * η) * avg ^ 2 * halfX + avg * halfX := by
        dsimp [avg, halfX, V, mu] at ⊢ hηmule
        nlinarith
  have hsupport := one_sub_six_mul_le_positiveSupport
    (Finset.Ioc X (2 * X)) (fun a ↦ roughMultiplicity z H a)
    hη hηsmall havg (by simpa [avg, V] using hlarge) hhalfX hfirst hsecond
  simpa only [roughPositivePoints] using hsupport

/-- Odd points in the ambient dyadic interval. -/
noncomputable def oddDyadicPoints (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X)).filter Odd

/-- Odd dyadic points missed by every rough residual in the even shift
block. -/
noncomputable def roughOddZeroPoints (X H z : ℕ) : Finset ℕ := by
  classical
  exact (oddDyadicPoints X).filter fun a ↦ roughMultiplicity z H a = 0

lemma roughPositivePoints_subset_oddDyadicPoints
    {X H z : ℕ} (hz : 2 < z) (hHX : 2 * H ≤ X) :
    roughPositivePoints X H z ⊆ oddDyadicPoints X := by
  classical
  intro a ha
  rw [roughPositivePoints, Finset.mem_filter] at ha
  rw [oddDyadicPoints, Finset.mem_filter]
  refine ⟨ha.1, Nat.not_even_iff_odd.mp ?_⟩
  have hnonempty :
      ((evenShifts H).filter fun s ↦ IsRough z (a - s)).Nonempty := by
    apply Finset.card_pos.mp
    simpa only [roughMultiplicity] using ha.2
  obtain ⟨s, hs⟩ := hnonempty
  obtain ⟨hsEven, hsRough⟩ := Finset.mem_filter.mp hs
  have haX : X < a := (Finset.mem_Ioc.mp ha.1).1
  have hsa : s ≤ a := (evenShifts_le hHX hsEven).trans haX.le
  intro haEven
  apply hsRough 2 Nat.prime_two hz
  have htwoA : 2 ∣ a := even_iff_two_dvd.mp haEven
  have htwoS : 2 ∣ s := by
    rw [evenShifts, Finset.mem_image] at hsEven
    obtain ⟨j, _hj, rfl⟩ := hsEven
    exact dvd_mul_right 2 j
  exact Nat.dvd_sub htwoA htwoS

/-- There are at most `ceil(X/2)` odd integers in `(X,2X]`. -/
lemma oddDyadicPoints_card_le (X : ℕ) :
    (oddDyadicPoints X).card ≤ X - X / 2 := by
  classical
  let f : ℕ → ℕ := fun a ↦ a / 2
  have hinj : Set.InjOn f (↑(oddDyadicPoints X) : Set ℕ) := by
    intro a ha b hb hab
    have haData := (Finset.mem_filter.mp ha).2
    have hbData := (Finset.mem_filter.mp hb).2
    obtain ⟨u, hu⟩ := haData
    obtain ⟨v, hv⟩ := hbData
    have haDiv := Nat.mod_add_div a 2
    have hbDiv := Nat.mod_add_div b 2
    have haMod := Nat.mod_lt a (by norm_num : 0 < 2)
    have hbMod := Nat.mod_lt b (by norm_num : 0 < 2)
    dsimp [f] at hab
    omega
  have himage : (oddDyadicPoints X).image f ⊆ Finset.Ico (X / 2) X := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    have haData := Finset.mem_filter.mp ha
    have haIoc := Finset.mem_Ioc.mp haData.1
    obtain ⟨u, hu⟩ := haData.2
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.div_le_div_right haIoc.1.le
    · rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
      omega
  calc
    (oddDyadicPoints X).card = ((oddDyadicPoints X).image f).card := by
      symm
      exact Finset.card_image_of_injOn hinj
    _ ≤ (Finset.Ico (X / 2) X).card := Finset.card_le_card himage
    _ = X - X / 2 := by simp

lemma roughOddZeroPoints_eq_sdiff (X H z : ℕ) :
    roughOddZeroPoints X H z =
      oddDyadicPoints X \ roughPositivePoints X H z := by
  classical
  ext a
  simp only [roughOddZeroPoints, oddDyadicPoints, roughPositivePoints,
    Finset.mem_filter, Finset.mem_sdiff, Nat.pos_iff_ne_zero]
  tauto

/-- The positive-support estimate, together with the exact parity count,
bounds the odd zero set by `3ηX+1`. -/
theorem roughOddZeroPoints_upper {X H z : ℕ} {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 6)
    (hX : 0 < X) (hH : 0 < H) (hz : 3 ≤ z) (hHX : 2 * H ≤ X)
    (hlarge : 1 ≤ η *
      (2 * (H : ℝ) * FullShiftSieve.roughEulerMass z))
    (herrFirst :
      (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card ≤
        η * (X : ℝ) * FullShiftSieve.roughEulerMass z)
    (herrSecond :
      (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card ≤
        4 * η * (X : ℝ) * FullShiftSieve.roughEulerMass z ^ 2) :
    ((roughOddZeroPoints X H z).card : ℝ) ≤ 3 * η * X + 1 := by
  have hsubset := roughPositivePoints_subset_oddDyadicPoints
    (X := X) (H := H) (z := z) (by omega) hHX
  have hpartition :
      (roughOddZeroPoints X H z).card +
        (roughPositivePoints X H z).card = (oddDyadicPoints X).card := by
    rw [roughOddZeroPoints_eq_sdiff]
    exact Finset.card_sdiff_add_card_eq_card hsubset
  have hoddNat := oddDyadicPoints_card_le X
  have hhalfNat : X - X / 2 ≤ X / 2 + 1 := by
    have hmod := Nat.mod_add_div X 2
    have hmodlt := Nat.mod_lt X (by norm_num : 0 < 2)
    omega
  have hodd : ((oddDyadicPoints X).card : ℝ) ≤ (X : ℝ) / 2 + 1 := by
    have : (oddDyadicPoints X).card ≤ X / 2 + 1 :=
      hoddNat.trans hhalfNat
    have hcast : ((oddDyadicPoints X).card : ℝ) ≤
        ((X / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    have hdiv : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 :=
      Nat.cast_div_le
    exact hcast.trans (by nlinarith [hdiv])
  have hpositive := roughPositivePoints_lower hη hηsmall hX hH hz hHX
    hlarge herrFirst herrSecond
  have hpartitionR :
      ((roughOddZeroPoints X H z).card : ℝ) +
        (roughPositivePoints X H z).card = (oddDyadicPoints X).card := by
    exact_mod_cast hpartition
  nlinarith

/-- Odd-zero estimate furnished by the truncated-Brun moment theorem. -/
theorem roughOddZeroPoints_upper_brun
    {X H z Lminus Lplus : ℕ} {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 6)
    (hX : 0 < X) (hH : 0 < H) (hz : 3 ≤ z) (hHX : 2 * H ≤ X)
    (hLminus : Odd Lminus) (hLplus : Even Lplus)
    (hpowMinus : (((z + 1 : ℕ) : ℝ) ^ 18) ≤
      (η / 4) * (2 : ℝ) ^ (Lminus + 1))
    (hpowPlus : (((z + 1 : ℕ) : ℝ) ^ 18) ≤
      (η / 4) * (2 : ℝ) ^ (Lplus + 1))
    (hlarge : 1 ≤ η *
      (2 * (H : ℝ) * FullShiftSieve.roughEulerMass z))
    (herrFirst : FullShiftSieve.brunEndpointError z Lminus ≤
      (η / 2) * (X : ℝ) * FullShiftSieve.roughEulerMass z)
    (herrSecond : FullShiftSieve.brunEndpointError z Lplus ≤
      η * (X : ℝ) * FullShiftSieve.roughEulerMass z ^ 2) :
    ((roughOddZeroPoints X H z).card : ℝ) ≤ 3 * η * X + 1 := by
  have hsubset := roughPositivePoints_subset_oddDyadicPoints
    (X := X) (H := H) (z := z) (by omega) hHX
  have hpartition :
      (roughOddZeroPoints X H z).card +
        (roughPositivePoints X H z).card = (oddDyadicPoints X).card := by
    rw [roughOddZeroPoints_eq_sdiff]
    exact Finset.card_sdiff_add_card_eq_card hsubset
  have hoddNat := oddDyadicPoints_card_le X
  have hhalfNat : X - X / 2 ≤ X / 2 + 1 := by
    have hmod := Nat.mod_add_div X 2
    have hmodlt := Nat.mod_lt X (by norm_num : 0 < 2)
    omega
  have hodd : ((oddDyadicPoints X).card : ℝ) ≤ (X : ℝ) / 2 + 1 := by
    have : (oddDyadicPoints X).card ≤ X / 2 + 1 := hoddNat.trans hhalfNat
    have hcast : ((oddDyadicPoints X).card : ℝ) ≤
        ((X / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    have hdiv : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 := Nat.cast_div_le
    exact hcast.trans (by nlinarith [hdiv])
  have hpositive := roughPositivePoints_lower_brun hη hηsmall hX hH hz hHX
    hLminus hLplus hpowMinus hpowPlus hlarge herrFirst herrSecond
  have hpartitionR :
      ((roughOddZeroPoints X H z).card : ℝ) +
        (roughPositivePoints X H z).card = (oddDyadicPoints X).card := by
    exact_mod_cast hpartition
  nlinarith

/-- Number of `z`-rough integers in the short interval `(x, x + H]`. -/
noncomputable def roughIntervalCount (z H x : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc x (x + H)).filter (IsRough z)).card

@[simp] lemma roughIntervalCount_eq_zero_iff (z H x : ℕ) :
    roughIntervalCount z H x = 0 ↔
      ∀ m ∈ Finset.Ioc x (x + H), ¬IsRough z m := by
  classical
  rw [roughIntervalCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]

/-- If an exceptional gap is shorter than `z`, it contains no `z`-rough
integer. -/
lemma exceptionalGap_no_rough {n z m : ℕ}
    (hn : ExceptionalGap n) (hgap : gapLength n < z)
    (hmleft : nthPrime n < m) (hmright : m < nthPrime (n + 1)) :
    ¬IsRough z m := by
  intro hm
  apply hn
  rw [goodGap_iff_exists_rough]
  exact ⟨m, hmleft, hmright,
    hm.mono_cutoff hgap.le⟩

/-- Every short interval lying strictly inside an exceptional gap shorter
than `z` has rough-number count zero. -/
lemma roughIntervalCount_eq_zero_of_inside_exceptionalGap
    {n z H x : ℕ} (hn : ExceptionalGap n)
    (hgap : gapLength n < z) (hxleft : nthPrime n ≤ x)
    (hxright : x + H < nthPrime (n + 1)) :
    roughIntervalCount z H x = 0 := by
  rw [roughIntervalCount_eq_zero_iff]
  intro m hm
  have hmIoc := Finset.mem_Ioc.mp hm
  exact exceptionalGap_no_rough hn hgap
    (hxleft.trans_lt hmIoc.1) (hmIoc.2.trans_lt hxright)

/-- Exceptional gaps on the dyadic prime scale which are long enough to
contain `H` disjoint short-interval starts, but still shorter than the
roughness cutoff. -/
noncomputable def mediumExceptionalGaps (X H z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X)).filter fun n ↦
    X ≤ nthPrime n ∧ nthPrime (n + 1) ≤ 2 * X ∧
      2 * H < gapLength n ∧ gapLength n < z ∧ ExceptionalGap n

/-- The parity-sensitive medium range used by the even-shift second moment.
The factor `4` leaves room for `H` distinct odd sample points and all `H`
even residual shifts inside each gap. -/
noncomputable def parityMediumExceptionalGaps (X H z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X)).filter fun n ↦
    X ≤ nthPrime n ∧ nthPrime (n + 1) ≤ 2 * X ∧
      4 * H < gapLength n ∧ gapLength n < z ∧ ExceptionalGap n

/-- Short-interval starts in `[X,2X]` at which no `z`-rough integer occurs. -/
noncomputable def roughZeroStarts (X H z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc X (2 * X)).filter fun x ↦
    roughIntervalCount z H x = 0

lemma nthPrime_add_gapLength (n : ℕ) :
    nthPrime n + gapLength n = nthPrime (n + 1) := by
  exact Nat.add_sub_of_le (nthPrime_lt_succ n).le

lemma parityMediumGap_point_injective (X H z : ℕ) :
    Set.InjOn
      (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + 2 * H + 2 * nj.2)
      (↑(parityMediumExceptionalGaps X H z ×ˢ Finset.range H) :
        Set (ℕ × ℕ)) := by
  classical
  intro nj hnj kl hkl heq
  rcases nj with ⟨n, j⟩
  rcases kl with ⟨k, l⟩
  change (n, j) ∈ parityMediumExceptionalGaps X H z ×ˢ
    Finset.range H at hnj
  change (k, l) ∈ parityMediumExceptionalGaps X H z ×ˢ
    Finset.range H at hkl
  change nthPrime n + 2 * H + 2 * j =
    nthPrime k + 2 * H + 2 * l at heq
  have hn : n ∈ parityMediumExceptionalGaps X H z ∧
      j ∈ Finset.range H := by
    simpa only [Finset.mem_product] using hnj
  have hk : k ∈ parityMediumExceptionalGaps X H z ∧
      l ∈ Finset.range H := by
    simpa only [Finset.mem_product] using hkl
  have hj : j < H := Finset.mem_range.mp hn.2
  have hl : l < H := Finset.mem_range.mp hk.2
  have hnData := (Finset.mem_filter.mp hn.1).2
  have hkData := (Finset.mem_filter.mp hk.1).2
  rcases hnData with ⟨_hnX, _hnUpper, hnGap, _hnZ, _hnExceptional⟩
  rcases hkData with ⟨_hkX, _hkUpper, hkGap, _hkZ, _hkExceptional⟩
  have hnInside : nthPrime n + 2 * H + 2 * j < nthPrime (n + 1) := by
    have hoff : 2 * H + 2 * j < gapLength n := by omega
    calc
      nthPrime n + 2 * H + 2 * j =
          nthPrime n + (2 * H + 2 * j) := by omega
      _ < nthPrime n + gapLength n := Nat.add_lt_add_left hoff _
      _ = nthPrime (n + 1) := nthPrime_add_gapLength n
  have hkInside : nthPrime k + 2 * H + 2 * l < nthPrime (k + 1) := by
    have hoff : 2 * H + 2 * l < gapLength k := by omega
    calc
      nthPrime k + 2 * H + 2 * l =
          nthPrime k + (2 * H + 2 * l) := by omega
      _ < nthPrime k + gapLength k := Nat.add_lt_add_left hoff _
      _ = nthPrime (k + 1) := nthPrime_add_gapLength k
  have hnk : n = k := by
    rcases lt_trichotomy n k with hlt | he | hgt
    · have hmono : nthPrime (n + 1) ≤ nthPrime k :=
        nthPrime_strictMono.monotone (Nat.succ_le_iff.mpr hlt)
      have hcontra : nthPrime n + 2 * H + 2 * j <
          nthPrime k + 2 * H + 2 * l :=
        hnInside.trans_le (hmono.trans (by omega))
      exact ((ne_of_lt hcontra) heq).elim
    · exact he
    · have hmono : nthPrime (k + 1) ≤ nthPrime n :=
        nthPrime_strictMono.monotone (Nat.succ_le_iff.mpr hgt)
      have hcontra : nthPrime k + 2 * H + 2 * l <
          nthPrime n + 2 * H + 2 * j :=
        hkInside.trans_le (hmono.trans (by omega))
      exact ((ne_of_gt hcontra) heq).elim
  subst k
  simp only [Prod.mk.injEq, true_and]
  omega

lemma parityMediumGap_point_image_subset_oddZeros
    {X H z : ℕ} (hX3 : 3 ≤ X) :
    (parityMediumExceptionalGaps X H z ×ˢ Finset.range H).image
        (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + 2 * H + 2 * nj.2) ⊆
      roughOddZeroPoints X H z := by
  classical
  intro a ha
  obtain ⟨nj, hnj, rfl⟩ := Finset.mem_image.mp ha
  rcases nj with ⟨n, j⟩
  change (n, j) ∈ parityMediumExceptionalGaps X H z ×ˢ
    Finset.range H at hnj
  change nthPrime n + 2 * H + 2 * j ∈ roughOddZeroPoints X H z
  have hn : n ∈ parityMediumExceptionalGaps X H z ∧
      j ∈ Finset.range H := by
    simpa only [Finset.mem_product] using hnj
  have hj : j < H := Finset.mem_range.mp hn.2
  have hnData := (Finset.mem_filter.mp hn.1).2
  rcases hnData with ⟨hnX, hnUpper, hnGap, hnZ, hnExceptional⟩
  rw [roughOddZeroPoints, Finset.mem_filter]
  constructor
  · rw [oddDyadicPoints, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · constructor
      · omega
      · have hoff : 2 * H + 2 * j < gapLength n := by omega
        exact (calc
          nthPrime n + 2 * H + 2 * j < nthPrime n + gapLength n := by
            omega
          _ = nthPrime (n + 1) := nthPrime_add_gapLength n
          _ ≤ 2 * X := hnUpper).le
    · have hpOdd : Odd (nthPrime n) :=
        (nthPrime_prime n).odd_iff.mpr (hX3.trans hnX)
      have hoffEven : Even (2 * H + 2 * j) := by
        rw [show 2 * H + 2 * j = 2 * (H + j) by omega]
        exact even_two_mul _
      have := hpOdd.add_even hoffEven
      simpa only [Nat.add_assoc] using this
  · rw [roughMultiplicity, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro s hsEven
    rw [evenShifts, Finset.mem_image] at hsEven
    obtain ⟨k, hk, rfl⟩ := hsEven
    have hkH : k < H := Finset.mem_range.mp hk
    apply exceptionalGap_no_rough hnExceptional hnZ
    · omega
    · have hoff : 2 * H + 2 * j < gapLength n := by omega
      have hpoint : nthPrime n + 2 * H + 2 * j < nthPrime (n + 1) := by
        calc
          nthPrime n + 2 * H + 2 * j < nthPrime n + gapLength n := by
            omega
          _ = nthPrime (n + 1) := nthPrime_add_gapLength n
      exact (Nat.sub_le _ _).trans_lt hpoint

/-- Each parity-medium exceptional gap supplies `H` distinct odd zero
points. -/
theorem parityMediumExceptionalGaps_mul_le_roughOddZeroPoints
    {X H z : ℕ} (hX3 : 3 ≤ X) :
    (parityMediumExceptionalGaps X H z).card * H ≤
      (roughOddZeroPoints X H z).card := by
  classical
  calc
    (parityMediumExceptionalGaps X H z).card * H =
        (parityMediumExceptionalGaps X H z ×ˢ Finset.range H).card := by simp
    _ = ((parityMediumExceptionalGaps X H z ×ˢ Finset.range H).image
          (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + 2 * H + 2 * nj.2)).card := by
      symm
      exact Finset.card_image_of_injOn
        (parityMediumGap_point_injective X H z)
    _ ≤ (roughOddZeroPoints X H z).card :=
      Finset.card_le_card
        (parityMediumGap_point_image_subset_oddZeros hX3)

/-- Positive even distances no larger than `4H`. -/
def evenShortDistances (H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (4 * H)).filter Even

lemma evenShortDistances_card_le (H : ℕ) :
    (evenShortDistances H).card ≤ 4 * H := by
  unfold evenShortDistances
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- Short exceptional gaps in the parity-sensitive decomposition. -/
noncomputable def paritySmallExceptionalGaps (X H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X)).filter fun n ↦
    X ≤ nthPrime n ∧ nthPrime (n + 1) ≤ 2 * X ∧
      gapLength n ≤ 4 * H ∧ ExceptionalGap n

/-- Union of the full-sieve upper candidates for all relevant short even
distances. -/
noncomputable def shortGapCandidateUnion (X H z : ℕ) : Finset ℕ := by
  classical
  exact (evenShortDistances H).biUnion fun d ↦
    FullShiftSieve.candidates {0, d} X z

lemma paritySmallGap_upperPrime_image_subset_candidates
    {X H z : ℕ} (hX3 : 3 ≤ X) (hzX : z ≤ X) :
    (paritySmallExceptionalGaps X H).image (fun n ↦ nthPrime (n + 1)) ⊆
      shortGapCandidateUnion X H z := by
  classical
  intro q hq
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
  have hnData := (Finset.mem_filter.mp hn).2
  rcases hnData with ⟨hnX, hnUpper, hnGap, _hnExceptional⟩
  have hpOdd : Odd (nthPrime n) :=
    (nthPrime_prime n).odd_iff.mpr (hX3.trans hnX)
  have hqOdd : Odd (nthPrime (n + 1)) :=
    (nthPrime_prime (n + 1)).odd_iff.mpr
      (hX3.trans (hnX.trans (nthPrime_lt_succ n).le))
  have hgapEven : Even (gapLength n) := by
    exact Nat.Odd.sub_odd hqOdd hpOdd
  rw [shortGapCandidateUnion, Finset.mem_biUnion]
  refine ⟨gapLength n, ?_, ?_⟩
  · rw [evenShortDistances, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.sub_pos_of_lt (nthPrime_lt_succ n), hnGap⟩,
      hgapEven⟩
  · rw [FullShiftSieve.mem_candidates_iff]
    constructor
    · rw [Finset.mem_Ioc]
      exact ⟨hnX.trans_lt (nthPrime_lt_succ n), hnUpper⟩
    · intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · intro p hp hpz hpdvd
        have heq : p = nthPrime (n + 1) :=
          (Nat.prime_dvd_prime_iff_eq hp
            (nthPrime_prime (n + 1))).mp hpdvd
        have hlt := nthPrime_lt_succ n
        omega
      · have hresidual : nthPrime (n + 1) - gapLength n = nthPrime n := by
          rw [gapLength]
          exact Nat.sub_sub_self (nthPrime_lt_succ n).le
        rw [hresidual]
        intro p hp hpz hpdvd
        have heq : p = nthPrime n :=
          (Nat.prime_dvd_prime_iff_eq hp (nthPrime_prime n)).mp hpdvd
        omega

lemma paritySmallGap_upperPrime_injective (X H : ℕ) :
    Set.InjOn (fun n ↦ nthPrime (n + 1))
      (↑(paritySmallExceptionalGaps X H) : Set ℕ) := by
  intro n hn k hk heq
  exact Nat.succ.inj (nthPrime_strictMono.injective heq)

theorem paritySmallExceptionalGaps_card_le_candidateSum
    {X H z : ℕ} (hX3 : 3 ≤ X) (hzX : z ≤ X) :
    (paritySmallExceptionalGaps X H).card ≤
      ∑ d ∈ evenShortDistances H,
        (FullShiftSieve.candidates {0, d} X z).card := by
  classical
  calc
    (paritySmallExceptionalGaps X H).card =
        ((paritySmallExceptionalGaps X H).image
          (fun n ↦ nthPrime (n + 1))).card := by
      symm
      exact Finset.card_image_of_injOn
        (paritySmallGap_upperPrime_injective X H)
    _ ≤ (shortGapCandidateUnion X H z).card :=
      Finset.card_le_card
        (paritySmallGap_upperPrime_image_subset_candidates hX3 hzX)
    _ ≤ ∑ d ∈ evenShortDistances H,
        (FullShiftSieve.candidates {0, d} X z).card := by
      exact Finset.card_biUnion_le

/-- Odd-prime beta-sieve candidates for all relevant short distances.  The
prime `2` need not be sieved here because the points injected from prime
pairs are already odd. -/
noncomputable def betaShortGapCandidateUnion (X H y : ℕ) : Finset ℕ := by
  classical
  exact (evenShortDistances H).biUnion fun d ↦
    Erdos851.ShiftSieve.siftedShiftCandidates {0, d} X 2 (y + 1)

lemma prime_coprime_sieveProduct_two
    {p y : ℕ} (hp : p.Prime) (hyp : y + 1 ≤ p) :
    Nat.Coprime (Erdos387.sievePrimeProduct 2 (y + 1)) p := by
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hpdvd
  have hpMem := Erdos387.mem_sievePrimes.mp
    (Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpdvd)
  omega

lemma paritySmallGap_upperPrime_image_subset_betaCandidates
    {X H y : ℕ} (hX3 : 3 ≤ X) (hyX : y + 1 ≤ X) :
    (paritySmallExceptionalGaps X H).image (fun n ↦ nthPrime (n + 1)) ⊆
      betaShortGapCandidateUnion X H y := by
  classical
  intro q hq
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
  have hnData := (Finset.mem_filter.mp hn).2
  rcases hnData with ⟨hnX, hnUpper, hnGap, _hnExceptional⟩
  have hpOdd : Odd (nthPrime n) :=
    (nthPrime_prime n).odd_iff.mpr (hX3.trans hnX)
  have hqOdd : Odd (nthPrime (n + 1)) :=
    (nthPrime_prime (n + 1)).odd_iff.mpr
      (hX3.trans (hnX.trans (nthPrime_lt_succ n).le))
  have hgapEven : Even (gapLength n) := Nat.Odd.sub_odd hqOdd hpOdd
  rw [betaShortGapCandidateUnion, Finset.mem_biUnion]
  refine ⟨gapLength n, ?_, ?_⟩
  · rw [evenShortDistances, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.sub_pos_of_lt (nthPrime_lt_succ n), hnGap⟩, hgapEven⟩
  · rw [Erdos851.ShiftSieve.siftedShiftCandidates, Finset.mem_filter]
    refine ⟨Finset.mem_Ioc.mpr
      ⟨hnX.trans_lt (nthPrime_lt_succ n), hnUpper⟩, ?_⟩
    have hresidual : nthPrime (n + 1) - gapLength n = nthPrime n := by
      rw [gapLength]
      exact Nat.sub_sub_self (nthPrime_lt_succ n).le
    have hcopNext := prime_coprime_sieveProduct_two
      (nthPrime_prime (n + 1))
      (hyX.trans (hnX.trans (nthPrime_lt_succ n).le))
    have hcopPrev := prime_coprime_sieveProduct_two
      (nthPrime_prime n) (hyX.trans hnX)
    have hgapNe : gapLength n ≠ 0 :=
      (Nat.sub_pos_of_lt (nthPrime_lt_succ n)).ne'
    have hzero : 0 ∉ ({gapLength n} : Finset ℕ) := by
      simpa using hgapNe.symm
    rw [Erdos851.ShiftSieve.shiftedProduct,
      Finset.prod_insert hzero, Finset.prod_singleton, Nat.sub_zero,
      hresidual]
    exact Nat.Coprime.mul_right hcopNext hcopPrev

theorem paritySmallExceptionalGaps_card_le_betaCandidateSum
    {X H y : ℕ} (hX3 : 3 ≤ X) (hyX : y + 1 ≤ X) :
    (paritySmallExceptionalGaps X H).card ≤
      ∑ d ∈ evenShortDistances H,
        (Erdos851.ShiftSieve.siftedShiftCandidates {0, d}
          X 2 (y + 1)).card := by
  calc
    (paritySmallExceptionalGaps X H).card =
        ((paritySmallExceptionalGaps X H).image
          (fun n ↦ nthPrime (n + 1))).card := by
      symm
      exact Finset.card_image_of_injOn
        (paritySmallGap_upperPrime_injective X H)
    _ ≤ (betaShortGapCandidateUnion X H y).card :=
      Finset.card_le_card
        (paritySmallGap_upperPrime_image_subset_betaCandidates hX3 hyX)
    _ ≤ ∑ d ∈ evenShortDistances H,
        (Erdos851.ShiftSieve.siftedShiftCandidates {0, d}
          X 2 (y + 1)).card := Finset.card_biUnion_le

/-- The concrete dimension-two beta sieve, averaged over the possible short
even distances.  The first term is the Selberg/Brun prime-pair main term;
the second is the square-level endpoint loss. -/
theorem exists_paritySmallExceptionalGaps_upper_beta :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {X H y S : ℕ}, 3 ≤ X → 0 < H → 2 ≤ y →
        y + 1 ≤ X → 4 * H ≤ X → 101 ≤ S →
        Real.log A ≤ 4 * ((S - 100 : ℕ) : ℝ) / 99 →
        (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) ≤ 1 →
        ((paritySmallExceptionalGaps X H).card : ℝ) ≤
          64 * (X : ℝ) * H * FullShiftSieve.roughEulerMass (y + 1) ^ 2 +
            4 * (H : ℝ) * (((y ^ S : ℕ) : ℝ) ^ 2) := by
  obtain ⟨A, hA, hpair⟩ := Erdos851.exists_pairShift_concrete_cardinality_bounds
  refine ⟨A, hA, ?_⟩
  intro X H y S hX3 hH hy hyX hHX hS hlog heta
  let betaEta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let V : ℝ := FullShiftSieve.roughEulerMass (y + 1)
  let E : ℝ := (((y ^ S : ℕ) : ℝ) ^ 2)
  let P := Erdos851.sievePrimes 2 y
  let C : ℕ → ℝ := fun d ↦
    ∏ p ∈ P, Erdos851.pairDirectCorrection d p
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (Erdos851.mem_sievePrimes.mp hp).2.2
  have hp2 : ∀ p ∈ P, 2 < p := by
    intro p hp
    exact (Erdos851.mem_sievePrimes.mp hp).1
  have hCnonneg (d : ℕ) : 0 ≤ C d := by
    dsimp [C]
    exact Finset.prod_nonneg fun p hp ↦
      Erdos851.pairDirectCorrection_nonneg (hp2 p hp)
  have hCsum : (∑ d ∈ evenShortDistances H, C d) ≤ (8 * H : ℕ) := by
    calc
      (∑ d ∈ evenShortDistances H, C d) ≤
          ∑ d ∈ Finset.Icc 1 (4 * H), C d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro d hdBig hdSmall
          exact hCnonneg d
      _ ≤ (8 * H : ℕ) :=
        pairCorrection_Icc_four_mul_le_eight_mul P hprime hp2 hH
  have hcardNat := paritySmallExceptionalGaps_card_le_betaCandidateSum
    (X := X) (H := H) (y := y) hX3 hyX
  have hcard : ((paritySmallExceptionalGaps X H).card : ℝ) ≤
      ∑ d ∈ evenShortDistances H,
        ((Erdos851.ShiftSieve.siftedShiftCandidates {0, d}
          X 2 (y + 1)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hterm (d : ℕ) (hd : d ∈ evenShortDistances H) :
      ((Erdos851.ShiftSieve.siftedShiftCandidates {0, d}
          X 2 (y + 1)).card : ℝ) ≤
        8 * (X : ℝ) * V ^ 2 * C d + E := by
    have hdData := Finset.mem_filter.mp hd
    have hdle : d ≤ X := (Finset.mem_Icc.mp hdData.1).2.trans hHX
    have hb := (hpair 0 d X 2 y S (by omega) hdle (by norm_num) hy
      (by omega) hS hlog).2
    have hone :
        Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 y =
          2 * FullShiftSieve.roughEulerMass (y + 1) := by
      simpa using FullShiftSieve.odd_oneShiftEuler_eq_two_mul_roughEulerMass
        (z := y + 1) (by omega)
    rw [Erdos851.pairShift_localEulerProduct_eq (Nat.dist 0 d)
      (by norm_num : 2 ≤ 2), Nat.dist_zero_left, hone] at hb
    have hbeta0 : 0 ≤ betaEta := by dsimp [betaEta]; positivity
    have hbeta2 : 1 + betaEta ≤ 2 := by
      dsimp [betaEta]
      linarith
    have hmainNonneg : 0 ≤ 4 * V ^ 2 * C d := by
      exact mul_nonneg (by positivity) (hCnonneg d)
    have hcoef : (1 + betaEta) * (4 * V ^ 2 * C d) ≤
        8 * V ^ 2 * C d := by
      calc
        (1 + betaEta) * (4 * V ^ 2 * C d) ≤
            2 * (4 * V ^ 2 * C d) :=
          mul_le_mul_of_nonneg_right hbeta2 hmainNonneg
        _ = 8 * V ^ 2 * C d := by ring
    have hXnonneg : (0 : ℝ) ≤ X := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hcoef hXnonneg
    calc
      ((Erdos851.ShiftSieve.siftedShiftCandidates {0, d}
          X 2 (y + 1)).card : ℝ) ≤
          (X : ℝ) * ((1 + betaEta) * ((2 * V) ^ 2 * C d)) + E := by
        simpa [betaEta, V, E, C, P] using hb
      _ =
          (X : ℝ) * ((1 + betaEta) * (4 * V ^ 2 * C d)) + E := by
        ring
      _ ≤ (X : ℝ) * (8 * V ^ 2 * C d) + E :=
        add_le_add hscaled le_rfl
      _ = 8 * (X : ℝ) * V ^ 2 * C d + E := by ring
  calc
    ((paritySmallExceptionalGaps X H).card : ℝ) ≤
        ∑ d ∈ evenShortDistances H,
          ((Erdos851.ShiftSieve.siftedShiftCandidates {0, d}
            X 2 (y + 1)).card : ℝ) := hcard
    _ ≤ ∑ d ∈ evenShortDistances H,
          (8 * (X : ℝ) * V ^ 2 * C d + E) := by
      exact Finset.sum_le_sum fun d hd ↦ hterm d hd
    _ = 8 * (X : ℝ) * V ^ 2 *
          (∑ d ∈ evenShortDistances H, C d) +
        (evenShortDistances H).card * E := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 8 * (X : ℝ) * V ^ 2 * (8 * H : ℕ) +
          4 * (H : ℝ) * E := by
      have hmain0 : 0 ≤ 8 * (X : ℝ) * V ^ 2 := by positivity
      have hE0 : 0 ≤ E := by dsimp [E]; positivity
      gcongr
      exact_mod_cast evenShortDistances_card_le H
    _ = 64 * (X : ℝ) * H *
          FullShiftSieve.roughEulerMass (y + 1) ^ 2 +
        4 * (H : ℝ) * (((y ^ S : ℕ) : ℝ) ^ 2) := by
      dsimp [V, E]
      push_cast
      ring

lemma shortPairCandidates_upper {X z d : ℕ}
    (hz : 3 ≤ z) (hdX : d ≤ X) (hdEven : Even d) :
    ((FullShiftSieve.candidates {0, d} X z).card : ℝ) ≤
      (X : ℝ) * (2 * FullShiftSieve.roughEulerMass z ^ 2 *
        ∏ p ∈ Erdos851.sievePrimes 2 (z - 1),
          Erdos851.pairDirectCorrection d p) +
      (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
  have hparity : 0 % 2 = d % 2 := by
    obtain ⟨k, rfl⟩ := hdEven
    omega
  have hshiftX : ∀ s ∈ ({0, d} : Finset ℕ), s ≤ X := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · omega
    · exact hdX
  have h := FullShiftSieve.upper_cardinality_bound
    (shifts := ({0, d} : Finset ℕ)) (hshifts := by simp)
    (X := X) (z := z)
    (hadmissible := FullShiftSieve.pair_admissible_of_sameParity hparity)
    hshiftX (fun p ↦ Erdos851.ShiftSieve.localNu_pair_le_two 0 d p)
  change ((FullShiftSieve.candidates {0, d} X z).card : ℝ) ≤
    (X : ℝ) * FullShiftSieve.pairEulerMass 0 d z +
      (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card at h
  rw [FullShiftSieve.pairEulerMass_eq_two_mul_sq_mul_correction hz hparity,
    Nat.dist_zero_left] at h
  exact h

/-- Full inclusion--exclusion and the ordinary-difference correction
average give the short-gap estimate used in the final decomposition. -/
theorem paritySmallExceptionalGaps_upper
    {X H z : ℕ} (hX3 : 3 ≤ X) (hH : 0 < H)
    (hz : 3 ≤ z) (hzX : z ≤ X) (hHX : 4 * H ≤ X) :
    ((paritySmallExceptionalGaps X H).card : ℝ) ≤
      16 * (X : ℝ) * H * FullShiftSieve.roughEulerMass z ^ 2 +
        4 * (H : ℝ) *
          (4 : ℝ) ^
            (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
  let P := Erdos851.sievePrimes 2 (z - 1)
  let C : ℕ → ℝ := fun d ↦
    ∏ p ∈ P, Erdos851.pairDirectCorrection d p
  let E : ℝ :=
    (4 : ℝ) ^ (Erdos387.sievePrimeProduct 1 z).primeFactors.card
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (Erdos851.mem_sievePrimes.mp hp).2.2
  have hp2 : ∀ p ∈ P, 2 < p := by
    intro p hp
    exact (Erdos851.mem_sievePrimes.mp hp).1
  have hC (d : ℕ) : 0 ≤ C d := by
    dsimp [C]
    exact Finset.prod_nonneg fun p hp ↦
      Erdos851.pairDirectCorrection_nonneg (hp2 p hp)
  have hCsum : (∑ d ∈ evenShortDistances H, C d) ≤ (8 * H : ℕ) := by
    calc
      (∑ d ∈ evenShortDistances H, C d) ≤
          ∑ d ∈ Finset.Icc 1 (4 * H), C d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro d hdBig hdSmall
          exact hC d
      _ ≤ (8 * H : ℕ) := by
        exact pairCorrection_Icc_four_mul_le_eight_mul P hprime hp2 hH
  have hcard := paritySmallExceptionalGaps_card_le_candidateSum
    (X := X) (H := H) (z := z) hX3 hzX
  have hcardR : ((paritySmallExceptionalGaps X H).card : ℝ) ≤
      ∑ d ∈ evenShortDistances H,
        ((FullShiftSieve.candidates {0, d} X z).card : ℝ) := by
    exact_mod_cast hcard
  calc
    ((paritySmallExceptionalGaps X H).card : ℝ) ≤
        ∑ d ∈ evenShortDistances H,
          ((FullShiftSieve.candidates {0, d} X z).card : ℝ) := hcardR
    _ ≤ ∑ d ∈ evenShortDistances H,
        ((X : ℝ) * (2 * FullShiftSieve.roughEulerMass z ^ 2 * C d) + E) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdData := Finset.mem_filter.mp hd
      exact shortPairCandidates_upper hz
        (hdData.1 |> Finset.mem_Icc.mp |>.2 |> fun h ↦ h.trans hHX)
        hdData.2
    _ = (X : ℝ) * (2 * FullShiftSieve.roughEulerMass z ^ 2) *
          (∑ d ∈ evenShortDistances H, C d) +
        (evenShortDistances H).card * E := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (X : ℝ) * (2 * FullShiftSieve.roughEulerMass z ^ 2) *
          (8 * H : ℕ) + 4 * (H : ℝ) * E := by
      have hmainNonneg : 0 ≤
          (X : ℝ) * (2 * FullShiftSieve.roughEulerMass z ^ 2) := by positivity
      have hE : 0 ≤ E := by dsimp [E]; positivity
      gcongr
      exact_mod_cast evenShortDistances_card_le H
    _ = 16 * (X : ℝ) * H * FullShiftSieve.roughEulerMass z ^ 2 +
        4 * (H : ℝ) *
          (4 : ℝ) ^
            (Erdos387.sievePrimeProduct 1 z).primeFactors.card := by
      dsimp [E]
      push_cast
      ring

/-- Offsets which remain inside distinct consecutive-prime gaps cannot
collide.  This is the finite, index-free form of the telescoping-gap
argument. -/
lemma gapStart_injective (F : Finset ℕ) (H : ℕ)
    (hgap : ∀ n ∈ F, H ≤ gapLength n) :
    Set.InjOn (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + nj.2)
      (↑(F ×ˢ Finset.range H) : Set (ℕ × ℕ)) := by
  classical
  intro nj hnmem kl hkmem heq
  rcases nj with ⟨n, j⟩
  rcases kl with ⟨k, l⟩
  simp only [Prod.fst, Prod.snd] at heq
  change (n, j) ∈ F ×ˢ Finset.range H at hnmem
  change (k, l) ∈ F ×ˢ Finset.range H at hkmem
  have hn : n ∈ F ∧ j ∈ Finset.range H := by
    exact Finset.mem_product.mp hnmem
  have hk : k ∈ F ∧ l ∈ Finset.range H := by
    exact Finset.mem_product.mp hkmem
  have hnj : j < H := Finset.mem_range.mp hn.2
  have hkl : l < H := Finset.mem_range.mp hk.2
  have hnInside : nthPrime n + j < nthPrime (n + 1) := by
    have hjgap : j < gapLength n := hnj.trans_le (hgap n hn.1)
    calc
      nthPrime n + j < nthPrime n + gapLength n :=
        Nat.add_lt_add_left hjgap _
      _ = nthPrime (n + 1) := nthPrime_add_gapLength n
  have hkInside : nthPrime k + l < nthPrime (k + 1) := by
    have hlgap : l < gapLength k := hkl.trans_le (hgap k hk.1)
    calc
      nthPrime k + l < nthPrime k + gapLength k :=
        Nat.add_lt_add_left hlgap _
      _ = nthPrime (k + 1) := nthPrime_add_gapLength k
  have hnk : n = k := by
    rcases lt_trichotomy n k with hlt | he | hgt
    · have hmono : nthPrime (n + 1) ≤ nthPrime k :=
        nthPrime_strictMono.monotone (Nat.succ_le_iff.mpr hlt)
      have : nthPrime n + j < nthPrime k + l :=
        hnInside.trans_le (hmono.trans (Nat.le_add_right _ _))
      exact ((ne_of_lt this) heq).elim
    · exact he
    · have hmono : nthPrime (k + 1) ≤ nthPrime n :=
        nthPrime_strictMono.monotone (Nat.succ_le_iff.mpr hgt)
      have : nthPrime k + l < nthPrime n + j :=
        hkInside.trans_le (hmono.trans (Nat.le_add_right _ _))
      exact ((ne_of_gt this) heq).elim
  subst k
  simp only [Prod.mk.injEq, true_and]
  exact Nat.add_left_cancel heq

/-- The generic gap-offset injection specialized to medium exceptional
gaps. -/
lemma mediumGap_start_injective (X H z : ℕ) :
    Set.InjOn (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + nj.2)
      (↑(mediumExceptionalGaps X H z ×ˢ Finset.range H) : Set (ℕ × ℕ)) := by
  apply gapStart_injective
  intro n hn
  have hnData := (Finset.mem_filter.mp hn).2
  rcases hnData with ⟨_, _, hnGap, _, _⟩
  exact (Nat.le_mul_of_pos_left H (by norm_num : 0 < 2)).trans hnGap.le

/-- The `H` starts supplied by every medium exceptional gap all lie in the
dyadic zero set for the rough short-interval count. -/
lemma mediumGap_start_image_subset_zeroStarts (X H z : ℕ) :
    (mediumExceptionalGaps X H z ×ˢ Finset.range H).image
        (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + nj.2) ⊆
      roughZeroStarts X H z := by
  classical
  intro x hx
  obtain ⟨nj, hnj, hxval⟩ := Finset.mem_image.mp hx
  rcases nj with ⟨n, j⟩
  simp only [Prod.fst, Prod.snd] at hnj hxval
  subst x
  have hn : n ∈ mediumExceptionalGaps X H z ∧ j ∈ Finset.range H := by
    simpa only [Finset.mem_product] using hnj
  have hj : j < H := Finset.mem_range.mp hn.2
  have hnData := (Finset.mem_filter.mp hn.1).2
  rcases hnData with ⟨hnX, hnUpper, hnGap, hnZ, hnExceptional⟩
  rw [roughZeroStarts, Finset.mem_filter]
  constructor
  · rw [Finset.mem_Icc]
    constructor
    · exact hnX.trans (Nat.le_add_right _ _)
    · have hinside : nthPrime n + j < nthPrime (n + 1) := by
        have hHtwo : H ≤ 2 * H :=
          le_mul_of_one_le_left (Nat.zero_le H) (by norm_num)
        have hjgap : j < gapLength n :=
          (hj.trans_le hHtwo).trans hnGap
        calc
          nthPrime n + j < nthPrime n + gapLength n :=
            Nat.add_lt_add_left hjgap _
          _ = nthPrime (n + 1) := nthPrime_add_gapLength n
      exact hinside.le.trans hnUpper
  · apply roughIntervalCount_eq_zero_of_inside_exceptionalGap
      hnExceptional hnZ (Nat.le_add_right _ _)
    have hjTwoH : j + H < 2 * H := by
      simpa only [two_mul] using Nat.add_lt_add_right hj H
    have hjGap : j + H < gapLength n := hjTwoH.trans hnGap
    calc
      nthPrime n + j + H = nthPrime n + (j + H) := Nat.add_assoc _ _ _
      _ < nthPrime n + gapLength n := Nat.add_lt_add_left hjGap _
      _ = nthPrime (n + 1) := nthPrime_add_gapLength n

/-- Disjointness of consecutive-prime gaps turns the zero-start estimate
into the finite counting inequality used in the four-way classification. -/
theorem mediumExceptionalGaps_mul_le_roughZeroStarts
    (X H z : ℕ) :
    (mediumExceptionalGaps X H z).card * H ≤
      (roughZeroStarts X H z).card := by
  classical
  calc
    (mediumExceptionalGaps X H z).card * H =
        (mediumExceptionalGaps X H z ×ˢ Finset.range H).card := by simp
    _ = ((mediumExceptionalGaps X H z ×ˢ Finset.range H).image
          (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + nj.2)).card := by
      symm
      exact Finset.card_image_of_injOn
        (mediumGap_start_injective X H z)
    _ ≤ (roughZeroStarts X H z).card :=
      Finset.card_le_card (mediumGap_start_image_subset_zeroStarts X H z)

/-- Exceptional gaps on the dyadic prime scale whose length is at least
`z`. -/
noncomputable def largeExceptionalGaps (X z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X)).filter fun n ↦
    X ≤ nthPrime n ∧ nthPrime (n + 1) ≤ 2 * X ∧
      z ≤ gapLength n ∧ ExceptionalGap n

/-- Every selected offset in a large gap lies in the ambient dyadic
integer interval. -/
lemma largeGap_start_image_subset_Ico (X z : ℕ) :
    (largeExceptionalGaps X z ×ˢ Finset.range z).image
        (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + nj.2) ⊆
      Finset.Ico X (2 * X) := by
  classical
  intro x hx
  obtain ⟨nj, hnj, hxval⟩ := Finset.mem_image.mp hx
  rcases nj with ⟨n, j⟩
  simp only [Prod.fst, Prod.snd] at hnj hxval
  subst x
  have hn := Finset.mem_product.mp hnj
  have hnData := (Finset.mem_filter.mp hn.1).2
  rcases hnData with ⟨hnX, hnUpper, hnGap, _⟩
  rw [Finset.mem_Ico]
  constructor
  · exact hnX.trans (Nat.le_add_right _ _)
  · have hj : j < z := Finset.mem_range.mp hn.2
    have hjgap : j < gapLength n := hj.trans_le hnGap
    calc
      nthPrime n + j < nthPrime n + gapLength n :=
        Nat.add_lt_add_left hjgap _
      _ = nthPrime (n + 1) := nthPrime_add_gapLength n
      _ ≤ 2 * X := hnUpper

/-- Telescoping/disjointness bound for long exceptional gaps. -/
theorem largeExceptionalGaps_mul_le (X z : ℕ) :
    (largeExceptionalGaps X z).card * z ≤ X := by
  classical
  calc
    (largeExceptionalGaps X z).card * z =
        (largeExceptionalGaps X z ×ˢ Finset.range z).card := by simp
    _ = ((largeExceptionalGaps X z ×ˢ Finset.range z).image
          (fun nj : ℕ × ℕ ↦ nthPrime nj.1 + nj.2)).card := by
      symm
      apply Finset.card_image_of_injOn
      apply gapStart_injective
      intro n hn
      exact ((Finset.mem_filter.mp hn).2.2.2.1)
    _ ≤ (Finset.Ico X (2 * X)).card :=
      Finset.card_le_card (largeGap_start_image_subset_Ico X z)
    _ = X := by simp; omega

/-- Exceptional dyadic gaps whose upper prime is still in the same dyadic
interval. -/
noncomputable def interiorExceptionalGaps (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X)).filter fun n ↦
    X ≤ nthPrime n ∧ nthPrime (n + 1) ≤ 2 * X ∧ ExceptionalGap n

/-- The short member of the gap decomposition. -/
noncomputable def smallExceptionalGaps (X H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X)).filter fun n ↦
    X ≤ nthPrime n ∧ nthPrime (n + 1) ≤ 2 * X ∧
      gapLength n ≤ 2 * H ∧ ExceptionalGap n

/-- Every interior exceptional gap is short, medium, or long. -/
lemma interiorExceptionalGaps_subset_three_ranges
    {X H z : ℕ} (hHz : 2 * H < z) :
    interiorExceptionalGaps X ⊆
      smallExceptionalGaps X H ∪
        (mediumExceptionalGaps X H z ∪ largeExceptionalGaps X z) := by
  classical
  intro n hn
  have hnData := (Finset.mem_filter.mp hn).2
  rcases hnData with ⟨hnX, hnUpper, hnExceptional⟩
  by_cases hsmall : gapLength n ≤ 2 * H
  · rw [Finset.mem_union]
    left
    rw [smallExceptionalGaps, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hn).1,
      hnX, hnUpper, hsmall, hnExceptional⟩
  · have hmediumLower : 2 * H < gapLength n := Nat.lt_of_not_ge hsmall
    by_cases hmediumUpper : gapLength n < z
    · rw [Finset.mem_union]
      right
      rw [Finset.mem_union]
      left
      rw [mediumExceptionalGaps, Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hn).1,
        hnX, hnUpper, hmediumLower, hmediumUpper, hnExceptional⟩
    · rw [Finset.mem_union]
      right
      rw [Finset.mem_union]
      right
      rw [largeExceptionalGaps, Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hn).1,
        hnX, hnUpper, Nat.le_of_not_gt hmediumUpper, hnExceptional⟩

/-- Finite cardinal form of the short/medium/long decomposition. -/
theorem interiorExceptionalGaps_card_le
    {X H z : ℕ} (hHz : 2 * H < z) :
    (interiorExceptionalGaps X).card ≤
      (smallExceptionalGaps X H).card +
        (mediumExceptionalGaps X H z).card +
          (largeExceptionalGaps X z).card := by
  calc
    (interiorExceptionalGaps X).card ≤
        (smallExceptionalGaps X H ∪
          (mediumExceptionalGaps X H z ∪
            largeExceptionalGaps X z)).card :=
      Finset.card_le_card (interiorExceptionalGaps_subset_three_ranges hHz)
    _ ≤ (smallExceptionalGaps X H).card +
          (mediumExceptionalGaps X H z ∪
            largeExceptionalGaps X z).card :=
      Finset.card_union_le _ _
    _ ≤ (smallExceptionalGaps X H).card +
          ((mediumExceptionalGaps X H z).card +
            (largeExceptionalGaps X z).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ = _ := by omega

/-- Parity-sensitive short/medium/long decomposition used with the even
rough-number shifts. -/
lemma interiorExceptionalGaps_subset_parity_ranges
    {X H z : ℕ} (hHz : 4 * H < z) :
    interiorExceptionalGaps X ⊆
      paritySmallExceptionalGaps X H ∪
        (parityMediumExceptionalGaps X H z ∪ largeExceptionalGaps X z) := by
  classical
  intro n hn
  have hnData := (Finset.mem_filter.mp hn).2
  rcases hnData with ⟨hnX, hnUpper, hnExceptional⟩
  by_cases hsmall : gapLength n ≤ 4 * H
  · rw [Finset.mem_union]
    left
    rw [paritySmallExceptionalGaps, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hn).1,
      hnX, hnUpper, hsmall, hnExceptional⟩
  · have hmediumLower : 4 * H < gapLength n := Nat.lt_of_not_ge hsmall
    by_cases hmediumUpper : gapLength n < z
    · rw [Finset.mem_union]
      right
      rw [Finset.mem_union]
      left
      rw [parityMediumExceptionalGaps, Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hn).1,
        hnX, hnUpper, hmediumLower, hmediumUpper, hnExceptional⟩
    · rw [Finset.mem_union]
      right
      rw [Finset.mem_union]
      right
      rw [largeExceptionalGaps, Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hn).1,
        hnX, hnUpper, Nat.le_of_not_gt hmediumUpper, hnExceptional⟩

theorem interiorExceptionalGaps_card_le_parity
    {X H z : ℕ} (hHz : 4 * H < z) :
    (interiorExceptionalGaps X).card ≤
      (paritySmallExceptionalGaps X H).card +
        (parityMediumExceptionalGaps X H z).card +
          (largeExceptionalGaps X z).card := by
  calc
    (interiorExceptionalGaps X).card ≤
        (paritySmallExceptionalGaps X H ∪
          (parityMediumExceptionalGaps X H z ∪
            largeExceptionalGaps X z)).card :=
      Finset.card_le_card (interiorExceptionalGaps_subset_parity_ranges hHz)
    _ ≤ (paritySmallExceptionalGaps X H).card +
          (parityMediumExceptionalGaps X H z ∪
            largeExceptionalGaps X z).card := Finset.card_union_le _ _
    _ ≤ (paritySmallExceptionalGaps X H).card +
          ((parityMediumExceptionalGaps X H z).card +
            (largeExceptionalGaps X z).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ = _ := by omega

/-- At most one gap with lower prime at most `2X` can cross the upper dyadic
endpoint. -/
noncomputable def crossingExceptionalGaps (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X)).filter fun n ↦
    X ≤ nthPrime n ∧ nthPrime n ≤ 2 * X ∧
      2 * X < nthPrime (n + 1) ∧ ExceptionalGap n

lemma crossingExceptionalGaps_card_le_one (X : ℕ) :
    (crossingExceptionalGaps X).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro n hn k hk
  have hnData := (Finset.mem_filter.mp hn).2
  have hkData := (Finset.mem_filter.mp hk).2
  rcases hnData with ⟨_, hnUpper, hnNext, _⟩
  rcases hkData with ⟨_, hkUpper, hkNext, _⟩
  rcases lt_trichotomy n k with hnk | hnk | hkn
  · have hmono : nthPrime (n + 1) ≤ nthPrime k :=
      nthPrime_strictMono.monotone (Nat.succ_le_iff.mpr hnk)
    exact (not_lt_of_ge (hmono.trans hkUpper) hnNext).elim
  · exact hnk
  · have hmono : nthPrime (k + 1) ≤ nthPrime n :=
      nthPrime_strictMono.monotone (Nat.succ_le_iff.mpr hkn)
    exact (not_lt_of_ge (hmono.trans hnUpper) hkNext).elim

lemma exceptionalDyadicGaps_eq_interior_union_crossing (X : ℕ) :
    exceptionalDyadicGaps X =
      interiorExceptionalGaps X ∪ crossingExceptionalGaps X := by
  classical
  ext n
  simp only [exceptionalDyadicGaps, interiorExceptionalGaps,
    crossingExceptionalGaps, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hnRange, hnX, hnUpper, hnExceptional⟩
    by_cases hnext : nthPrime (n + 1) ≤ 2 * X
    · exact Or.inl ⟨hnRange, hnX, hnext, hnExceptional⟩
    · exact Or.inr ⟨hnRange, hnX, hnUpper,
        Nat.lt_of_not_ge hnext, hnExceptional⟩
  · rintro (⟨hnRange, hnX, hnNext, hnExceptional⟩ |
      ⟨hnRange, hnX, hnUpper, _hnNext, hnExceptional⟩)
    · exact ⟨hnRange, hnX,
        (nthPrime_lt_succ n).le.trans hnNext, hnExceptional⟩
    · exact ⟨hnRange, hnX, hnUpper, hnExceptional⟩

/-- The boundary gap contributes only the harmless additive constant in the
dyadic classification. -/
theorem exceptionalDyadicCount_le_interior_add_one (X : ℕ) :
    exceptionalDyadicCount X ≤ (interiorExceptionalGaps X).card + 1 := by
  rw [exceptionalDyadicCount,
    exceptionalDyadicGaps_eq_interior_union_crossing]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (crossingExceptionalGaps_card_le_one X) _)

/-- Assembly of the parity-sensitive short/medium/long decomposition from
three real-valued component estimates.  This lemma isolates all divisions by
the positive spacing parameters `H` and `z`. -/
theorem exceptionalDyadicCount_upper_of_component_bounds
    {X H z : ℕ} {Bsmall Bzero : ℝ}
    (hX : 3 ≤ X) (hH : 0 < H) (hz : 0 < z) (hHz : 4 * H < z)
    (hsmall : ((paritySmallExceptionalGaps X H).card : ℝ) ≤ Bsmall)
    (hzero : ((roughOddZeroPoints X H z).card : ℝ) ≤ Bzero) :
    (exceptionalDyadicCount X : ℝ) ≤
      Bsmall + Bzero / H + (X : ℝ) / z + 1 := by
  have hinterNat := exceptionalDyadicCount_le_interior_add_one X
  have hpartsNat := interiorExceptionalGaps_card_le_parity
    (X := X) (H := H) (z := z) hHz
  have htotalNat : exceptionalDyadicCount X ≤
      (paritySmallExceptionalGaps X H).card +
        (parityMediumExceptionalGaps X H z).card +
          (largeExceptionalGaps X z).card + 1 := by
    omega
  have htotal : (exceptionalDyadicCount X : ℝ) ≤
      (paritySmallExceptionalGaps X H).card +
        (parityMediumExceptionalGaps X H z).card +
          (largeExceptionalGaps X z).card + 1 := by
    exact_mod_cast htotalNat
  have hmedMulNat := parityMediumExceptionalGaps_mul_le_roughOddZeroPoints
    (X := X) (H := H) (z := z) hX
  have hmedMul :
      ((parityMediumExceptionalGaps X H z).card : ℝ) * H ≤
        (roughOddZeroPoints X H z).card := by
    exact_mod_cast hmedMulNat
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hmed : ((parityMediumExceptionalGaps X H z).card : ℝ) ≤
      Bzero / H := by
    rw [le_div_iff₀ hHr]
    exact hmedMul.trans hzero
  have hlongMulNat := largeExceptionalGaps_mul_le X z
  have hlongMul : ((largeExceptionalGaps X z).card : ℝ) * z ≤ X := by
    exact_mod_cast hlongMulNat
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  have hlong : ((largeExceptionalGaps X z).card : ℝ) ≤ (X : ℝ) / z := by
    rw [le_div_iff₀ hzr]
    exact hlongMul
  linarith

/-- Fully explicit finite Gafni--Tao estimate.  The first two terms are the
beta-sieve short-gap bound; the third is the truncated-Brun odd-zero bound;
the fourth is the telescoping long-gap bound. -/
theorem exists_exceptionalDyadicCount_upper_beta_brun :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {X H y S z Lminus Lplus : ℕ} {η : ℝ},
        3 ≤ X → 0 < H → 2 ≤ y → y + 1 ≤ X → 4 * H ≤ X →
        101 ≤ S → Real.log A ≤ 4 * ((S - 100 : ℕ) : ℝ) / 99 →
        (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) ≤ 1 →
        3 ≤ z → 4 * H < z → 0 < η → η ≤ 1 / 6 →
        Odd Lminus → Even Lplus →
        (((z + 1 : ℕ) : ℝ) ^ 18) ≤
          (η / 4) * (2 : ℝ) ^ (Lminus + 1) →
        (((z + 1 : ℕ) : ℝ) ^ 18) ≤
          (η / 4) * (2 : ℝ) ^ (Lplus + 1) →
        1 ≤ η * (2 * (H : ℝ) * FullShiftSieve.roughEulerMass z) →
        FullShiftSieve.brunEndpointError z Lminus ≤
          (η / 2) * (X : ℝ) * FullShiftSieve.roughEulerMass z →
        FullShiftSieve.brunEndpointError z Lplus ≤
          η * (X : ℝ) * FullShiftSieve.roughEulerMass z ^ 2 →
        (exceptionalDyadicCount X : ℝ) ≤
          64 * (X : ℝ) * H * FullShiftSieve.roughEulerMass (y + 1) ^ 2 +
            4 * (H : ℝ) * (((y ^ S : ℕ) : ℝ) ^ 2) +
            (3 * η * X + 1) / H + (X : ℝ) / z + 1 := by
  obtain ⟨A, hA, hsmall⟩ := exists_paritySmallExceptionalGaps_upper_beta
  refine ⟨A, hA, ?_⟩
  intro X H y S z Lminus Lplus η hX hH hy hyX hHX hS hlog hbeta
    hz hHz hη hηsmall hLm hLp hpowm hpowl hlarge herrm herrp
  have hsmall' := hsmall hX hH hy hyX hHX hS hlog hbeta
  have hzero := roughOddZeroPoints_upper_brun hη hηsmall (by omega) hH hz
    (by omega) hLm hLp hpowm hpowl hlarge herrm herrp
  have hassembled := exceptionalDyadicCount_upper_of_component_bounds
    hX hH (by omega : 0 < z) hHz hsmall' hzero
  exact hassembled

/-! ## A cofinal choice of sieve parameters -/

/-- Binary logarithmic scale attached to the lower prime size. -/
def gapLogIndex (X : ℕ) : ℕ := Nat.log 2 X

/-- Square-root and fourth-root scales used for the short interval length. -/
def gapRootIndex (X : ℕ) : ℕ := Nat.sqrt (gapLogIndex X)

def gapFourthIndex (X : ℕ) : ℕ := Nat.sqrt (gapRootIndex X)

/-- Length of the even shift block.  It is of order `(log X)^(3/4)`. -/
def gapIntervalLength (X : ℕ) : ℕ :=
  gapRootIndex X * gapFourthIndex X

/-- The medium/long cutoff, of order `(log X)^2`. -/
def gapRoughCutoff (X : ℕ) : ℕ := gapLogIndex X ^ 2 + 3

/-- The small-gap beta-sieve cutoff. -/
def gapBetaCutoff (S X : ℕ) : ℕ :=
  2 ^ (gapLogIndex X / (16 * S))

/-- Relative moment tolerance. -/
noncomputable def gapSieveTolerance (X : ℕ) : ℝ :=
  1 / gapRootIndex X

/-- Opposite-parity Brun truncation depths. -/
def gapBrunMinus (X : ℕ) : ℕ :=
  100 * (Nat.log 2 (gapLogIndex X) + 1) + 1

def gapBrunPlus (X : ℕ) : ℕ :=
  100 * (Nat.log 2 (gapLogIndex X) + 1) + 2

lemma tendsto_natLog_two_atTop : Tendsto (Nat.log 2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro J
  refine ⟨2 ^ J, ?_⟩
  intro X hX
  exact Nat.le_log_of_pow_le (by norm_num) hX

lemma tendsto_gapLogIndex_atTop : Tendsto gapLogIndex atTop atTop :=
  tendsto_natLog_two_atTop

lemma tendsto_gapLogLogIndex_atTop :
    Tendsto (fun X ↦ Nat.log 2 (gapLogIndex X)) atTop atTop :=
  tendsto_natLog_two_atTop.comp tendsto_gapLogIndex_atTop

lemma tendsto_gapRootIndex_atTop : Tendsto gapRootIndex atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro r
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (tendsto_gapLogIndex_atTop.eventually
      (eventually_ge_atTop (r ^ 2)))
  exact ⟨X₀, fun X hX ↦ Nat.le_sqrt'.2 (hX₀ X hX)⟩

lemma tendsto_gapFourthIndex_atTop : Tendsto gapFourthIndex atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro w
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (tendsto_gapRootIndex_atTop.eventually
      (eventually_ge_atTop (w ^ 2)))
  exact ⟨X₀, fun X hX ↦ Nat.le_sqrt'.2 (hX₀ X hX)⟩

/-- Every fixed polynomial is eventually dominated by the binary
exponential, in a form convenient for exact natural-number inequalities. -/
lemma eventually_nat_mul_pow_le_two_pow (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * n ^ k ≤ 2 ^ n := by
  have hlittle : (fun n : ℕ ↦ (C : ℝ) * (n : ℝ) ^ k) =o[atTop]
      (fun n : ℕ ↦ (2 : ℝ) ^ n) :=
    (isLittleO_pow_const_const_pow_of_one_lt
      (R := ℝ) k (by norm_num : (1 : ℝ) < 2)).const_mul_left C
  have hbound := hlittle.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound] with n hn
  have hleft : 0 ≤ (C : ℝ) * (n : ℝ) ^ k := by positivity
  have hright : 0 ≤ (2 : ℝ) ^ n := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hleft,
    abs_of_nonneg hright, one_mul] at hn
  exact_mod_cast hn

lemma eventually_nat_mul_pow_le_two_pow_half (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * n ^ k ≤ 2 ^ (n / 2) := by
  have hbase := eventually_nat_mul_pow_le_two_pow (C * 3 ^ k) k
  have hhalf : Tendsto (fun n : ℕ ↦ n / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    exact ⟨2 * M, fun n hn ↦ by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      omega⟩
  filter_upwards [hhalf.eventually hbase, eventually_ge_atTop 2] with n hn htwo
  let m := n / 2
  have hnm : n ≤ 3 * m := by dsimp [m]; omega
  have hpow : n ^ k ≤ (3 * m) ^ k := Nat.pow_le_pow_left hnm k
  calc
    C * n ^ k ≤ C * (3 * m) ^ k := Nat.mul_le_mul_left C hpow
    _ = (C * 3 ^ k) * m ^ k := by rw [Nat.mul_pow]; ac_rfl
    _ ≤ 2 ^ m := hn
    _ = 2 ^ (n / 2) := rfl

lemma gapRoughEulerMass_lower {X : ℕ} (hJ : 2 ≤ gapLogIndex X) :
    Erdos469.naturalLinearMertensLower /
        (3 * (Nat.log 2 (gapLogIndex X) + 1 : ℕ) : ℝ) ≤
      FullShiftSieve.roughEulerMass (gapRoughCutoff X) := by
  let J := gapLogIndex X
  let q := Nat.log 2 J
  have hJ0 : J ≠ 0 := by dsimp [J]; omega
  have hJpow : J < 2 ^ (q + 1) := by
    dsimp [q]
    exact Nat.lt_pow_succ_log_self (by norm_num) J
  have hnat : J ^ 2 + 2 ≤ 2 ^ (2 * (q + 1) + 1) := by
    have hsquare : J ^ 2 < (2 ^ (q + 1)) ^ 2 :=
      Nat.pow_lt_pow_left hJpow (by norm_num)
    have hsquare' : J ^ 2 < 2 ^ (2 * (q + 1)) := by
      simpa only [← Nat.pow_mul, mul_comm] using hsquare
    have hpowtwo : 2 ≤ 2 ^ (2 * (q + 1)) := by
      have : 1 ≤ 2 * (q + 1) := by omega
      simpa using (pow_le_pow_right₀ (a := (2 : ℕ)) (by norm_num) this)
    rw [Nat.pow_add]
    norm_num only [Nat.pow_one, Nat.mul_two]
    omega
  have hlogpos : 0 < Real.log (J ^ 2 + 2 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < J ^ 2 + 2)
  have hlogupper : Real.log (J ^ 2 + 2 : ℕ) ≤
      (3 * (q + 1 : ℕ) : ℝ) := by
    have hpowposR : (0 : ℝ) < 2 ^ (2 * (q + 1) + 1) := by positivity
    calc
      Real.log (J ^ 2 + 2 : ℕ) ≤
          Real.log ((2 : ℝ) ^ (2 * (q + 1) + 1)) := by
        apply Real.strictMonoOn_log.monotoneOn
          (by
            show (0 : ℝ) < (J ^ 2 + 2 : ℕ)
            exact_mod_cast (show 0 < J ^ 2 + 2 by omega)) hpowposR
        exact_mod_cast hnat
      _ = ((2 * (q + 1) + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
      _ ≤ (3 * (q + 1 : ℕ) : ℝ) := by
        have hlogtwo : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          norm_num at this ⊢
          exact this
        have hq : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith
        push_cast
        nlinarith
  have hdenpos : (0 : ℝ) < 3 * (q + 1 : ℕ) := by positivity
  have hdiv : Erdos469.naturalLinearMertensLower /
      (3 * (q + 1 : ℕ) : ℝ) ≤
        Erdos469.naturalLinearMertensLower / Real.log (J ^ 2 + 2 : ℕ) := by
    exact div_le_div_of_nonneg_left Erdos469.naturalLinearMertensLower_pos.le
      hlogpos hlogupper
  exact hdiv.trans (by
    simpa [gapRoughCutoff, J] using
      (FullShiftSieve.roughEulerMass_bounds
        (z := gapRoughCutoff X) (by simp [gapRoughCutoff])).1)

lemma gapBetaEulerMass_upper {S X : ℕ} (hS : 0 < S)
    (hJ : 32 * S ≤ gapLogIndex X) :
    FullShiftSieve.roughEulerMass (gapBetaCutoff S X + 1) ≤
      (32 * (S : ℝ) * Erdos469.naturalLinearMertensUpper) /
        ((gapLogIndex X : ℝ) * Real.log 2) := by
  let J := gapLogIndex X
  let d := 16 * S
  let k := J / d
  let y := 2 ^ k
  have hd : 0 < d := by dsimp [d]; omega
  have hk : 0 < k := by
    dsimp [k]
    exact Nat.div_pos (by dsimp [d]; omega) hd
  have hquot : J < (k + 1) * d := by
    apply (Nat.div_lt_iff_lt_mul hd).mp
    dsimp [k]
    omega
  have hJk : J ≤ 32 * S * k := by
    dsimp [d] at hquot
    nlinarith
  have hy : 2 ≤ y := by
    dsimp [y]
    exact (show 2 ^ 1 ≤ 2 ^ k by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogy : Real.log (y : ℝ) = (k : ℝ) * Real.log 2 := by
    dsimp [y]
    push_cast
    rw [Real.log_pow]
  have hlogypos : 0 < Real.log (y : ℝ) := by rw [hlogy]; positivity
  have hmertens := (FullShiftSieve.roughEulerMass_bounds
    (z := y + 1) (by omega)).2
  have hbase : FullShiftSieve.roughEulerMass (y + 1) ≤
      Erdos469.naturalLinearMertensUpper /
        ((k : ℝ) * Real.log 2) := by
    simpa [hlogy] using hmertens
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hSnonneg : (0 : ℝ) ≤ S := by positivity
  have hUpos := Erdos469.naturalLinearMertensUpper_pos
  have hJkR : (J : ℝ) ≤ 32 * (S : ℝ) * k := by exact_mod_cast hJk
  have hcompare :
      Erdos469.naturalLinearMertensUpper / ((k : ℝ) * Real.log 2) ≤
        (32 * (S : ℝ) * Erdos469.naturalLinearMertensUpper) /
          ((J : ℝ) * Real.log 2) := by
    rw [div_le_div_iff₀ (mul_pos hkpos hlogtwo) (mul_pos hJpos hlogtwo)]
    calc
      Erdos469.naturalLinearMertensUpper * ((J : ℝ) * Real.log 2) =
          (J : ℝ) *
            (Erdos469.naturalLinearMertensUpper * Real.log 2) := by ring
      _ ≤ (32 * (S : ℝ) * k) *
            (Erdos469.naturalLinearMertensUpper * Real.log 2) :=
        mul_le_mul_of_nonneg_right hJkR (mul_nonneg hUpos.le hlogtwo.le)
      _ = 32 * (S : ℝ) * Erdos469.naturalLinearMertensUpper *
          ((k : ℝ) * Real.log 2) := by ring
  simpa [gapBetaCutoff, J, k, y] using hbase.trans hcompare

lemma gapBrun_power_bounds {X : ℕ} (hJ : 2 ≤ gapLogIndex X) :
    (((gapRoughCutoff X + 1 : ℕ) : ℝ) ^ 18) ≤
        (gapSieveTolerance X / 4) * (2 : ℝ) ^ (gapBrunMinus X + 1) ∧
      (((gapRoughCutoff X + 1 : ℕ) : ℝ) ^ 18) ≤
        (gapSieveTolerance X / 4) * (2 : ℝ) ^ (gapBrunPlus X + 1) := by
  let J := gapLogIndex X
  let r := Nat.sqrt J
  let q := Nat.log 2 J
  let z := J ^ 2 + 3
  let Lm := 100 * (q + 1) + 1
  let Lp := 100 * (q + 1) + 2
  have hJpow : J < 2 ^ (q + 1) := by
    dsimp [q]
    exact Nat.lt_pow_succ_log_self (by norm_num) J
  have hrpos : 0 < r := by dsimp [r]; rw [Nat.sqrt_pos]; omega
  have hrle : r ≤ 2 ^ (q + 1) :=
    (Nat.sqrt_le_self J).trans hJpow.le
  have hzle : z + 1 ≤ 2 ^ (2 * (q + 1) + 1) := by
    dsimp [z]
    have hsquare : J ^ 2 < (2 ^ (q + 1)) ^ 2 :=
      Nat.pow_lt_pow_left hJpow (by norm_num)
    have hsquare' : J ^ 2 < 2 ^ (2 * (q + 1)) := by
      simpa only [← Nat.pow_mul, mul_comm] using hsquare
    have hpowfour : 4 ≤ 2 ^ (2 * (q + 1)) := by
      have hexp : 2 ≤ 2 * (q + 1) := by omega
      simpa using (pow_le_pow_right₀ (a := (2 : ℕ)) (by norm_num) hexp)
    rw [Nat.pow_add]
    norm_num only [Nat.pow_one, Nat.mul_two]
    omega
  have hnatMinus : 4 * r * (z + 1) ^ 18 ≤ 2 ^ (Lm + 1) := by
    calc
      4 * r * (z + 1) ^ 18 ≤
          4 * 2 ^ (q + 1) * (2 ^ (2 * (q + 1) + 1)) ^ 18 := by
        gcongr
      _ = 2 ^ (37 * q + 57) := by
        rw [← Nat.pow_mul]
        calc
          4 * 2 ^ (q + 1) * 2 ^ ((2 * (q + 1) + 1) * 18) =
              2 ^ 2 * 2 ^ (q + 1) *
                2 ^ ((2 * (q + 1) + 1) * 18) := by norm_num
          _ = 2 ^ (2 + (q + 1) + (2 * (q + 1) + 1) * 18) := by
            rw [← Nat.pow_add, ← Nat.pow_add]
          _ = 2 ^ (37 * q + 57) := by congr 1 <;> omega
      _ ≤ 2 ^ (Lm + 1) := by
        apply pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
        dsimp [Lm]
        omega
  have hnatPlus : 4 * r * (z + 1) ^ 18 ≤ 2 ^ (Lp + 1) := by
    exact hnatMinus.trans (by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
      dsimp [Lm, Lp]
      omega)
  have hrposR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hconvert {L : ℕ} (h : 4 * r * (z + 1) ^ 18 ≤ 2 ^ L) :
      (((z + 1 : ℕ) : ℝ) ^ 18) ≤
        ((1 / (r : ℝ)) / 4) * (2 : ℝ) ^ L := by
    have hR : (4 : ℝ) * r * ((z + 1 : ℕ) : ℝ) ^ 18 ≤
        (2 : ℝ) ^ L := by exact_mod_cast h
    calc
      (((z + 1 : ℕ) : ℝ) ^ 18) ≤ (2 : ℝ) ^ L / (4 * r) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * r)]
        calc
          (((z + 1 : ℕ) : ℝ) ^ 18) * (4 * r) =
              4 * r * ((z + 1 : ℕ) : ℝ) ^ 18 := by ring
          _ ≤ (2 : ℝ) ^ L := hR
      _ = ((1 / (r : ℝ)) / 4) * (2 : ℝ) ^ L := by
        field_simp
  constructor
  · simpa [gapRoughCutoff, gapSieveTolerance, gapRootIndex,
      gapBrunMinus, J, r, q, z, Lm] using hconvert hnatMinus
  · simpa [gapRoughCutoff, gapSieveTolerance, gapRootIndex,
      gapBrunPlus, J, r, q, z, Lp] using hconvert hnatPlus

lemma gapBrunEndpointError_le_halfPower {X L : ℕ}
    (hJ : 2 ≤ gapLogIndex X)
    (hL : L ≤ gapBrunPlus X)
    (hscale : 1002 * (Nat.log 2 (gapLogIndex X) + 1) ^ 2 ≤
      gapLogIndex X) :
    FullShiftSieve.brunEndpointError (gapRoughCutoff X) L ≤
      (2 : ℝ) ^ (gapLogIndex X / 2) := by
  let J := gapLogIndex X
  let q := Nat.log 2 J
  let z := J ^ 2 + 3
  let Lp := 100 * (q + 1) + 2
  have hJpow : J < 2 ^ (q + 1) := by
    dsimp [q]
    exact Nat.lt_pow_succ_log_self (by norm_num) J
  have hzle : z ≤ 2 ^ (2 * q + 3) := by
    dsimp [z]
    have hsquare : J ^ 2 < (2 ^ (q + 1)) ^ 2 :=
      Nat.pow_lt_pow_left hJpow (by norm_num)
    have hsquare' : J ^ 2 < 2 ^ (2 * (q + 1)) := by
      simpa only [← Nat.pow_mul, mul_comm] using hsquare
    have hpowthree : 3 ≤ 2 ^ (2 * (q + 1)) := by
      have hexp : 2 ≤ 2 * (q + 1) := by omega
      have : 4 ≤ 2 ^ (2 * (q + 1)) := by
        simpa using (pow_le_pow_right₀ (a := (2 : ℕ)) (by norm_num) hexp)
      omega
    rw [show 2 * q + 3 = 2 * (q + 1) + 1 by omega, Nat.pow_add]
    norm_num only [Nat.pow_one, Nat.mul_two]
    omega
  have hL' : L ≤ Lp := by simpa [gapBrunPlus, J, q, Lp] using hL
  have hLp : Lp ≤ 102 * (q + 1) := by dsimp [Lp]; omega
  have hpowz : z ^ L ≤ 2 ^ ((2 * q + 3) * L) := by
    calc
      z ^ L ≤ (2 ^ (2 * q + 3)) ^ L := Nat.pow_le_pow_left hzle L
      _ = 2 ^ ((2 * q + 3) * L) := by rw [Nat.pow_mul]
  have hpowzpos : 1 ≤ z ^ L := one_le_pow₀ (by dsimp [z]; omega)
  have hnat : (z ^ L + 1) * 2 ^ L ≤ 2 ^ (J / 2) := by
    calc
      (z ^ L + 1) * 2 ^ L ≤ (2 * z ^ L) * 2 ^ L := by
        apply Nat.mul_le_mul_right
        omega
      _ ≤ (2 * 2 ^ ((2 * q + 3) * L)) * 2 ^ L := by gcongr
      _ = 2 ^ (1 + (2 * q + 3) * L + L) := by
        calc
          (2 * 2 ^ ((2 * q + 3) * L)) * 2 ^ L =
              (2 ^ 1 * 2 ^ ((2 * q + 3) * L)) * 2 ^ L := by norm_num
          _ = 2 ^ (1 + (2 * q + 3) * L + L) := by
            rw [← Nat.pow_add, ← Nat.pow_add]
      _ ≤ 2 ^ (J / 2) := by
        apply pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
        have hqscale : 501 * (q + 1) ^ 2 ≤ J / 2 := by
          apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
          nlinarith
        calc
          1 + (2 * q + 3) * L + L ≤ 501 * (q + 1) ^ 2 := by
            have := hL'.trans hLp
            nlinarith [sq_nonneg (q : ℤ)]
          _ ≤ J / 2 := hqscale
  simpa [FullShiftSieve.brunEndpointError, gapRoughCutoff, J, z] using
    (show (((z ^ L + 1 : ℕ) : ℝ) * (2 : ℝ) ^ L) ≤
      (2 : ℝ) ^ (J / 2) by exact_mod_cast hnat)

lemma eventually_gap_endpoint_scale :
    ∀ᶠ X : ℕ in atTop,
      1002 * (Nat.log 2 (gapLogIndex X) + 1) ^ 2 ≤ gapLogIndex X := by
  have hpoly := eventually_nat_mul_pow_le_two_pow 4008 2
  filter_upwards [tendsto_gapLogLogIndex_atTop.eventually hpoly,
    tendsto_gapLogLogIndex_atTop.eventually (eventually_ge_atTop 1),
    tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop 2)] with X hp hq hJ
  let J := gapLogIndex X
  let q := Nat.log 2 J
  have hpow : 2 ^ q ≤ J := by
    dsimp [q]
    exact Nat.pow_log_le_self 2 (by omega)
  have hquad : 1002 * (q + 1) ^ 2 ≤ 4008 * q ^ 2 := by nlinarith
  exact hquad.trans (hp.trans hpow)

lemma eventually_gap_brun_endpoint_hypotheses :
    ∀ᶠ X : ℕ in atTop,
      FullShiftSieve.brunEndpointError (gapRoughCutoff X) (gapBrunMinus X) ≤
          (gapSieveTolerance X / 2) * (X : ℝ) *
            FullShiftSieve.roughEulerMass (gapRoughCutoff X) ∧
        FullShiftSieve.brunEndpointError (gapRoughCutoff X) (gapBrunPlus X) ≤
          gapSieveTolerance X * (X : ℝ) *
            FullShiftSieve.roughEulerMass (gapRoughCutoff X) ^ 2 := by
  let M := Erdos469.naturalLinearMertensLower
  have hM : 0 < M := Erdos469.naturalLinearMertensLower_pos
  obtain ⟨K : ℕ, hK⟩ := exists_nat_ge (max (6 / M) (9 / M ^ 2))
  have hpoly := eventually_nat_mul_pow_le_two_pow_half K 3
  filter_upwards [tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop 2),
    eventually_gap_endpoint_scale,
    tendsto_gapLogIndex_atTop.eventually hpoly] with X hJ hscale hpolyX
  let J := gapLogIndex X
  let r := Nat.sqrt J
  let q := Nat.log 2 J
  let P : ℝ := (2 : ℝ) ^ (J / 2)
  let V := FullShiftSieve.roughEulerMass (gapRoughCutoff X)
  have hX0 : X ≠ 0 := by
    intro h
    subst X
    simp [gapLogIndex] at hJ
  have hpowXNat : 2 ^ J ≤ X := by
    dsimp [J]
    exact Nat.pow_log_le_self 2 hX0
  have hpowX : (2 : ℝ) ^ J ≤ X := by exact_mod_cast hpowXNat
  have hrpos : 0 < r := by dsimp [r]; rw [Nat.sqrt_pos]; omega
  have hrle : r ≤ J := Nat.sqrt_le_self J
  have hqle : q + 1 ≤ J := by
    dsimp [q]
    have := Nat.log_lt_self 2 (by omega : J ≠ 0)
    omega
  have hV := gapRoughEulerMass_lower (X := X) hJ
  change M / (3 * (q + 1 : ℕ) : ℝ) ≤ V at hV
  have hPm := gapBrunEndpointError_le_halfPower (X := X)
    (L := gapBrunMinus X) hJ (by simp [gapBrunMinus, gapBrunPlus]) hscale
  have hPp := gapBrunEndpointError_le_halfPower (X := X)
    (L := gapBrunPlus X) hJ le_rfl hscale
  have hPnonneg : 0 ≤ P := by positivity
  have hPsq : P ^ 2 ≤ (2 : ℝ) ^ J := by
    dsimp [P]
    rw [pow_two, ← pow_add]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hKsix : (6 : ℝ) ≤ M * K := by
    have : 6 / M ≤ (K : ℝ) := (le_max_left _ _).trans hK
    simpa [mul_comm] using (div_le_iff₀ hM).mp this
  have hKnine : (9 : ℝ) ≤ M ^ 2 * K := by
    have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
    have : 9 / M ^ 2 ≤ (K : ℝ) := (le_max_right _ _).trans hK
    simpa [mul_comm] using (div_le_iff₀ hM2).mp this
  have hpolyR : (K : ℝ) * (J : ℝ) ^ 3 ≤ P := by
    simpa only [J, P, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (show ((K * gapLogIndex X ^ 3 : ℕ) : ℝ) ≤
        ((2 ^ (gapLogIndex X / 2) : ℕ) : ℝ) by exact_mod_cast hpolyX)
  have hrR : (r : ℝ) ≤ J := by exact_mod_cast hrle
  have hqR : ((q + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hqle
  push_cast at hqR hV
  have hden1 : (6 : ℝ) * r * (q + 1) ≤ M * P := by
    have hmulrq : (r : ℝ) * (q + 1) ≤ (J : ℝ) * J :=
      mul_le_mul hrR hqR (by positivity) (by positivity)
    calc
      (6 : ℝ) * r * (q + 1) ≤ 6 * (J : ℝ) ^ 2 := by
        nlinarith
      _ ≤ (M * K) * (J : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hKsix (sq_nonneg _)
      _ ≤ M * ((K : ℝ) * (J : ℝ) ^ 3) := by
        have hJone : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
        have hsqcube : (J : ℝ) ^ 2 ≤ J ^ 3 := by nlinarith [sq_nonneg (J : ℝ)]
        calc
          (M * K) * (J : ℝ) ^ 2 = M * (K * (J : ℝ) ^ 2) := by ring
          _ ≤ M * (K * (J : ℝ) ^ 3) := by gcongr
      _ ≤ M * P := mul_le_mul_of_nonneg_left hpolyR hM.le
  have hden2 : (9 : ℝ) * r * (q + 1) ^ 2 ≤ M ^ 2 * P := by
    have hqSq : ((q : ℝ) + 1) ^ 2 ≤ (J : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hqR 2
    have hmulrq : (r : ℝ) * ((q : ℝ) + 1) ^ 2 ≤
        (J : ℝ) * J ^ 2 :=
      mul_le_mul hrR hqSq (by positivity) (by positivity)
    calc
      (9 : ℝ) * r * (q + 1) ^ 2 ≤ 9 * (J : ℝ) ^ 3 := by
        calc
          (9 : ℝ) * r * (q + 1) ^ 2 =
              9 * ((r : ℝ) * (q + 1) ^ 2) := by ring
          _ ≤ 9 * ((J : ℝ) * J ^ 2) :=
            mul_le_mul_of_nonneg_left hmulrq (by norm_num)
          _ = 9 * (J : ℝ) ^ 3 := by ring
      _ ≤ (M ^ 2 * K) * (J : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hKnine (by positivity)
      _ = M ^ 2 * ((K : ℝ) * (J : ℝ) ^ 3) := by ring
      _ ≤ M ^ 2 * P := mul_le_mul_of_nonneg_left hpolyR (sq_nonneg M)
  have hfirstP : P ≤ (1 / (r : ℝ) / 2) * (X : ℝ) * V := by
    have hdenpos : (0 : ℝ) < 6 * r * (q + 1) := by positivity
    have hmul : P * (6 * (r : ℝ) * (q + 1)) ≤ M * X := by
      calc
        P * (6 * (r : ℝ) * (q + 1)) ≤ P * (M * P) :=
          mul_le_mul_of_nonneg_left hden1 hPnonneg
        _ = M * P ^ 2 := by ring
        _ ≤ M * (2 : ℝ) ^ J := mul_le_mul_of_nonneg_left hPsq hM.le
        _ ≤ M * X := mul_le_mul_of_nonneg_left hpowX hM.le
    have hbase : P ≤ M * (X : ℝ) / (6 * r * (q + 1)) :=
      (le_div_iff₀ hdenpos).2 hmul
    calc
      P ≤ M * (X : ℝ) / (6 * r * (q + 1)) := hbase
      _ = (1 / (r : ℝ) / 2) * (X : ℝ) *
          (M / (3 * (q + 1))) := by field_simp; ring
      _ ≤ (1 / (r : ℝ) / 2) * (X : ℝ) * V := by
        exact mul_le_mul_of_nonneg_left hV (by positivity)
  have hsecondP : P ≤ (1 / (r : ℝ)) * (X : ℝ) * V ^ 2 := by
    have hdenpos : (0 : ℝ) < 9 * r * (q + 1) ^ 2 := by positivity
    have hmul : P * (9 * (r : ℝ) * (q + 1) ^ 2) ≤ M ^ 2 * X := by
      calc
        P * (9 * (r : ℝ) * (q + 1) ^ 2) ≤ P * (M ^ 2 * P) :=
          mul_le_mul_of_nonneg_left hden2 hPnonneg
        _ = M ^ 2 * P ^ 2 := by ring
        _ ≤ M ^ 2 * (2 : ℝ) ^ J :=
          mul_le_mul_of_nonneg_left hPsq (sq_nonneg M)
        _ ≤ M ^ 2 * X := mul_le_mul_of_nonneg_left hpowX (sq_nonneg M)
    have hbase : P ≤ M ^ 2 * (X : ℝ) / (9 * r * (q + 1) ^ 2) :=
      (le_div_iff₀ hdenpos).2 hmul
    calc
      P ≤ M ^ 2 * (X : ℝ) / (9 * r * (q + 1) ^ 2) := hbase
      _ = (1 / (r : ℝ)) * (X : ℝ) *
          (M / (3 * (q + 1))) ^ 2 := by field_simp; ring
      _ ≤ (1 / (r : ℝ)) * (X : ℝ) * V ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hV 2
  simpa [gapSieveTolerance, gapRootIndex, J, r, V] using
    And.intro (hPm.trans hfirstP) (hPp.trans hsecondP)

/-- The absolute beta-sieve constant can be absorbed by one fixed truncation
depth.  This choice is independent of the dyadic scale `X`. -/
lemma exists_admissible_beta_depth {A : ℝ} (hA : 1 ≤ A) :
    ∃ S : ℕ, 101 ≤ S ∧
      Real.log A ≤ 4 * ((S - 100 : ℕ) : ℝ) / 99 ∧
      (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) ≤ 1 := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  obtain ⟨n₁ : ℕ, hn₁⟩ := exists_pow_lt_of_lt_one
    (show 0 < (3 : ℝ) / (4 * A) by positivity)
    (by norm_num : (1 / 4 : ℝ) < 1)
  obtain ⟨n₂ : ℕ, hn₂⟩ := exists_nat_ge (99 * Real.log A / 4)
  let n := max (max n₁ n₂) 1
  refine ⟨n + 100, by
    have : 1 ≤ n := by dsimp [n]; exact le_max_right _ _
    omega, ?_, ?_⟩
  · have hn₂nNat : n₂ ≤ n := (le_max_right n₁ n₂).trans (le_max_left _ _)
    have hn₂n : (n₂ : ℝ) ≤ n := by exact_mod_cast hn₂nNat
    have hfour : (0 : ℝ) < 4 := by norm_num
    have hnlog : 99 * Real.log A / 4 ≤ (n : ℝ) := hn₂.trans hn₂n
    simp only [Nat.add_sub_cancel] at *
    linarith
  · have hn₁n : n₁ ≤ n := (le_max_left n₁ n₂).trans (le_max_left _ _)
    have hpow : (1 / 4 : ℝ) ^ n ≤ (1 / 4 : ℝ) ^ n₁ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn₁n
    have hsmall : (1 / 4 : ℝ) ^ n ≤ 3 / (4 * A) := hpow.trans hn₁.le
    simp only [Nat.add_sub_cancel]
    calc
      (4 * A / 3) * (1 / 4 : ℝ) ^ n ≤
          (4 * A / 3) * (3 / (4 * A)) := by gcongr
      _ = 1 := by field_simp

/-- A fixed multiple of the iterated binary logarithm is eventually below
the fourth-root scale. -/
lemma eventually_gap_logLog_le_fourth (C : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      C * (Nat.log 2 (gapLogIndex X) + 1) ≤ gapFourthIndex X := by
  have hpoly := eventually_nat_mul_pow_le_two_pow (16 * C ^ 4) 4
  filter_upwards [tendsto_gapLogLogIndex_atTop.eventually hpoly,
    tendsto_gapLogLogIndex_atTop.eventually (eventually_ge_atTop 1),
    tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop 1)] with X hp hq hJ
  let J := gapLogIndex X
  let q := Nat.log 2 J
  let a := C * (q + 1)
  have hqpow : 2 ^ q ≤ J := by
    dsimp [q]
    exact Nat.pow_log_le_self 2 (by omega)
  have ha4 : a ^ 4 ≤ J := by
    calc
      a ^ 4 = C ^ 4 * (q + 1) ^ 4 := by
        dsimp [a]
        rw [Nat.mul_pow]
      _ ≤ 16 * C ^ 4 * q ^ 4 := by
        have hq' : 1 ≤ q := by simpa [q, J] using hq
        have hqadd : q + 1 ≤ 2 * q := by omega
        have hpowadd : (q + 1) ^ 4 ≤ (2 * q) ^ 4 :=
          Nat.pow_le_pow_left hqadd 4
        calc
          C ^ 4 * (q + 1) ^ 4 ≤ C ^ 4 * (2 * q) ^ 4 :=
            Nat.mul_le_mul_left _ hpowadd
          _ = 16 * C ^ 4 * q ^ 4 := by
            rw [Nat.mul_pow]
            norm_num
            ring
      _ ≤ 2 ^ q := by simpa [J, q] using hp
      _ ≤ J := hqpow
  have ha2 : a ^ 2 ≤ Nat.sqrt J := by
    apply Nat.le_sqrt'.2
    simpa [← pow_mul] using ha4
  have ha : a ≤ Nat.sqrt (Nat.sqrt J) := Nat.le_sqrt'.2 ha2
  simpa [gapFourthIndex, gapRootIndex, J, q, a] using ha

/-- The elementary side conditions for the cofinal sieve parameters. -/
lemma eventually_gap_basic_parameter_hypotheses (S : ℕ) (hS : 0 < S) :
    ∀ᶠ X : ℕ in atTop,
      3 ≤ X ∧
      0 < gapIntervalLength X ∧
      2 ≤ gapBetaCutoff S X ∧
      gapBetaCutoff S X + 1 ≤ X ∧
      4 * gapIntervalLength X ≤ X ∧
      3 ≤ gapRoughCutoff X ∧
      4 * gapIntervalLength X < gapRoughCutoff X ∧
      0 < gapSieveTolerance X ∧
      gapSieveTolerance X ≤ 1 / 6 := by
  have hexp := eventually_nat_mul_pow_le_two_pow 4 1
  filter_upwards [eventually_ge_atTop 3,
    tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop (32 * S)),
    tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop 6),
    tendsto_gapRootIndex_atTop.eventually (eventually_ge_atTop 6),
    tendsto_gapLogIndex_atTop.eventually hexp] with X hX hJS hJ hr hfour
  let J := gapLogIndex X
  let r := Nat.sqrt J
  let w := Nat.sqrt r
  let H := r * w
  let y := 2 ^ (J / (16 * S))
  have hJpos : 0 < J := by dsimp [J]; omega
  have hrpos : 0 < r := by dsimp [r]; rw [Nat.sqrt_pos]; exact hJpos
  have hwpos : 0 < w := by dsimp [w]; rw [Nat.sqrt_pos]; exact hrpos
  have hr2 : r ^ 2 ≤ J := by dsimp [r]; exact Nat.sqrt_le' J
  have hwle : w ≤ r := by dsimp [w]; exact Nat.sqrt_le_self r
  have hHle : H ≤ J := by
    dsimp [H]
    calc
      r * w ≤ r * r := Nat.mul_le_mul_left r hwle
      _ = r ^ 2 := by ring
      _ ≤ J := hr2
  have hX0 : X ≠ 0 := by omega
  have hpowX : 2 ^ J ≤ X := by
    dsimp [J]
    exact Nat.pow_log_le_self 2 hX0
  have hk : 1 ≤ J / (16 * S) := by
    rw [Nat.le_div_iff_mul_le (by positivity : 0 < 16 * S)]
    omega
  have hy : 2 ≤ y := by
    dsimp [y]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk
  have hyX : y + 1 ≤ X := by
    have hyle : y ≤ 2 ^ J := by
      dsimp [y]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
        (Nat.div_le_self _ _)
    have hylt : y < 2 ^ J := by
      have hklt : J / (16 * S) < J := by
        apply Nat.div_lt_self hJpos
        omega
      exact Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) hklt
    omega
  have hfourJ : 4 * J ≤ 2 ^ J := by simpa [J] using hfour
  have hHX : 4 * H ≤ X :=
    (Nat.mul_le_mul_left 4 hHle).trans (hfourJ.trans hpowX)
  have hHz : 4 * H < J ^ 2 + 3 := by
    calc
      4 * H ≤ 4 * J := Nat.mul_le_mul_left 4 hHle
      _ < J ^ 2 + 3 := by nlinarith
  have heta : (0 : ℝ) < 1 / r := by positivity
  have hetasmall : (1 : ℝ) / r ≤ 1 / 6 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hr)
  simpa [gapLogIndex, gapRootIndex, gapFourthIndex, gapIntervalLength,
    gapBetaCutoff, gapRoughCutoff, gapSieveTolerance, J, r, w, H, y] using
    And.intro hX (And.intro (Nat.mul_pos hrpos hwpos)
      (And.intro hy (And.intro hyX (And.intro hHX
        (And.intro (by omega : 3 ≤ J ^ 2 + 3)
          (And.intro hHz (And.intro heta hetasmall)))))))

/-- The lower Mertens bound and the fourth-root choice make the Paley--Zygmund
large-mean hypothesis automatic. -/
lemma eventually_gap_large_mean_hypothesis :
    ∀ᶠ X : ℕ in atTop,
      1 ≤ gapSieveTolerance X *
        (2 * (gapIntervalLength X : ℝ) *
          FullShiftSieve.roughEulerMass (gapRoughCutoff X)) := by
  let M := Erdos469.naturalLinearMertensLower
  have hM : 0 < M := Erdos469.naturalLinearMertensLower_pos
  obtain ⟨C : ℕ, hC⟩ := exists_nat_ge (3 / (2 * M))
  filter_upwards [tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop 2),
    eventually_gap_logLog_le_fourth C] with X hJ hCw
  let J := gapLogIndex X
  let r := Nat.sqrt J
  let w := Nat.sqrt r
  let q := Nat.log 2 J
  let V := FullShiftSieve.roughEulerMass (gapRoughCutoff X)
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast (show 0 < r by dsimp [r]; rw [Nat.sqrt_pos]; omega)
  have hqpos : (0 : ℝ) < q + 1 := by positivity
  have hV := gapRoughEulerMass_lower (X := X) hJ
  change M / (3 * (q + 1 : ℕ) : ℝ) ≤ V at hV
  push_cast at hV
  have hCreal : 3 / (2 * M) ≤ (C : ℝ) := hC
  have hCwR : (C : ℝ) * ((q : ℝ) + 1) ≤ w := by exact_mod_cast hCw
  have hthree : (3 : ℝ) * (q + 1) ≤ 2 * M * w := by
    calc
      (3 : ℝ) * (q + 1) = (3 / (2 * M)) * (q + 1) * (2 * M) := by
        field_simp
      _ ≤ C * (q + 1) * (2 * M) := by gcongr
      _ ≤ w * (2 * M) := by gcongr
      _ = 2 * M * w := by ring
  have hWV : 1 ≤ 2 * (w : ℝ) * V := by
    have hden : (0 : ℝ) < 3 * (q + 1) := by positivity
    calc
      1 ≤ 2 * w * (M / (3 * (q + 1))) := by
        rw [show 2 * (w : ℝ) * (M / (3 * (q + 1))) =
          (2 * M * w) / (3 * (q + 1)) by ring]
        exact (le_div_iff₀ hden).2 (by simpa only [one_mul] using hthree)
      _ ≤ 2 * w * V := mul_le_mul_of_nonneg_left hV (by positivity)
  have hcancel : (1 / (r : ℝ)) * (2 * ((r * w : ℕ) : ℝ) * V) =
      2 * (w : ℝ) * V := by
    push_cast
    field_simp
  change 1 ≤ (1 / (r : ℝ)) * (2 * ((r * w : ℕ) : ℝ) * V)
  rw [hcancel]
  exact hWV

/-- The finite parity/beta/Brun estimate with one fixed beta depth and all
other parameters specialized to the cofinal choices above. -/
theorem exists_eventually_exceptionalDyadicCount_upper_concrete :
    ∃ S : ℕ, 0 < S ∧ ∀ᶠ X : ℕ in atTop,
      (exceptionalDyadicCount X : ℝ) ≤
        64 * (X : ℝ) * gapIntervalLength X *
            FullShiftSieve.roughEulerMass (gapBetaCutoff S X + 1) ^ 2 +
          4 * (gapIntervalLength X : ℝ) *
            ((((gapBetaCutoff S X) ^ S : ℕ) : ℝ) ^ 2) +
          (3 * gapSieveTolerance X * X + 1) / gapIntervalLength X +
          (X : ℝ) / gapRoughCutoff X + 1 := by
  obtain ⟨A, hA, hfinite⟩ := exists_exceptionalDyadicCount_upper_beta_brun
  obtain ⟨S, hS, hlog, hbeta⟩ := exists_admissible_beta_depth hA
  refine ⟨S, by omega, ?_⟩
  filter_upwards [eventually_gap_basic_parameter_hypotheses S (by omega),
    tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop 2),
    eventually_gap_brun_endpoint_hypotheses,
    eventually_gap_large_mean_hypothesis] with X hbasic hJ hendpoint hlarge
  rcases hbasic with ⟨hX, hH, hy, hyX, hHX, hz, hHz, heta, hetasmall⟩
  rcases gapBrun_power_bounds (X := X) hJ with ⟨hpowm, hpowp⟩
  rcases hendpoint with ⟨herrm, herrp⟩
  have hLm : Odd (gapBrunMinus X) := by
    refine ⟨50 * (Nat.log 2 (gapLogIndex X) + 1), ?_⟩
    simp [gapBrunMinus]
    ring
  have hLp : Even (gapBrunPlus X) := by
    refine ⟨50 * (Nat.log 2 (gapLogIndex X) + 1) + 1, ?_⟩
    simp [gapBrunPlus]
    ring
  exact hfinite hX hH hy hyX hHX hS hlog hbeta hz hHz heta hetasmall
    hLm hLp hpowm hpowp hlarge herrm herrp

/-- The beta-sieve endpoint term is exponentially smaller than the main
scale after the cofinal substitution. -/
lemma eventually_gap_beta_endpoint_natural (S : ℕ) (hS : 0 < S) :
    ∀ᶠ X : ℕ in atTop,
      4 * gapIntervalLength X * (gapBetaCutoff S X ^ S) ^ 2 *
          gapLogIndex X * gapFourthIndex X ≤ X := by
  have hpoly := eventually_nat_mul_pow_le_two_pow_half 4 2
  filter_upwards [tendsto_gapLogIndex_atTop.eventually hpoly,
    tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with X hpolyX hJ hX
  let J := gapLogIndex X
  let r := Nat.sqrt J
  let w := Nat.sqrt r
  let H := r * w
  let k := J / (16 * S)
  let y := 2 ^ k
  have hr2 : r ^ 2 ≤ J := by dsimp [r]; exact Nat.sqrt_le' J
  have hw2 : w ^ 2 ≤ r := by dsimp [w]; exact Nat.sqrt_le' r
  have hHJw : H * J * w ≤ J ^ 2 := by
    calc
      H * J * w = J * (r * w ^ 2) := by dsimp [H]; ring
      _ ≤ J * (r * r) := by gcongr
      _ ≤ J * J := by
        rw [show r * r = r ^ 2 by ring]
        gcongr
      _ = J ^ 2 := by ring
  have hkdiv : k * (16 * S) ≤ J := by
    dsimp [k]
    exact Nat.div_mul_le_self J (16 * S)
  have hexp : 2 * S * k ≤ J / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
    calc
      2 * S * k * 8 = k * (16 * S) := by ring
      _ ≤ J := hkdiv
  have hypow : (y ^ S) ^ 2 = 2 ^ (2 * S * k) := by
    dsimp [y]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hyexp : (y ^ S) ^ 2 ≤ 2 ^ (J / 8) := by
    rw [hypow]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hexp
  have hpowX : 2 ^ J ≤ X := by
    dsimp [J]
    exact Nat.pow_log_le_self 2 (by omega)
  calc
    4 * H * (y ^ S) ^ 2 * J * w = 4 * (H * J * w) * (y ^ S) ^ 2 := by ring
    _ ≤ 4 * J ^ 2 * 2 ^ (J / 8) := by gcongr
    _ ≤ 2 ^ (J / 2) * 2 ^ (J / 8) := by
      exact Nat.mul_le_mul_right _ (by simpa [J] using hpolyX)
    _ = 2 ^ (J / 2 + J / 8) := by rw [← pow_add]
    _ ≤ 2 ^ J := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
      omega
    _ ≤ X := hpowX

/-- Quantitative dyadic conclusion of the formalized sieve argument.  The
extra fourth-root saving is more than is needed for density one. -/
theorem exceptionalDyadicCount_isBigO_gapScale :
    (fun X : ℕ ↦ (exceptionalDyadicCount X : ℝ)) =O[atTop]
      (fun X : ℕ ↦ (X : ℝ) /
        ((gapLogIndex X : ℝ) * gapFourthIndex X)) := by
  obtain ⟨S, hS, hraw⟩ :=
    exists_eventually_exceptionalDyadicCount_upper_concrete
  let U := Erdos469.naturalLinearMertensUpper
  let B : ℝ := 32 * S * U / Real.log 2
  let C : ℝ := 64 * B ^ 2 + 16
  have hBpos : 0 < B := by
    dsimp [B, U]
    have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
    exact div_pos (mul_pos (mul_pos (by norm_num) hSreal)
      Erdos469.naturalLinearMertensUpper_pos) (Real.log_pos (by norm_num))
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hpolySq := eventually_nat_mul_pow_le_two_pow 1 2
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hraw,
    tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop (32 * S)),
    tendsto_gapLogIndex_atTop.eventually (eventually_ge_atTop 4),
    tendsto_gapRootIndex_atTop.eventually (eventually_ge_atTop 1),
    tendsto_gapFourthIndex_atTop.eventually (eventually_ge_atTop 1),
    tendsto_gapLogIndex_atTop.eventually hpolySq,
    eventually_gap_beta_endpoint_natural S hS] with X hrawX hJS hJ hr hw hJSq hendNat
  let J := gapLogIndex X
  let r := Nat.sqrt J
  let w := Nat.sqrt r
  let H := r * w
  let y := gapBetaCutoff S X
  let z := gapRoughCutoff X
  let G : ℝ := (X : ℝ) / ((J : ℝ) * w)
  have hJpos : 0 < J := by dsimp [J]; omega
  have hrpos : 0 < r := by dsimp [r]; rw [Nat.sqrt_pos]; exact hJpos
  have hwpos : 0 < w := by dsimp [w]; rw [Nat.sqrt_pos]; exact hrpos
  have hXpos : 0 < X := by
    by_contra hnot
    have : X = 0 := Nat.eq_zero_of_not_pos hnot
    subst X
    simp [J, gapLogIndex] at hJ
  have hr2 : r ^ 2 ≤ J := by dsimp [r]; exact Nat.sqrt_le' J
  have hw2 : w ^ 2 ≤ r := by dsimp [w]; exact Nat.sqrt_le' r
  have hwle : w ≤ r := by dsimp [w]; exact Nat.sqrt_le_self r
  have hHJw : H * J * w ≤ J ^ 2 := by
    calc
      H * J * w = J * (r * w ^ 2) := by dsimp [H]; ring
      _ ≤ J * (r * r) := by gcongr
      _ ≤ J * J := by
        rw [show r * r = r ^ 2 by ring]
        gcongr
      _ = J ^ 2 := by ring
  have hJupper : J ≤ 4 * r ^ 2 := by
    have hlt : J < (r + 1) ^ 2 := by
      dsimp [r]
      exact Nat.lt_succ_sqrt' J
    have hrone : 1 ≤ r := by omega
    have hradd : r + 1 ≤ 2 * r := by omega
    calc
      J ≤ (r + 1) ^ 2 := hlt.le
      _ ≤ (2 * r) ^ 2 := Nat.pow_le_pow_left hradd 2
      _ = 4 * r ^ 2 := by ring
  have hpowX : 2 ^ J ≤ X := by
    dsimp [J]
    exact Nat.pow_log_le_self 2 hXpos.ne'
  have hJwX : J * w ≤ X := by
    calc
      J * w ≤ J * J := by gcongr; exact (Nat.sqrt_le_self r).trans (Nat.sqrt_le_self J)
      _ = J ^ 2 := by ring
      _ ≤ 2 ^ J := by simpa [J] using hJSq
      _ ≤ X := hpowX
  have hDpos : (0 : ℝ) < (J : ℝ) * w := by positivity
  have hHpos : (0 : ℝ) < H := by positivity
  have hGnonneg : 0 ≤ G := by dsimp [G]; positivity
  have hV := gapBetaEulerMass_upper (S := S) (X := X) hS hJS
  have hV' : FullShiftSieve.roughEulerMass (y + 1) ≤ B / J := by
    calc
      FullShiftSieve.roughEulerMass (y + 1) ≤
          (32 * (S : ℝ) * Erdos469.naturalLinearMertensUpper) /
            ((J : ℝ) * Real.log 2) := by simpa [y, J] using hV
      _ = B / J := by
        dsimp [B, U]
        field_simp
  have hratio : (H : ℝ) / (J : ℝ) ^ 2 ≤ 1 / ((J : ℝ) * w) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (J : ℝ) ^ 2) hDpos]
    have hcast : ((H * J * w : ℕ) : ℝ) ≤ (J ^ 2 : ℕ) := by exact_mod_cast hHJw
    push_cast at hcast
    nlinarith
  have hshort : 64 * (X : ℝ) * H *
      FullShiftSieve.roughEulerMass (y + 1) ^ 2 ≤ 64 * B ^ 2 * G := by
    have hk : 1 ≤ J / (16 * S) := by
      rw [Nat.le_div_iff_mul_le (by positivity : 0 < 16 * S)]
      omega
    have hy2 : 2 ≤ y := by
      dsimp [y, gapBetaCutoff]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk
    have hlower := (FullShiftSieve.roughEulerMass_bounds
      (z := y + 1) (by omega)).1
    have hVnonneg : 0 ≤ FullShiftSieve.roughEulerMass (y + 1) := by
      have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy2)
      exact (div_pos Erdos469.naturalLinearMertensLower_pos hlogy).le.trans
        (by simpa using hlower)
    calc
      64 * (X : ℝ) * H * FullShiftSieve.roughEulerMass (y + 1) ^ 2 ≤
          64 * (X : ℝ) * H * (B / J) ^ 2 := by gcongr
      _ = 64 * B ^ 2 * (X : ℝ) * ((H : ℝ) / (J : ℝ) ^ 2) := by
        field_simp
      _ ≤ 64 * B ^ 2 * (X : ℝ) * (1 / ((J : ℝ) * w)) := by gcongr
      _ = 64 * B ^ 2 * G := by dsimp [G]; ring
  have hendCast : (4 * H * (y ^ S) ^ 2 * J * w : ℕ) ≤ X := by
    simpa [gapIntervalLength, gapRootIndex, gapFourthIndex, gapLogIndex,
      gapBetaCutoff, J, r, w, H, y] using hendNat
  have hendR : (4 : ℝ) * H * ((y ^ S : ℕ) : ℝ) ^ 2 ≤ G := by
    rw [show G = (X : ℝ) / ((J : ℝ) * w) by rfl,
      le_div_iff₀ hDpos]
    have hendCastR : ((4 * H * (y ^ S) ^ 2 * J * w : ℕ) : ℝ) ≤ X := by
      exact_mod_cast hendCast
    push_cast at hendCastR ⊢
    simpa only [mul_assoc] using hendCastR
  have hdenMedium : (0 : ℝ) < (r : ℝ) ^ 2 * w := by positivity
  have hfracMedium : (1 : ℝ) / ((r : ℝ) ^ 2 * w) ≤
      4 / ((J : ℝ) * w) := by
    rw [div_le_div_iff₀ hdenMedium hDpos]
    have hupperR : (J : ℝ) ≤ 4 * (r : ℝ) ^ 2 := by exact_mod_cast hJupper
    have hupperRw := mul_le_mul_of_nonneg_right hupperR
      (show (0 : ℝ) ≤ w by positivity)
    nlinarith
  have hmediumMain :
      (3 * gapSieveTolerance X * (X : ℝ)) / H ≤ 12 * G := by
    calc
      (3 * gapSieveTolerance X * (X : ℝ)) / H =
          (3 * (X : ℝ)) * (1 / ((r : ℝ) ^ 2 * w)) := by
        simp [gapSieveTolerance, gapRootIndex, gapIntervalLength,
          gapFourthIndex, J, r, w, H]
        field_simp
      _ ≤ (3 * (X : ℝ)) * (4 / ((J : ℝ) * w)) := by gcongr
      _ = 12 * G := by dsimp [G]; ring
  have hJleX : J ≤ X := by
    calc
      J = J * 1 := by omega
      _ ≤ J * w := Nat.mul_le_mul_left J hw
      _ ≤ X := hJwX
  have hJwXH : J * w ≤ X * H := by
    calc
      J * w ≤ X * w := Nat.mul_le_mul_right w hJleX
      _ ≤ X * H := by
        apply Nat.mul_le_mul_left X
        dsimp [H]
        calc
          w = 1 * w := by omega
          _ ≤ r * w := Nat.mul_le_mul_right w (by omega)
  have honeMedium : (1 : ℝ) / H ≤ G := by
    rw [show G = (X : ℝ) / ((J : ℝ) * w) by rfl,
      div_le_div_iff₀ hHpos hDpos]
    have hcast : ((J * w : ℕ) : ℝ) ≤ X * H := by exact_mod_cast hJwXH
    push_cast at hcast
    simpa only [one_mul] using hcast
  have hmedium :
      (3 * gapSieveTolerance X * X + 1) / H ≤ 13 * G := by
    rw [add_div]
    nlinarith
  have hzD : J * w ≤ z := by
    calc
      J * w ≤ J * J := by gcongr; exact (Nat.sqrt_le_self r).trans (Nat.sqrt_le_self J)
      _ = J ^ 2 := by ring
      _ ≤ z := by simp [z, gapRoughCutoff, J]
  have hzpos : (0 : ℝ) < z := by
    exact_mod_cast (show 0 < z by dsimp [z, gapRoughCutoff]; omega)
  have hlong : (X : ℝ) / z ≤ G := by
    rw [show G = (X : ℝ) / ((J : ℝ) * w) by rfl]
    exact div_le_div_of_nonneg_left (by positivity) hDpos (by exact_mod_cast hzD)
  have hone : (1 : ℝ) ≤ G := by
    rw [show G = (X : ℝ) / ((J : ℝ) * w) by rfl,
      le_div_iff₀ hDpos]
    have hcast : ((J * w : ℕ) : ℝ) ≤ X := by exact_mod_cast hJwX
    push_cast at hcast
    simpa only [one_mul] using hcast
  have htotal : (exceptionalDyadicCount X : ℝ) ≤ C * G := by
    have hraw' : (exceptionalDyadicCount X : ℝ) ≤
        64 * (X : ℝ) * H * FullShiftSieve.roughEulerMass (y + 1) ^ 2 +
          4 * (H : ℝ) * (((y ^ S : ℕ) : ℝ) ^ 2) +
          (3 * gapSieveTolerance X * X + 1) / H + (X : ℝ) / z + 1 := by
      simpa [gapIntervalLength, gapRootIndex, gapFourthIndex, gapLogIndex,
        gapBetaCutoff, gapRoughCutoff, J, r, w, H, y, z] using hrawX
    calc
      (exceptionalDyadicCount X : ℝ) ≤ _ := hraw'
      _ ≤ 64 * B ^ 2 * G + G + 13 * G + G + G := by gcongr
      _ = C * G := by dsimp [C]; ring
  have hcountnonneg : (0 : ℝ) ≤ exceptionalDyadicCount X := Nat.cast_nonneg _
  simpa [J, r, w, G, gapFourthIndex, gapRootIndex, Real.norm_eq_abs,
    abs_of_pos hCpos, abs_of_nonneg hcountnonneg,
    abs_of_nonneg hGnonneg] using htotal

/-- The real scale in the quantitative dyadic estimate. -/
noncomputable def gapScale (X : ℕ) : ℝ :=
  (X : ℝ) / ((gapLogIndex X : ℝ) * gapFourthIndex X)

lemma exceptionalDyadicCount_isBigO_gapScale' :
    (fun X : ℕ ↦ (exceptionalDyadicCount X : ℝ)) =O[atTop] gapScale := by
  change (fun X : ℕ ↦ (exceptionalDyadicCount X : ℝ)) =O[atTop]
    (fun X : ℕ ↦ (X : ℝ) /
      ((gapLogIndex X : ℝ) * gapFourthIndex X))
  exact exceptionalDyadicCount_isBigO_gapScale

/-- Along every fixed positive multiple of the `n`th prime, the dyadic
sieve scale is `o(n)`.  This is the precise PNT bridge used below. -/
lemma gapScale_mul_nthPrime_isLittleO (c : ℕ) (hc : 0 < c) :
    (fun N : ℕ ↦ gapScale (c * nthPrime N)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  obtain ⟨a, ha, hpna⟩ := nth_prime_asymp.isBigO.exists_pos
  have hcp : Tendsto (fun N : ℕ ↦ c * nthPrime N) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.mp tendsto_nth_prime_atTop) M
    refine ⟨N₀, fun N hN ↦ ?_⟩
    exact (hN₀ N hN).trans (by
      calc
        nthPrime N = 1 * nthPrime N := by omega
        _ ≤ c * nthPrime N := Nat.mul_le_mul_right _ (by omega))
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨W : ℕ, hW⟩ := exists_nat_ge
    ((2 * c * a * Real.log 2) / ε)
  filter_upwards [hpna.bound,
    (tendsto_gapFourthIndex_atTop.comp hcp).eventually (eventually_ge_atTop W),
    eventually_ge_atTop 2] with N hpn hw hN
  let p := nthPrime N
  let x := c * p
  let J := gapLogIndex x
  let w := gapFourthIndex x
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hpNat : N ≤ p :=
    (Nat.le_add_right N 2).trans (Nat.add_two_le_nth_prime N)
  have hpxNat : p ≤ x := by
    dsimp [x]
    calc
      p = 1 * p := by omega
      _ ≤ c * p := Nat.mul_le_mul_right _ (by omega)
  have hNxNat : N ≤ x := hpNat.trans hpxNat
  have hxpos : 0 < x := Nat.mul_pos hc (nthPrime_prime N).pos
  have hJpos : 0 < J := by
    dsimp [J, gapLogIndex]
    exact Nat.log_pos (by norm_num) (by omega)
  have hwpos : 0 < w := by
    dsimp [w, gapFourthIndex, gapRootIndex]
    rw [Nat.sqrt_pos, Nat.sqrt_pos]
    exact hJpos
  have hxpow : x < 2 ^ (J + 1) := by
    dsimp [J, gapLogIndex]
    exact Nat.lt_pow_succ_log_self (by norm_num) x
  have hlogNx : Real.log (N : ℝ) ≤ Real.log (x : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn hNpos
      (show (0 : ℝ) < x by exact_mod_cast hxpos) (by exact_mod_cast hNxNat)
  have hlogx : Real.log (x : ℝ) < ((J : ℝ) + 1) * Real.log 2 := by
    calc
      Real.log (x : ℝ) < Real.log ((2 : ℝ) ^ (J + 1)) := by
        exact Real.strictMonoOn_log
          (show (x : ℝ) ∈ Set.Ioi 0 by
            simp only [Set.mem_Ioi]
            exact_mod_cast hxpos)
          (show (2 : ℝ) ^ (J + 1) ∈ Set.Ioi 0 by
            simp only [Set.mem_Ioi]
            positivity)
          (by exact_mod_cast hxpow)
      _ = (((J + 1 : ℕ) : ℝ)) * Real.log 2 := by rw [Real.log_pow]
      _ = ((J : ℝ) + 1) * Real.log 2 := by push_cast; ring
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  have hlogbound : Real.log (N : ℝ) ≤ 2 * (J : ℝ) * Real.log 2 := by
    calc
      Real.log (N : ℝ) ≤ Real.log (x : ℝ) := hlogNx
      _ ≤ ((J : ℝ) + 1) * Real.log 2 := hlogx.le
      _ ≤ 2 * (J : ℝ) * Real.log 2 := by
        have hlogtwo := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
        nlinarith
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  have hpnonneg' : (0 : ℝ) ≤ nthPrime N := by positivity
  have hNlognonneg : (0 : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hpnonneg',
    abs_of_nonneg hNlognonneg] at hpn
  have hpn' : (p : ℝ) ≤ a * ((N : ℝ) * Real.log (N : ℝ)) := by
    simpa [p] using hpn
  have hxupper : (x : ℝ) ≤ c * a * ((N : ℝ) * Real.log (N : ℝ)) := by
    dsimp [x]
    push_cast
    calc
      (c : ℝ) * p ≤ (c : ℝ) *
          (a * ((N : ℝ) * Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hpn' (by positivity)
      _ = (c : ℝ) * a * ((N : ℝ) * Real.log (N : ℝ)) := by ring
  have hcoef : (2 * (c : ℝ) * a * Real.log 2) / ε ≤ w := by
    exact hW.trans (by exact_mod_cast hw)
  have hwRpos : (0 : ℝ) < w := by exact_mod_cast hwpos
  have hJwpos : (0 : ℝ) < (J : ℝ) * w := by positivity
  have hscale : gapScale x ≤ ε * (N : ℝ) := by
    calc
      gapScale x = (x : ℝ) / ((J : ℝ) * w) := by
        simp [gapScale, J, w]
      _ ≤ (c * a * ((N : ℝ) * Real.log (N : ℝ))) /
          ((J : ℝ) * w) := div_le_div_of_nonneg_right hxupper hJwpos.le
      _ ≤ (2 * c * a * Real.log 2 * (N : ℝ)) / w := by
        rw [div_le_div_iff₀ hJwpos hwRpos]
        calc
          ((c : ℝ) * a * ((N : ℝ) * Real.log (N : ℝ))) * w =
              ((c : ℝ) * a * N) * Real.log N * w := by ring
          _ ≤ ((c : ℝ) * a * N) * (2 * (J : ℝ) * Real.log 2) * w := by
            gcongr
          _ = (2 * (c : ℝ) * a * Real.log 2 * N) * ((J : ℝ) * w) := by ring
      _ ≤ ε * (N : ℝ) := by
        rw [div_le_iff₀ hwRpos]
        have hεw : 2 * (c : ℝ) * a * Real.log 2 ≤ ε * w := by
          have := (div_le_iff₀ hε).mp hcoef
          nlinarith
        nlinarith [show (0 : ℝ) ≤ N by positivity]
  have hscaleNonneg : 0 ≤ gapScale x := by simp [gapScale]; positivity
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  change ‖gapScale x‖ ≤ ε * ‖(N : ℝ)‖
  simpa [Real.norm_eq_abs, abs_of_nonneg hscaleNonneg,
    abs_of_nonneg hNnonneg] using hscale

lemma exceptionalDyadicCount_mul_nthPrime_isLittleO (c : ℕ) (hc : 0 < c) :
    (fun N : ℕ ↦ (exceptionalDyadicCount (c * nthPrime N) : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  have hO := exceptionalDyadicCount_isBigO_gapScale'.comp_tendsto
    (show Tendsto (fun N : ℕ ↦ c * nthPrime N) atTop atTop by
      rw [tendsto_atTop_atTop]
      intro M
      obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.mp tendsto_nth_prime_atTop) M
      exact ⟨N₀, fun N hN ↦ (hN₀ N hN).trans (by
        calc
          nthPrime N = 1 * nthPrime N := by omega
          _ ≤ c * nthPrime N := Nat.mul_le_mul_right _ (by omega))⟩)
  exact hO.trans_isLittleO (gapScale_mul_nthPrime_isLittleO c hc)

/-- A fixed dilation controls the primes at indices `N` and `2N`.  Only this
coarse consequence of PNT is needed to pass from prime-size shells to index
shells. -/
lemma exists_nthPrime_two_mul_le_dilation :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      nthPrime (2 * N) ≤ 2 ^ K * nthPrime N := by
  obtain ⟨a, ha, hupper⟩ := nth_prime_asymp.isBigO.exists_pos
  obtain ⟨b, hb, hlower⟩ := nth_prime_asymp.symm.isBigO.exists_pos
  obtain ⟨R : ℕ, hR⟩ := exists_nat_ge (4 * a * b)
  let K := Nat.log 2 (R + 1) + 1
  have hdouble : Tendsto (fun N : ℕ ↦ 2 * N) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    exact ⟨M, fun N hN ↦ by omega⟩
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  filter_upwards [hdouble.eventually hupper.bound, hlower.bound,
    eventually_ge_atTop 2] with N hup hlo hN
  let p := nthPrime N
  let p₂ := nthPrime (2 * N)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlog2N : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    rw [show ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) by push_cast; ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (N : ℝ) ≠ 0)]
    have hlogtwoN : Real.log 2 ≤ Real.log (N : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega))
        (by exact_mod_cast hN)
    linarith
  have hlog2N' : Real.log (2 * (N : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog2N
  have hp₂nonneg : (0 : ℝ) ≤ nthPrime (2 * N) := by positivity
  have hpnonneg : (0 : ℝ) ≤ nthPrime N := by positivity
  have htwoNlognonneg : (0 : ℝ) ≤
      ((2 * N : ℕ) : ℝ) * Real.log ((2 * N : ℕ) : ℝ) := by positivity
  have hNlognonneg : (0 : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hp₂nonneg,
    abs_of_nonneg htwoNlognonneg] at hup
  simp only [Real.norm_eq_abs, abs_of_nonneg hpnonneg,
    abs_of_nonneg hNlognonneg] at hlo
  have hup' : (p₂ : ℝ) ≤ a * (((2 * N : ℕ) : ℝ) *
      Real.log ((2 * N : ℕ) : ℝ)) := by simpa [p₂] using hup
  have hlo' : (N : ℝ) * Real.log (N : ℝ) ≤ b * p := by
    simpa [p] using hlo
  have hp₂R : (p₂ : ℝ) ≤ 4 * a * b * p := by
    calc
      (p₂ : ℝ) ≤ a * (((2 * N : ℕ) : ℝ) *
          Real.log ((2 * N : ℕ) : ℝ)) := hup'
      _ ≤ a * ((2 * (N : ℝ)) * (2 * Real.log (N : ℝ))) := by
        rw [show (((2 * N : ℕ) : ℝ)) = 2 * (N : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlog2N' (by positivity)) ha.le
      _ = (4 * a) * ((N : ℝ) * Real.log (N : ℝ)) := by ring
      _ ≤ (4 * a) * (b * p) := mul_le_mul_of_nonneg_left hlo' (by positivity)
      _ = 4 * a * b * p := by ring
  have hRp : (4 * a * b) * (p : ℝ) ≤ R * p :=
    mul_le_mul_of_nonneg_right hR (by positivity)
  have hRpow : R ≤ 2 ^ K := by
    have hlt : R + 1 < 2 ^ (Nat.log 2 (R + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (R + 1)
    dsimp [K]
    omega
  have htotalR : (p₂ : ℝ) ≤ (2 ^ K : ℕ) * p := by
    calc
      (p₂ : ℝ) ≤ 4 * a * b * p := hp₂R
      _ ≤ R * p := hRp
      _ ≤ (2 ^ K : ℕ) * p := by exact_mod_cast Nat.mul_le_mul_right p hRpow
  exact_mod_cast htotalR

/-- Exceptional indices in the dyadic index interval `[N,2N)`. -/
noncomputable def exceptionalIndexDyadicGaps (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter ExceptionalGap

noncomputable abbrev exceptionalIndexDyadicCount (N : ℕ) : ℕ :=
  (exceptionalIndexDyadicGaps N).card

lemma exists_binary_shell {p q K : ℕ} (hp : 0 < p) (hK : 0 < K)
    (hlower : p ≤ q) (hupper : q ≤ 2 ^ K * p) :
    ∃ j < K, 2 ^ j * p ≤ q ∧ q ≤ 2 ^ (j + 1) * p := by
  induction K with
  | zero => omega
  | succ K ih =>
      by_cases hK0 : K = 0
      · subst K
        refine ⟨0, by omega, ?_, ?_⟩
        · simpa using hlower
        · simpa using hupper
      · by_cases hq : q ≤ 2 ^ K * p
        · obtain ⟨j, hjK, hjlo, hjhi⟩ := ih (by omega) hq
          exact ⟨j, by omega, hjlo, hjhi⟩
        · refine ⟨K, by omega, Nat.le_of_not_ge hq, ?_⟩
          simpa [pow_succ, mul_assoc] using hupper

lemma exceptionalIndexDyadicGaps_subset_prime_shells {N K : ℕ}
    (hK : 0 < K) (hprime : nthPrime (2 * N) ≤ 2 ^ K * nthPrime N) :
    exceptionalIndexDyadicGaps N ⊆
      (Finset.range K).biUnion
        (fun j ↦ exceptionalDyadicGaps (2 ^ j * nthPrime N)) := by
  classical
  intro n hn
  have hnData := (Finset.mem_filter.mp hn).2
  have hnIco := (Finset.mem_filter.mp hn).1
  rw [Finset.mem_Ico] at hnIco
  have hpLower : nthPrime N ≤ nthPrime n :=
    nthPrime_strictMono.monotone hnIco.1
  have hpUpper : nthPrime n ≤ 2 ^ K * nthPrime N :=
    (nthPrime_strictMono.monotone hnIco.2.le).trans hprime
  obtain ⟨j, hjK, hjlo, hjhi⟩ := exists_binary_shell
    (nthPrime_prime N).pos hK hpLower hpUpper
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_range.mpr hjK, ?_⟩
  rw [exceptionalDyadicGaps, Finset.mem_filter]
  have hnRange : n < 2 * (2 ^ j * nthPrime N) := by
    have hnprime : n + 2 ≤ nthPrime n := Nat.add_two_le_nth_prime n
    calc
      n < nthPrime n := lt_of_lt_of_le (by omega) hnprime
      _ ≤ 2 ^ (j + 1) * nthPrime N := hjhi
      _ = 2 * (2 ^ j * nthPrime N) := by rw [pow_succ]; ring
  exact ⟨Finset.mem_range.mpr hnRange, hjlo,
    (by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hjhi), hnData⟩

lemma exceptionalIndexDyadicCount_le_prime_shell_sum {N K : ℕ}
    (hK : 0 < K) (hprime : nthPrime (2 * N) ≤ 2 ^ K * nthPrime N) :
    exceptionalIndexDyadicCount N ≤
      ∑ j ∈ Finset.range K, exceptionalDyadicCount (2 ^ j * nthPrime N) := by
  exact (Finset.card_le_card
    (exceptionalIndexDyadicGaps_subset_prime_shells hK hprime)).trans
      Finset.card_biUnion_le

/-- The number of exceptional indices in `[N,2N)` is `o(N)`. -/
theorem exceptionalIndexDyadicCount_isLittleO :
    (fun N : ℕ ↦ (exceptionalIndexDyadicCount N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  obtain ⟨K, hK, hprime⟩ := exists_nthPrime_two_mul_le_dilation
  have hsum :
      (fun N : ℕ ↦ ∑ j ∈ Finset.range K,
        (exceptionalDyadicCount (2 ^ j * nthPrime N) : ℝ)) =o[atTop]
          (fun N : ℕ ↦ (N : ℝ)) := by
    have hterms : ∀ j ∈ Finset.range K,
        (fun N : ℕ ↦ (exceptionalDyadicCount (2 ^ j * nthPrime N) : ℝ))
          =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
      intro j hj
      exact exceptionalDyadicCount_mul_nthPrime_isLittleO (2 ^ j) (by positivity)
    have hs := Asymptotics.IsLittleO.sum hterms
    exact hs.congr' (Eventually.of_forall fun N ↦ by simp) (EventuallyEq.refl _ _)
  have hbound :
      (fun N : ℕ ↦ (exceptionalIndexDyadicCount N : ℝ)) =O[atTop]
        (fun N : ℕ ↦ ∑ j ∈ Finset.range K,
          (exceptionalDyadicCount (2 ^ j * nthPrime N) : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hprime] with N hprimeN
    have hnat := exceptionalIndexDyadicCount_le_prime_shell_sum hK hprimeN
    have hleft : (0 : ℝ) ≤ exceptionalIndexDyadicCount N := Nat.cast_nonneg _
    have hright : (0 : ℝ) ≤ ∑ j ∈ Finset.range K,
        (exceptionalDyadicCount (2 ^ j * nthPrime N) : ℝ) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright, one_mul]
    exact_mod_cast hnat
  exact hbound.trans_isLittleO hsum

lemma exceptionalPrefixCount_two_mul (N : ℕ) :
    exceptionalPrefixCount (2 * N) =
      exceptionalPrefixCount N + exceptionalIndexDyadicCount N := by
  classical
  change ((Finset.range (2 * N)).filter ExceptionalGap).card =
    ((Finset.range N).filter ExceptionalGap).card +
      ((Finset.Ico N (2 * N)).filter ExceptionalGap).card
  have hunion : Finset.range (2 * N) =
      Finset.range N ∪ Finset.Ico N (2 * N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [hunion, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro n hn₁ hn₂
  have hnRange := (Finset.mem_filter.mp hn₁).1
  have hnIco := (Finset.mem_filter.mp hn₂).1
  rw [Finset.mem_range] at hnRange
  rw [Finset.mem_Ico] at hnIco
  omega

lemma exceptionalPrefixCount_pow_two (k : ℕ) :
    exceptionalPrefixCount (2 ^ k) =
      exceptionalPrefixCount 1 +
        ∑ j ∈ Finset.range k, exceptionalIndexDyadicCount (2 ^ j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_comm, exceptionalPrefixCount_two_mul, ih,
        Finset.sum_range_succ]
      omega

lemma exceptionalIndexDyadicCount_pow_two_isLittleO :
    (fun k : ℕ ↦ (exceptionalIndexDyadicCount (2 ^ k) : ℝ)) =o[atTop]
      (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
  have hpow : Tendsto (fun k : ℕ ↦ 2 ^ k) atTop atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  have hcomp := exceptionalIndexDyadicCount_isLittleO.comp_tendsto hpow
  apply hcomp.congr'
  · exact Eventually.of_forall fun _ ↦ rfl
  · filter_upwards with k
    simp only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat]

lemma tendsto_sum_two_pow_atTop :
    Tendsto (fun k : ℕ ↦ ∑ j ∈ Finset.range k, (2 : ℝ) ^ j) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨m : ℕ, hm⟩ := exists_nat_ge M
  refine ⟨m, fun k hk ↦ hm.trans ?_⟩
  calc
    (m : ℝ) = ∑ _j ∈ Finset.range m, (1 : ℝ) := by simp
    _ ≤ ∑ j ∈ Finset.range m, (2 : ℝ) ^ j := by
      gcongr with j hj
      exact one_le_pow₀ (by norm_num)
    _ ≤ ∑ j ∈ Finset.range k, (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono hk
      · intro j hjk hjm
        positivity

lemma sum_exceptionalIndexDyadicCount_pow_two_isLittleO :
    (fun k : ℕ ↦ ∑ j ∈ Finset.range k,
      (exceptionalIndexDyadicCount (2 ^ j) : ℝ)) =o[atTop]
        (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
  have hsum :
      (fun k : ℕ ↦ ∑ j ∈ Finset.range k,
        (exceptionalIndexDyadicCount (2 ^ j) : ℝ)) =o[atTop]
          (fun k : ℕ ↦ ∑ j ∈ Finset.range k, (2 : ℝ) ^ j) :=
    exceptionalIndexDyadicCount_pow_two_isLittleO.sum_range
      (fun _ ↦ by positivity) tendsto_sum_two_pow_atTop
  have hgeom :
      (fun k : ℕ ↦ ∑ j ∈ Finset.range k, (2 : ℝ) ^ j) =O[atTop]
        (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with k
    have hsumNonneg : 0 ≤ ∑ j ∈ Finset.range k, (2 : ℝ) ^ j := by positivity
    have hpowNonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
      abs_of_nonneg hpowNonneg, one_mul]
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    norm_num
  exact hsum.trans_isBigO hgeom

lemma exceptionalPrefixCount_pow_two_isLittleO :
    (fun k : ℕ ↦ (exceptionalPrefixCount (2 ^ k) : ℝ)) =o[atTop]
      (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
  have hconst : (fun _k : ℕ ↦ (exceptionalPrefixCount 1 : ℝ)) =o[atTop]
      (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
    have hone : (fun _k : ℕ ↦ (1 : ℝ)) =o[atTop]
        (fun k : ℕ ↦ (2 : ℝ) ^ k) := by
      simpa using (isLittleO_pow_const_const_pow_of_one_lt
        (R := ℝ) 0 (by norm_num : (1 : ℝ) < 2))
    simpa only [mul_one] using
      hone.const_mul_left (exceptionalPrefixCount 1 : ℝ)
  have hadd := hconst.add sum_exceptionalIndexDyadicCount_pow_two_isLittleO
  apply hadd.congr'
  · filter_upwards with k
    have heq := congrArg (fun n : ℕ ↦ (n : ℝ))
      (exceptionalPrefixCount_pow_two k).symm
    push_cast at heq
    exact heq
  · exact EventuallyEq.refl _ _

lemma tendsto_log_succ_atTop :
    Tendsto (fun N : ℕ ↦ Nat.log 2 N + 1) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.mp tendsto_natLog_two_atTop) M
  exact ⟨N₀, fun N hN ↦ by have := hN₀ N hN; omega⟩

lemma prefixCount_mono_aux (S : Set ℕ) : Monotone (prefixCount S) := by
  intro M N hMN
  classical
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hn.1).trans_le hMN), hn.2⟩

/-- The complete quantitative-to-density transfer on the index scale. -/
theorem exceptionalPrefixCount_isLittleO :
    (fun N : ℕ ↦ (exceptionalPrefixCount N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  let k : ℕ → ℕ := fun N ↦ Nat.log 2 N + 1
  have hpower := exceptionalPrefixCount_pow_two_isLittleO.comp_tendsto
    (show Tendsto k atTop atTop by simpa [k] using tendsto_log_succ_atTop)
  have hcover :
      (fun N : ℕ ↦ (exceptionalPrefixCount N : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (exceptionalPrefixCount (2 ^ k N) : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpow : N ≤ 2 ^ k N := by
      have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N
      simpa [k] using hlt.le
    have hmono := prefixCount_mono_aux exceptionalGapIndices hNpow
    have hleft : (0 : ℝ) ≤ exceptionalPrefixCount N := Nat.cast_nonneg _
    have hright : (0 : ℝ) ≤ exceptionalPrefixCount (2 ^ k N) := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_of_nonneg hleft,
      abs_of_nonneg hright, one_mul]
    exact_mod_cast hmono
  have hpowscale :
      (fun N : ℕ ↦ ((2 : ℝ) ^ k N)) =O[atTop]
        (fun N : ℕ ↦ (N : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hpowlog : 2 ^ Nat.log 2 N ≤ N :=
      Nat.pow_log_le_self 2 (by omega)
    have hbound : 2 ^ k N ≤ 2 * N := by
      simpa [k, pow_succ, mul_comm, mul_left_comm, mul_assoc] using
        Nat.mul_le_mul_left 2 hpowlog
    have hleft : (0 : ℝ) ≤ (2 : ℝ) ^ k N := by positivity
    have hright : (0 : ℝ) ≤ (N : ℝ) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg hleft,
      abs_of_nonneg hright]
    exact_mod_cast hbound
  exact hcover.trans_isLittleO (hpower.trans_isBigO hpowscale)

@[simp] lemma exceptionalGapIndices_eq_compl :
    exceptionalGapIndices = goodGapIndicesᶜ := by
  ext n
  simp [exceptionalGapIndices, goodGapIndices, ExceptionalGap]

/-! ## The elementary density transfer -/

/-- Away from the empty initial interval, the partial density of a complement
is one minus the original partial density. -/
lemma partialDensity_compl (S : Set ℕ) (n : ℕ) (hn : 0 < n) :
    Sᶜ.partialDensity Set.univ n = 1 - S.partialDensity Set.univ n := by
  have hsubset : S ∩ Iio n ⊆ Iio n := inter_subset_right
  have hcard : (Sᶜ ∩ Iio n).ncard = n - (S ∩ Iio n).ncard := by
    calc
      (Sᶜ ∩ Iio n).ncard = (Iio n \ (S ∩ Iio n)).ncard := by
        congr 1
        ext x
        simp [and_comm]
      _ = (Iio n).ncard - (S ∩ Iio n).ncard := Set.ncard_sdiff hsubset
      _ = n - (S ∩ Iio n).ncard := by simp
  simp only [Set.partialDensity]
  simp only [inter_univ, univ_inter]
  rw [hcard, show (Iio n).ncard = n by simp]
  have hle : (S ∩ Iio n).ncard ≤ n := by
    simpa using Set.ncard_le_ncard hsubset
  rw [Nat.cast_sub hle]
  field_simp

/-- A zero-density exceptional set has a density-one complement. -/
lemma hasDensity_compl_one_of_zero (S : Set ℕ) (hS : S.HasDensity 0) :
    Sᶜ.HasDensity 1 := by
  rw [Set.HasDensity] at hS ⊢
  have hsub := hS.const_sub 1
  norm_num at hsub ⊢
  apply hsub.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (partialDensity_compl S n hn).symm

/-- The final logical transfer used by the resolution: proving that the
exceptional gaps have density zero is exactly enough for Erdős's assertion. -/
lemma goodGapIndices_density_one_of_exceptional_density_zero
    (h : exceptionalGapIndices.HasDensity 0) :
    goodGapIndices.HasDensity 1 := by
  have hc := hasDensity_compl_one_of_zero exceptionalGapIndices h
  rw [exceptionalGapIndices_eq_compl, compl_compl] at hc
  exact hc

/-- `prefixCount` is the numerator occurring in natural partial density. -/
lemma prefixCount_eq_ncard (S : Set ℕ) (N : ℕ) :
    prefixCount S N = (S ∩ Iio N).ncard := by
  classical
  change ((Finset.range N).filter (· ∈ S)).card = (S ∩ Iio N).ncard
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_comm]

/-- Partial density on the naturals is the corresponding prefix count divided
by the prefix length. -/
lemma partialDensity_eq_prefixCount_ratio (S : Set ℕ) (N : ℕ) :
    S.partialDensity Set.univ N = (prefixCount S N : ℝ) / N := by
  rw [Set.partialDensity]
  simp only [inter_univ, univ_inter]
  rw [← prefixCount_eq_ncard]
  simp

/-- A vanishing prefix-count ratio gives natural density zero. -/
theorem hasDensity_zero_of_prefixCount_ratio_tendsto (S : Set ℕ)
    (h : Tendsto (fun N : ℕ ↦ (prefixCount S N : ℝ) / N) atTop (𝓝 0)) :
    S.HasDensity 0 := by
  rw [Set.HasDensity]
  simpa only [partialDensity_eq_prefixCount_ratio] using h

/-- The exceptional gaps have natural density zero. -/
theorem exceptionalGapIndices_density_zero :
    exceptionalGapIndices.HasDensity 0 := by
  apply hasDensity_zero_of_prefixCount_ratio_tendsto
  simpa only [Pi.div_apply] using
    exceptionalPrefixCount_isLittleO.tendsto_div_nhds_zero

/-- Erdős Problem 682, in its literal density-one form. -/
theorem erdos_682 :
    {n : ℕ | ∃ m : ℕ,
      nthPrime n < m ∧ m < nthPrime (n + 1) ∧
        nthPrime (n + 1) - nthPrime n ≤ Nat.minFac m}.HasDensity 1 := by
  change goodGapIndices.HasDensity 1
  exact goodGapIndices_density_one_of_exceptional_density_zero
    exceptionalGapIndices_density_zero

lemma tendsto_const_div_log_nat (c : ℝ) :
    Tendsto (fun N : ℕ ↦ c / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hlog) :
      Tendsto (fun N : ℕ ↦ c * (Real.log (N : ℝ))⁻¹) atTop (𝓝 (c * 0)))

/-- The paper's correctly indexed quantitative corollary,
`# exceptional indices below N = O(N / log N)`, implies density zero. -/
theorem hasDensity_zero_of_prefixCount_isBigO (S : Set ℕ)
    (h : (fun N : ℕ ↦ (prefixCount S N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ))) :
    S.HasDensity 0 := by
  apply hasDensity_zero_of_prefixCount_ratio_tendsto
  obtain ⟨c, hc⟩ := h.bound
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hc, eventually_gt_atTop (1 : ℕ)] with N hN hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN1)
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN1)
    have hcountnonneg : (0 : ℝ) ≤ (prefixCount S N : ℝ) := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_of_nonneg hcountnonneg,
      abs_of_pos (div_pos hNpos hlogpos)] at hN
    rw [div_le_iff₀ hNpos]
    calc
      (prefixCount S N : ℝ) ≤ c * ((N : ℝ) / Real.log (N : ℝ)) := hN
      _ = (c / Real.log (N : ℝ)) * N := by ring
  · exact tendsto_const_div_log_nat c

/-- Specialization of the quantitative index bridge to exceptional gaps. -/
theorem exceptionalGapIndices_density_zero_of_prefix_isBigO
    (h : (fun N : ℕ ↦ (exceptionalPrefixCount N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ))) :
    exceptionalGapIndices.HasDensity 0 :=
  hasDensity_zero_of_prefixCount_isBigO exceptionalGapIndices h

/-- Once the source-faithful first-`N` estimate is available, Erdős's
density-one conclusion follows with no further number theory. -/
theorem goodGapIndices_density_one_of_prefix_isBigO
    (h : (fun N : ℕ ↦ (exceptionalPrefixCount N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ))) :
    goodGapIndices.HasDensity 1 :=
  goodGapIndices_density_one_of_exceptional_density_zero
    (exceptionalGapIndices_density_zero_of_prefix_isBigO h)

/-- Monotonicity of prefix counts. -/
lemma prefixCount_mono (S : Set ℕ) : Monotone (prefixCount S) := by
  intro M N hMN
  classical
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hn.1).trans_le hMN), hn.2⟩

/-- Prime-number-theorem scale conversion.  A cumulative prime-size estimate
`O(X / log^2 X)` becomes the correctly indexed estimate `O(N / log N)`.
This is the one-log correction to the wording on the local problem page. -/
theorem prefixCount_isBigO_of_primeScaleCount_isBigO (S : Set ℕ)
    (h : (fun X : ℕ ↦ (primeScaleCount S X : ℝ)) =O[atTop]
      (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ) ^ 2)) :
    (fun N : ℕ ↦ (prefixCount S N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨a, ha, hpna⟩ := nth_prime_asymp.isBigO.exists_pos
  obtain ⟨b, hb, hsource⟩ := h.exists_pos
  apply Asymptotics.IsBigO.of_bound (b * a)
  filter_upwards [hpna.bound, tendsto_nth_prime_atTop.eventually hsource.bound,
    eventually_gt_atTop (1 : ℕ)] with N hpn hsrc hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hnthNat : N ≤ nth_prime N :=
    (Nat.le_add_right N 2).trans (Nat.add_two_le_nth_prime N)
  have hnthpos : (0 : ℝ) < nth_prime N := by
    exact_mod_cast (Nat.prime_nth_prime N).pos
  have hlognthpos : 0 < Real.log (nth_prime N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime N).one_lt)
  have hlogle : Real.log (N : ℝ) ≤ Real.log (nth_prime N : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn hNpos hnthpos (by exact_mod_cast hnthNat)
  have hNlognonneg : 0 ≤ (N : ℝ) * Real.log (N : ℝ) :=
    mul_nonneg hNpos.le hlogNpos.le
  have hnthnonneg : (0 : ℝ) ≤ nth_prime N := hnthpos.le
  simp only [Real.norm_eq_abs, abs_of_nonneg hnthnonneg,
    abs_of_nonneg hNlognonneg] at hpn
  have hscale :
      (nth_prime N : ℝ) / Real.log (nth_prime N : ℝ) ^ 2 ≤
        a * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      (nth_prime N : ℝ) / Real.log (nth_prime N : ℝ) ^ 2 ≤
          (a * ((N : ℝ) * Real.log (N : ℝ))) /
            Real.log (nth_prime N : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hpn (sq_nonneg _)
      _ ≤ (a * ((N : ℝ) * Real.log (N : ℝ))) /
            Real.log (N : ℝ) ^ 2 := by
        gcongr
      _ = a * ((N : ℝ) / Real.log (N : ℝ)) := by
        field_simp
  have hsource_nonneg :
      0 ≤ (nth_prime N : ℝ) / Real.log (nth_prime N : ℝ) ^ 2 :=
    div_nonneg hnthnonneg (sq_nonneg _)
  have hcountSucc_nonneg : (0 : ℝ) ≤ prefixCount S (N + 1) := Nat.cast_nonneg _
  have hcount :
      (prefixCount S N : ℝ) ≤ (b * a) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      (prefixCount S N : ℝ) ≤ prefixCount S (N + 1) := by
        exact_mod_cast prefixCount_mono S (Nat.le_succ N)
      _ ≤ b * ((nth_prime N : ℝ) / Real.log (nth_prime N : ℝ) ^ 2) := by
        simpa only [primeScaleCount, pi_nth_prime, Real.norm_eq_abs,
          abs_of_nonneg hcountSucc_nonneg, abs_of_nonneg hsource_nonneg] using hsrc
      _ ≤ b * (a * ((N : ℝ) / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hscale hb.le
      _ = (b * a) * ((N : ℝ) / Real.log (N : ℝ)) := by ring
  have hratio_nonneg : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg hNpos.le hlogNpos.le
  have hprefixnonneg : (0 : ℝ) ≤ (prefixCount S N : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hprefixnonneg,
    abs_of_nonneg hratio_nonneg] using hcount

/-- The cumulative sharp Gafni--Tao scale implies the first-`N` exceptional
index estimate. -/
theorem exceptionalPrefixCount_isBigO_of_primePrefix_isBigO
    (h : (fun X : ℕ ↦ (exceptionalPrimePrefixCount X : ℝ)) =O[atTop]
      (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ) ^ 2)) :
    (fun N : ℕ ↦ (exceptionalPrefixCount N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / Real.log (N : ℝ)) :=
  prefixCount_isBigO_of_primeScaleCount_isBigO exceptionalGapIndices h

/-- A cumulative `O(X/log^2 X)` bound on the lower-prime scale already
implies Erdős's density-one conclusion. -/
theorem goodGapIndices_density_one_of_primePrefix_isBigO
    (h : (fun X : ℕ ↦ (exceptionalPrimePrefixCount X : ℝ)) =O[atTop]
      (fun X : ℕ ↦ (X : ℝ) / Real.log (X : ℝ) ^ 2)) :
    goodGapIndices.HasDensity 1 :=
  goodGapIndices_density_one_of_prefix_isBigO
    (exceptionalPrefixCount_isBigO_of_primePrefix_isBigO h)

/-! ## Erdős's explicit conditional family -/

/-- The small primes used by Erdős to cover the block `2184, ..., 2200`. -/
def coverPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13}

lemma coverPrime_prime {p : ℕ} (hp : p ∈ coverPrimes) : Nat.Prime p := by
  simp [coverPrimes] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma coverPrime_lt_eighteen {p : ℕ} (hp : p ∈ coverPrimes) : p < 18 := by
  simp [coverPrimes] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma coverPrime_dvd_30030 {p : ℕ} (hp : p ∈ coverPrimes) : p ∣ 30030 := by
  simp [coverPrimes] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma block_2184_2200_covered (r : ℕ) (hlo : 2184 ≤ r) (hhi : r ≤ 2200) :
    ∃ p ∈ coverPrimes, p ∣ r := by
  interval_cases r <;> norm_num [coverPrimes]

lemma shifted_interior_has_small_factor (d m : ℕ)
    (hleft : 2183 + 30030 * d < m) (hright : m < 2201 + 30030 * d) :
    ∃ p ∈ coverPrimes, p ∣ m := by
  let j := m - (2183 + 30030 * d)
  have hjlo : 1 ≤ j := by
    dsimp [j]
    omega
  have hjhi : j ≤ 17 := by
    dsimp [j]
    omega
  have hm : m = (2183 + j) + 30030 * d := by
    dsimp [j]
    omega
  obtain ⟨p, hpcover, hpbase⟩ :=
    block_2184_2200_covered (2183 + j) (by omega) (by omega)
  refine ⟨p, hpcover, ?_⟩
  rw [hm]
  exact hpbase.add (dvd_mul_of_dvd_left (coverPrime_dvd_30030 hpcover) d)

lemma shifted_interior_minFac_lt (d m : ℕ)
    (hleft : 2183 + 30030 * d < m) (hright : m < 2201 + 30030 * d) :
    Nat.minFac m < 18 := by
  obtain ⟨p, hpcover, hpm⟩ := shifted_interior_has_small_factor d m hleft hright
  exact (Nat.minFac_le_of_dvd (coverPrime_prime hpcover).two_le hpm).trans_lt
    (coverPrime_lt_eighteen hpcover)

lemma shifted_interior_not_prime (d m : ℕ)
    (hleft : 2183 + 30030 * d < m) (hright : m < 2201 + 30030 * d) :
    ¬Nat.Prime m := by
  intro hmprime
  have hmin := shifted_interior_minFac_lt d m hleft hright
  rw [hmprime.minFac_eq] at hmin
  omega

/-- If the two linear forms in Erdős's construction are prime, they are
successive primes and give an exceptional gap of length 18. -/
theorem erdos_conditional_counterexample (d : ℕ)
    (hleft : Nat.Prime (2183 + 30030 * d))
    (hright : Nat.Prime (2201 + 30030 * d)) :
    ∃ n : ℕ,
      nthPrime n = 2183 + 30030 * d ∧
      nthPrime (n + 1) = 2201 + 30030 * d ∧
      ExceptionalGap n := by
  have hleft_range : 2183 + 30030 * d ∈ Set.range nthPrime := by
    rw [Nat.range_nth_of_infinite Nat.infinite_setOfPred_prime]
    exact hleft
  obtain ⟨n, hn⟩ := hleft_range
  have hright_range : 2201 + 30030 * d ∈ Set.range nthPrime := by
    rw [Nat.range_nth_of_infinite Nat.infinite_setOfPred_prime]
    exact hright
  obtain ⟨k, hk⟩ := hright_range
  have hnk : n < k := by
    by_contra hnot
    have hkn : k ≤ n := Nat.le_of_not_gt hnot
    have hvalues : nthPrime k ≤ nthPrime n := nthPrime_strictMono.monotone hkn
    rw [hn, hk] at hvalues
    omega
  have hkn : k ≤ n + 1 := by
    by_contra hnot
    have hn1k : n + 1 < k := Nat.lt_of_not_ge hnot
    have hp_between_left :
        2183 + 30030 * d < nthPrime (n + 1) := by
      rw [← hn]
      exact nthPrime_lt_succ n
    have hp_between_right :
        nthPrime (n + 1) < 2201 + 30030 * d := by
      rw [← hk]
      exact nthPrime_strictMono hn1k
    exact shifted_interior_not_prime d (nthPrime (n + 1))
      hp_between_left hp_between_right (nthPrime_prime (n + 1))
  have hkeq : k = n + 1 := by omega
  subst k
  refine ⟨n, hn, hk, ?_⟩
  rw [exceptionalGap_iff]
  intro m hm₁ hm₂
  have hsmall : Nat.minFac m < 18 := by
    apply shifted_interior_minFac_lt d m
    · simpa [hn] using hm₁
    · simpa [hk] using hm₂
  have hgap : gapLength n = 18 := by
    dsimp [gapLength]
    rw [hn, hk]
    omega
  simpa [hgap] using hsmall

end Erdos682

#print axioms Erdos682.erdos_682
#print axioms Erdos682.exceptionalDyadicCount_isBigO_gapScale
#print axioms Erdos682.erdos_conditional_counterexample
