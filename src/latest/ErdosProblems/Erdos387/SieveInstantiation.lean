/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BrunSieve
import ErdosProblems.Erdos387.LocalDensity
import ErdosProblems.Erdos387.Section6Counting

/-!
# Instantiating the lower sieve on the covered binomial progression

This file constructs the literal `BoundingSieve` whose support consists of
the binomial coefficients attached to the unsifted progression candidates.
Its local density at a sieving prime is `k / p`.
-/

namespace Erdos387

open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open Finset Nat ArithmeticFunction

/-- The finite progression before removing small prime divisors. -/
noncomputable def BaseCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (X / 2) X).filter fun n =>
    S.k < n ∧ (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α

theorem mem_BaseCandidates {B K X n : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} :
    n ∈ BaseCandidates S X ↔
      n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
        (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α := by
  classical
  simp [BaseCandidates]

/-- Canonical natural representative of the public integer progression. -/
noncomputable def progressionResidue {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) : ℕ :=
  (S.α % (CoverBPZ.Nk_formula S.k : ℤ)).toNat

theorem progressionResidue_lt {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    progressionResidue S < CoverBPZ.Nk_formula S.k := by
  have hMpos := CoverBPZ.Nk_formula_pos S.k
  have hnonneg : 0 ≤ S.α % (CoverBPZ.Nk_formula S.k : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hMpos.ne')
  have hlt : S.α % (CoverBPZ.Nk_formula S.k : ℤ) <
      (CoverBPZ.Nk_formula S.k : ℤ) :=
    Int.emod_lt_of_pos _ (by exact_mod_cast hMpos)
  unfold progressionResidue
  exact (Int.toNat_lt hnonneg).mpr hlt

/-- Convert the public integer divisibility presentation of the progression
to ordinary natural modular equality. -/
theorem progression_dvd_iff_modEq {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α ↔
      n ≡ progressionResidue S [MOD CoverBPZ.Nk_formula S.k] := by
  let M := CoverBPZ.Nk_formula S.k
  have hMpos : 0 < M := CoverBPZ.Nk_formula_pos S.k
  have hnonneg : 0 ≤ S.α % (M : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hMpos.ne')
  have hcast : ((progressionResidue S : ℕ) : ℤ) = S.α % (M : ℤ) := by
    unfold progressionResidue
    rw [Int.toNat_of_nonneg hnonneg]
  constructor
  · intro hdiv
    have haN : S.α ≡ (n : ℤ) [ZMOD (M : ℤ)] :=
      Int.modEq_iff_dvd.mpr hdiv
    have hnR : (n : ℤ) ≡ (progressionResidue S : ℤ) [ZMOD (M : ℤ)] := by
      rw [hcast]
      exact haN.symm.trans (Int.mod_modEq S.α (M : ℤ)).symm
    exact Int.natCast_modEq_iff.mp hnR
  · intro hnR
    have hnRz : (n : ℤ) ≡ (progressionResidue S : ℤ) [ZMOD (M : ℤ)] :=
      Int.natCast_modEq_iff.mpr hnR
    have hnA : (n : ℤ) ≡ S.α [ZMOD (M : ℤ)] := by
      rw [hcast] at hnRz
      exact hnRz.trans (Int.mod_modEq S.α (M : ℤ))
    exact Int.modEq_iff_dvd.mp hnA.symm

/-- The primes strictly between `k` and the roughness threshold `z`. -/
def sievePrimes (k z : ℕ) : Finset ℕ :=
  (Finset.range z).filter fun p => p.Prime ∧ k < p

theorem mem_sievePrimes {k z p : ℕ} :
    p ∈ sievePrimes k z ↔ p.Prime ∧ k < p ∧ p < z := by
  simp only [sievePrimes, Finset.mem_filter, Finset.mem_range]
  aesop

/-- Squarefree product of the sieving primes. -/
def sievePrimeProduct (k z : ℕ) : ℕ :=
  ∏ p ∈ sievePrimes k z, p

theorem sievePrimeProduct_squarefree (k z : ℕ) :
    Squarefree (sievePrimeProduct k z) := by
  unfold sievePrimeProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (coprime_primes (mem_sievePrimes.mp hp).1
      (mem_sievePrimes.mp hq).1).mpr hpq
  · intro p hp
    exact (mem_sievePrimes.mp hp).1.squarefree

theorem prime_mem_sievePrimes_of_dvd_product {k z p : ℕ}
    (hp : p.Prime) (hdiv : p ∣ sievePrimeProduct k z) :
    p ∈ sievePrimes k z := by
  unfold sievePrimeProduct at hdiv
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
  have hqPrime := (mem_sievePrimes.mp hq).1
  have hpEq : p = q := ((hqPrime.dvd_iff_eq hp.ne_one).mp hpq).symm
  simpa [hpEq] using hq

/-- Every prime divisor of the public progression modulus is at most `k`. -/
theorem prime_le_of_dvd_Nk_formula {k p : ℕ} (hp : p.Prime)
    (hdiv : p ∣ CoverBPZ.Nk_formula k) : p ≤ k := by
  unfold CoverBPZ.Nk_formula at hdiv
  obtain ⟨q, hq, hpqPow⟩ :=
    (hp.prime.dvd_finsetProd_iff
      (fun q => q ^ (Nat.log q k + 1))).mp hdiv
  have hqData := Finset.mem_filter.mp hq
  have hpq : p ∣ q := hp.dvd_of_dvd_pow hpqPow
  have hpEq : p = q :=
    (((hqData.2.dvd_iff_eq hp.ne_one).mp hpq).symm)
  rw [hpEq]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqData.1)

/-- The progression modulus is coprime to every divisor of the product of
sieving primes, since the former has prime factors at most `k` and the latter
has prime factors greater than `k`. -/
theorem coprime_Nk_formula_of_dvd_sievePrimeProduct
    {k z d : ℕ} (hd : d ∣ sievePrimeProduct k z) :
    Nat.Coprime (CoverBPZ.Nk_formula k) d := by
  by_contra hcop
  obtain ⟨p, hp, hpM, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hple : p ≤ k := prime_le_of_dvd_Nk_formula hp hpM
  have hpProd : p ∣ sievePrimeProduct k z := hpd.trans hd
  have hmem := prime_mem_sievePrimes_of_dvd_product hp hpProd
  exact (Nat.not_lt_of_ge hple) (mem_sievePrimes.mp hmem).2.1

theorem sievePrimeProduct_pos (k z : ℕ) :
    0 < sievePrimeProduct k z := by
  unfold sievePrimeProduct
  exact Finset.prod_pos fun p hp => (mem_sievePrimes.mp hp).1.pos

theorem pos_of_dvd_sievePrimeProduct {k z d : ℕ}
    (hd : d ∣ sievePrimeProduct k z) : 0 < d :=
  Nat.pos_of_dvd_of_pos hd (sievePrimeProduct_pos k z)

/-- CRT combination of the covered progression class modulo `N_k` with a
local forbidden class modulo a squarefree sieve divisor. -/
noncomputable def progressionLocalResidue {B K z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) (a : ℕ) : ℕ :=
  Nat.chineseRemainder (coprime_Nk_formula_of_dvd_sievePrimeProduct hd)
    (progressionResidue S) a

theorem progressionLocalResidue_mod_Nk {B K z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) (a : ℕ) :
    progressionLocalResidue S hd a ≡ progressionResidue S
      [MOD CoverBPZ.Nk_formula S.k] :=
  (Nat.chineseRemainder
    (coprime_Nk_formula_of_dvd_sievePrimeProduct hd)
    (progressionResidue S) a).prop.1

theorem progressionLocalResidue_mod_local {B K z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) (a : ℕ) :
    progressionLocalResidue S hd a ≡ a [MOD d] :=
  (Nat.chineseRemainder
    (coprime_Nk_formula_of_dvd_sievePrimeProduct hd)
    (progressionResidue S) a).prop.2

theorem progressionLocalResidue_lt {B K z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) (a : ℕ) :
    progressionLocalResidue S hd a < CoverBPZ.Nk_formula S.k * d := by
  exact Nat.chineseRemainder_lt_mul
    (coprime_Nk_formula_of_dvd_sievePrimeProduct hd)
    (progressionResidue S) a
    (CoverBPZ.Nk_formula_pos S.k).ne'
    (pos_of_dvd_sievePrimeProduct hd).ne'

/-- The simultaneous progression-and-binomial forbidden residue classes. -/
noncomputable def progressionLocalResidues {B K z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) : Finset ℕ := by
  classical
  exact (localAssignmentResidues d S.k).image
    (progressionLocalResidue S hd)

/-- CRT combination preserves the exact `k ^ ω(d)` local multiplicity. -/
theorem card_progressionLocalResidues {B K z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) (hsq : Squarefree d)
    (hlarge : ∀ p ∈ d.primeFactors, S.k < p) :
    (progressionLocalResidues S hd).card =
      S.k ^ d.primeFactors.card := by
  classical
  unfold progressionLocalResidues
  rw [(Finset.card_image_iff).mpr]
  · exact card_localAssignmentResidues hlarge
  · intro a ha b hb hab
    have habMod : a ≡ b [MOD d] :=
      (progressionLocalResidue_mod_local S hd a).symm.trans
        ((by simpa [hab] using
          progressionLocalResidue_mod_local S hd b))
    exact habMod.eq_of_lt_of_lt
      (by
        change a ∈ localAssignmentResidues d S.k at ha
        rw [localAssignmentResidues, Finset.mem_image] at ha
        obtain ⟨A, _, rfl⟩ := ha
        exact localAssignmentResidue_lt hsq A)
      (by
        change b ∈ localAssignmentResidues d S.k at hb
        rw [localAssignmentResidues, Finset.mem_image] at hb
        obtain ⟨A, _, rfl⟩ := hb
        exact localAssignmentResidue_lt hsq A)

theorem progressionLocalResidues_lt {B K z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) :
    ∀ a ∈ progressionLocalResidues S hd,
      a < CoverBPZ.Nk_formula S.k * d := by
  intro a ha
  rw [progressionLocalResidues, Finset.mem_image] at ha
  obtain ⟨b, _, rfl⟩ := ha
  exact progressionLocalResidue_lt S hd b

/-- Membership in a simultaneous CRT class is exactly the conjunction of
the covered progression congruence and membership in a local class modulo
`d`. -/
theorem mod_mem_progressionLocalResidues_iff {B K z d n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) (hsq : Squarefree d) :
    n % (CoverBPZ.Nk_formula S.k * d) ∈ progressionLocalResidues S hd ↔
      n ≡ progressionResidue S [MOD CoverBPZ.Nk_formula S.k] ∧
        n % d ∈ localAssignmentResidues d S.k := by
  classical
  constructor
  · intro hn
    rw [progressionLocalResidues, Finset.mem_image] at hn
    obtain ⟨a, ha, hna⟩ := hn
    have hnCombined : n ≡ progressionLocalResidue S hd a
        [MOD CoverBPZ.Nk_formula S.k * d] := by
      change n % (CoverBPZ.Nk_formula S.k * d) =
        progressionLocalResidue S hd a %
          (CoverBPZ.Nk_formula S.k * d)
      rw [Nat.mod_eq_of_lt (progressionLocalResidue_lt S hd a)]
      exact hna.symm
    refine ⟨(hnCombined.of_mul_right d).trans
      (progressionLocalResidue_mod_Nk S hd a), ?_⟩
    have hnd : n ≡ a [MOD d] :=
      (hnCombined.of_mul_left (CoverBPZ.Nk_formula S.k)).trans
        (progressionLocalResidue_mod_local S hd a)
    have haLt : a < d := by
      rw [localAssignmentResidues, Finset.mem_image] at ha
      obtain ⟨A, _, rfl⟩ := ha
      exact localAssignmentResidue_lt hsq A
    have hnmod : n % d = a := Nat.mod_eq_of_modEq hnd haLt
    simpa [hnmod] using ha
  · rintro ⟨hnM, hnd⟩
    rw [progressionLocalResidues, Finset.mem_image]
    refine ⟨n % d, hnd, ?_⟩
    have hnLocal : n ≡ n % d [MOD d] := (Nat.mod_modEq n d).symm
    have hnCombined : n ≡ progressionLocalResidue S hd (n % d)
        [MOD CoverBPZ.Nk_formula S.k * d] :=
      Nat.chineseRemainder_modEq_unique
        (coprime_Nk_formula_of_dvd_sievePrimeProduct hd) hnM hnLocal
    exact (Nat.mod_eq_of_modEq hnCombined
      (progressionLocalResidue_lt S hd (n % d))).symm

theorem primeFactor_large_of_dvd_sievePrimeProduct {k z d p : ℕ}
    (hd : d ∣ sievePrimeProduct k z) (hp : p ∈ d.primeFactors) :
    k < p := by
  have hpPrime := (Nat.mem_primeFactors.mp hp).1
  have hpProd : p ∣ sievePrimeProduct k z :=
    (Nat.dvd_of_mem_primeFactors hp).trans hd
  exact (mem_sievePrimes.mp
    (prime_mem_sievePrimes_of_dvd_product hpPrime hpProd)).2.1

/-- Base progression values for which the modulus divides the binomial
coefficient. -/
noncomputable def DivisibleBaseCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X d : ℕ) : Finset ℕ := by
  classical
  exact (BaseCandidates S X).filter fun n => d ∣ n.choose S.k

/-- In the range where `k < n` is automatic, the literal divisibility
subset of the covered progression is exactly a union of simultaneous CRT
classes modulo `N_k d`. -/
theorem divisibleBaseCandidates_eq_modularPreimageIoc {B K X z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hX : S.k ≤ X / 2)
    (hd : d ∣ sievePrimeProduct S.k z) :
    DivisibleBaseCandidates S X d =
      modularPreimageIoc (X / 2) X
        (CoverBPZ.Nk_formula S.k * d) (progressionLocalResidues S hd) := by
  classical
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sievePrimeProduct_squarefree S.k z)
  have hlarge : ∀ p ∈ d.primeFactors, S.k < p :=
    fun p hp => primeFactor_large_of_dvd_sievePrimeProduct hd hp
  ext n
  simp only [DivisibleBaseCandidates, BaseCandidates, modularPreimageIoc,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hnIoc, hkn, hprog⟩, hdChoose⟩
    refine ⟨hnIoc, (mod_mem_progressionLocalResidues_iff S hd hsq).mpr
      ⟨(progression_dvd_iff_modEq S).mp hprog, ?_⟩⟩
    exact (squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge hkn.le).mp hdChoose
  · rintro ⟨hnIoc, hnMod⟩
    have hkn : S.k < n := lt_of_le_of_lt hX hnIoc.1
    have hnData := (mod_mem_progressionLocalResidues_iff S hd hsq).mp hnMod
    refine ⟨⟨hnIoc, hkn, (progression_dvd_iff_modEq S).mpr hnData.1⟩, ?_⟩
    exact (squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge hkn.le).mpr hnData.2

/-- Exact local-density discrepancy on the covered progression.  A
squarefree sieve divisor `d` selects `k ^ ω(d)` classes modulo `N_k d`, and
the two interval endpoints contribute at most twice that many points. -/
theorem abs_card_divisibleBaseCandidates_sub_density
    {B K X z d : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hd : d ∣ sievePrimeProduct S.k z) :
    |((DivisibleBaseCandidates S X d).card : ℝ) -
        (S.k : ℝ) ^ d.primeFactors.card * ((X - X / 2 : ℕ) : ℝ) /
          (CoverBPZ.Nk_formula S.k * d : ℕ)| ≤
      2 * (S.k : ℝ) ^ d.primeFactors.card := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sievePrimeProduct_squarefree S.k z)
  have hlarge : ∀ p ∈ d.primeFactors, S.k < p :=
    fun p hp => primeFactor_large_of_dvd_sievePrimeProduct hd hp
  have hmodPos : 0 < CoverBPZ.Nk_formula S.k * d :=
    Nat.mul_pos (CoverBPZ.Nk_formula_pos S.k)
      (pos_of_dvd_sievePrimeProduct hd)
  have h := abs_card_modularPreimageIoc_sub_density
    (L := X / 2) (U := X) (g := CoverBPZ.Nk_formula S.k * d)
    (Nat.div_le_self X 2) hmodPos (progressionLocalResidues S hd)
    (progressionLocalResidues_lt S hd)
  rw [← divisibleBaseCandidates_eq_modularPreimageIoc S hX hd,
    card_progressionLocalResidues S hd hsq hlarge] at h
  push_cast at h
  simpa only [Nat.cast_mul] using h

theorem divisibleBaseCandidates_one {B K X : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    DivisibleBaseCandidates S X 1 = BaseCandidates S X := by
  classical
  ext n
  simp [DivisibleBaseCandidates]

/-- The unsifted progression itself has the expected interval length divided
by `N_k`, with endpoint error at most two. -/
theorem abs_card_BaseCandidates_sub_density {B K X : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hX : S.k ≤ X / 2) :
    |((BaseCandidates S X).card : ℝ) -
        ((X - X / 2 : ℕ) : ℝ) / CoverBPZ.Nk_formula S.k| ≤ 2 := by
  have h := abs_card_divisibleBaseCandidates_sub_density
    (z := 0) (d := 1) S hX (one_dvd _)
  rw [divisibleBaseCandidates_one] at h
  simpa using h

/-- Multiplicative local density.  On a squarefree modulus it is
`k ^ ω(d) / d`. -/
noncomputable def binomialSieveNu (k : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p => (k : ℝ) / p

theorem binomialSieveNu_prime {k p : ℕ} (hp : p.Prime) :
    binomialSieveNu k p = (k : ℝ) / p := by
  rw [binomialSieveNu, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  simp [hp]

theorem binomialSieveNu_mult (k : ℕ) :
    (binomialSieveNu k).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

/-- Closed form of the local density on squarefree moduli. -/
theorem binomialSieveNu_squarefree {k d : ℕ} (hd : Squarefree d) :
    binomialSieveNu k d = (k : ℝ) ^ d.primeFactors.card / d := by
  rw [binomialSieveNu,
    ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Finset.prod_div_distrib, Finset.prod_const]
  congr 1
  rw [← Nat.cast_prod]
  norm_cast
  exact Nat.prod_primeFactors_of_squarefree hd

/-- Uniform remainder bound for every divisor of the sieve-prime product.
The exact CRT count gives an endpoint error `2 k^ω(d)`; comparing against
the literal size of the base progression costs at most another
`2 k^ω(d)`. -/
theorem abs_card_DivisibleBaseCandidates_sub_nu_mul_base_le
    {B K X z d : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hd : d ∣ sievePrimeProduct S.k z) :
    |((DivisibleBaseCandidates S X d).card : ℝ) -
        binomialSieveNu S.k d * (BaseCandidates S X).card| ≤
      4 * (S.k : ℝ) ^ d.primeFactors.card := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sievePrimeProduct_squarefree S.k z)
  rw [binomialSieveNu_squarefree hsq]
  let R : ℝ := (S.k : ℝ) ^ d.primeFactors.card
  let H : ℝ := ((X - X / 2 : ℕ) : ℝ)
  let M : ℝ := CoverBPZ.Nk_formula S.k
  let D : ℝ := (DivisibleBaseCandidates S X d).card
  let A : ℝ := (BaseCandidates S X).card
  let q : ℝ := R / d
  have hD : |D - R * H / (M * d)| ≤ 2 * R := by
    simpa [R, H, M, D, Nat.cast_mul] using
      abs_card_divisibleBaseCandidates_sub_density S hX hd
  have hA : |A - H / M| ≤ 2 := by
    simpa [A, H, M] using abs_card_BaseCandidates_sub_density S hX
  have hdPosNat : 0 < d := pos_of_dvd_sievePrimeProduct hd
  have hdPos : (0 : ℝ) < d := by exact_mod_cast hdPosNat
  have hMPos : (0 : ℝ) < M := by
    dsimp [M]
    exact_mod_cast CoverBPZ.Nk_formula_pos S.k
  have hR : 0 ≤ R := by positivity
  have hq : 0 ≤ q := by positivity
  have hqLe : q ≤ R := by
    apply (div_le_iff₀ hdPos).2
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPosNat
    nlinarith
  have hmain : R * H / (M * d) = q * (H / M) := by
    dsimp [q]
    field_simp
  have hdecomp :
      D - q * A = (D - R * H / (M * d)) - q * (A - H / M) := by
    rw [hmain]
    ring
  change |D - q * A| ≤ 4 * R
  rw [hdecomp]
  calc
    |(D - R * H / (M * d)) - q * (A - H / M)| ≤
        |D - R * H / (M * d)| + |q * (A - H / M)| := abs_sub _ _
    _ = |D - R * H / (M * d)| + q * |A - H / M| := by
      rw [abs_mul, abs_of_nonneg hq]
    _ ≤ 2 * R + q * 2 := add_le_add hD (mul_le_mul_of_nonneg_left hA hq)
    _ ≤ 4 * R := by linarith

/-- The abstract sieve attached to the covered progression.  Support values
are binomial coefficients rather than their indices, so coprimality with the
sieving-prime product is exactly roughness. -/
noncomputable def binomialBoundingSieve {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z : ℕ) : BoundingSieve := by
  classical
  let A := BaseCandidates S X
  exact
    { support := A.image fun n => n.choose S.k
      prodPrimes := sievePrimeProduct S.k z
      prodPrimes_squarefree := sievePrimeProduct_squarefree S.k z
      weights := fun m =>
        ((A.filter fun n => n.choose S.k = m).card : ℝ)
      weights_nonneg := fun _ => by positivity
      totalMass := A.card
      nu := binomialSieveNu S.k
      nu_mult := binomialSieveNu_mult S.k
      nu_pos_of_prime := by
        intro p hp hdiv
        rw [binomialSieveNu_prime hp]
        have hmem := prime_mem_sievePrimes_of_dvd_product hp hdiv
        have hkPos : 0 < S.k := by have := S.hk3; omega
        exact div_pos (by exact_mod_cast hkPos) (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp hdiv
        rw [binomialSieveNu_prime hp]
        have hmem := prime_mem_sievePrimes_of_dvd_product hp hdiv
        have hkp : S.k < p := (mem_sievePrimes.mp hmem).2.1
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hkp) }

/-- On the certified progression, coprimality with the product of primes in
`(k,z)` is exactly `z`-roughness: the covering certificate already excludes
all primes at most `k`. -/
theorem coprime_sievePrimeProduct_iff_rough {B K n z : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α) :
    Nat.Coprime (sievePrimeProduct S.k z) (n.choose S.k) ↔
      IsZRough z (n.choose S.k) := by
  constructor
  · intro hcop p hp hpz hpChoose
    by_cases hpk : p ≤ S.k
    · exact S.no_prime_le_k_dvd_choose hn hprog hp hpk hpChoose
    · have hmem : p ∈ sievePrimes S.k z :=
        mem_sievePrimes.mpr ⟨hp, Nat.lt_of_not_ge hpk, hpz⟩
      have hpProd : p ∣ sievePrimeProduct S.k z := by
        unfold sievePrimeProduct
        exact Finset.dvd_prod_of_mem id hmem
      have hpcop : Nat.Coprime p (n.choose S.k) :=
        Nat.Coprime.of_dvd_left hpProd hcop
      exact (hp.coprime_iff_not_dvd.mp hpcop) hpChoose
  · intro hrough
    by_contra hcop
    obtain ⟨p, hp, hpProd, hpChoose⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hmem := prime_mem_sievePrimes_of_dvd_product hp hpProd
    exact hrough p hp (mem_sievePrimes.mp hmem).2.2 hpChoose

/-- The base progression filtered by the roughness predicate. -/
noncomputable def RoughBaseCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z : ℕ) : Finset ℕ := by
  classical
  exact (BaseCandidates S X).filter fun n =>
    IsZRough z (n.choose S.k)

theorem siftedCandidates_eq_filter_base {B K X z : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    SiftedCandidates S X z = RoughBaseCandidates S X z := by
  classical
  ext n
  simp [SiftedCandidates, RoughBaseCandidates, BaseCandidates, and_assoc]

/-- The abstract sieve's weighted sifted sum is literally the cardinality of
`SiftedCandidates`; fiber weights make this true without needing a separate
injectivity proof for `n ↦ n.choose k`. -/
theorem binomialBoundingSieve_siftedSum {B K X z : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    (binomialBoundingSieve S X z).siftedSum =
      ((SiftedCandidates S X z).card : ℝ) := by
  classical
  let A := BaseCandidates S X
  let f : ℕ → ℕ := fun n => n.choose S.k
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    A (A.image f) f
  have hcopFilter :
      ((A.image f).filter fun m => Nat.Coprime
        (sievePrimeProduct S.k z) m) =
        (A.image f).filter fun m => Nat.Coprime
          (sievePrimeProduct S.k z) m := rfl
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ A.image f,
      if Nat.Coprime (sievePrimeProduct S.k z) m then
        ((A.filter fun n => f n = m).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcard :
      (∑ m ∈ (A.image f).filter fun m =>
          Nat.Coprime (sievePrimeProduct S.k z) m,
          (A.filter fun n => f n = m).card) =
        (A.filter fun n =>
          Nat.Coprime (sievePrimeProduct S.k z) (f n)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcard]
  norm_cast
  rw [siftedCandidates_eq_filter_base]
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, RoughBaseCandidates]
  constructor
  · rintro ⟨hnA, hcop⟩
    have hnData := (mem_BaseCandidates (S := S)).mp hnA
    exact ⟨hnA, (coprime_sievePrimeProduct_iff_rough S
      hnData.2.1 hnData.2.2).mp hcop⟩
  · rintro ⟨hnA, hrough⟩
    have hnData := (mem_BaseCandidates (S := S)).mp hnA
    exact ⟨hnA, (coprime_sievePrimeProduct_iff_rough S
      hnData.2.1 hnData.2.2).mpr hrough⟩

/-- The multiple sum in the abstract sieve is the literal cardinality of the
corresponding divisibility subset of the base progression. -/
theorem binomialBoundingSieve_multSum {B K X z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    (binomialBoundingSieve S X z).multSum d =
      ((DivisibleBaseCandidates S X d).card : ℝ) := by
  classical
  let A := BaseCandidates S X
  let f : ℕ → ℕ := fun n => n.choose S.k
  rw [BoundingSieve.multSum]
  change (∑ m ∈ A.image f,
      if d ∣ m then ((A.filter fun n => f n = m).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcard :
      (∑ m ∈ (A.image f).filter fun m => d ∣ m,
          (A.filter fun n => f n = m).card) =
        (A.filter fun n => d ∣ f n).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcard]
  norm_cast

/-- The abstract sieve remainder inherits the explicit CRT endpoint bound. -/
theorem binomialBoundingSieve_abs_rem_le {B K X z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hX : S.k ≤ X / 2)
    (hd : d ∣ sievePrimeProduct S.k z) :
    |(binomialBoundingSieve S X z).rem d| ≤
      4 * (S.k : ℝ) ^ d.primeFactors.card := by
  rw [BoundingSieve.rem, binomialBoundingSieve_multSum]
  change |((DivisibleBaseCandidates S X d).card : ℝ) -
      binomialSieveNu S.k d * (BaseCandidates S X).card| ≤ _
  exact abs_card_DivisibleBaseCandidates_sub_nu_mul_base_le S hX hd

/-- The ready-to-use finite lower bound for the exact `SiftedCandidates`
cardinality. -/
theorem siftedCandidates_brunLowerBound {B K X z L : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hL : Odd L) :
    (binomialBoundingSieve S X z).totalMass *
          (binomialBoundingSieve S X z).mainSum (brunLowerWeight L) -
        (binomialBoundingSieve S X z).errSum (brunLowerWeight L) ≤
      ((SiftedCandidates S X z).card : ℝ) := by
  rw [← binomialBoundingSieve_siftedSum S]
  exact brunLowerBound (binomialBoundingSieve S X z) hL

/-- The matching finite upper Brun bound.  This is used after imposing a
candidate large-divisor tuple; the local sieve remains the same because that
tuple is coprime to the small-prime product. -/
theorem siftedCandidates_brunUpperBound {B K X z L : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hL : Even L) :
    ((SiftedCandidates S X z).card : ℝ) ≤
      (binomialBoundingSieve S X z).totalMass *
          (binomialBoundingSieve S X z).mainSum (brunUpperWeight L) +
        (binomialBoundingSieve S X z).errSum (brunUpperWeight L) := by
  rw [← binomialBoundingSieve_siftedSum S]
  exact brunUpperBound (binomialBoundingSieve S X z) hL

end Erdos387
