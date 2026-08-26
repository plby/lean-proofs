import ErdosProblems.Erdos380.PrimeBoxCounting
import ErdosProblems.Erdos380.TopPrimeDecomposition
import Mathlib.Data.Nat.Log

/-! # Assigning singleton-bad integers to the original prime boxes -/

open scoped BigOperators

namespace Erdos380

abbrev PrimeBoxSample {k : ℕ} (b : PrimeBox k) :=
  dyadicPrimes (2 ^ b.1) × (∀ i, dyadicPrimes (2 ^ (b.2.1 i)))

def primeBoxSampleRecord {k : ℕ} (b : PrimeBox k) (s : PrimeBoxSample b) : PrimeRecord k :=
  (s.1.val, (fun i => (s.2 i).val), b.2.2)

lemma primeBoxSampleRecord_injective {k : ℕ} (b : PrimeBox k) :
    Function.Injective (primeBoxSampleRecord b) := by
  intro s t h
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun r : PrimeRecord k => r.1) h)
  · funext i
    exact Subtype.ext (congrArg (fun r : PrimeRecord k => r.2.1 i) h)

noncomputable def primeBoxRecords {k : ℕ} (b : PrimeBox k) : Finset (PrimeRecord k) :=
  Finset.univ.image (primeBoxSampleRecord b)

lemma mem_primeBoxRecords {k : ℕ} {b : PrimeBox k} {r : PrimeRecord k} :
    r ∈ primeBoxRecords b ↔ r.1 ∈ dyadicPrimes (2 ^ b.1) ∧
      (∀ i, r.2.1 i ∈ dyadicPrimes (2 ^ (b.2.1 i))) ∧ r.2.2 = b.2.2 := by
  classical
  constructor
  · intro hr
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨s.1.property, (fun i => (s.2 i).property), rfl⟩
  · rintro ⟨hp, hf, hb⟩
    apply Finset.mem_image.mpr
    refine ⟨(⟨r.1, hp⟩, fun i => ⟨r.2.1 i, hf i⟩), Finset.mem_univ _, ?_⟩
    exact Prod.ext rfl (Prod.ext rfl hb.symm)

lemma primeBoxRecords_card {k : ℕ} (b : PrimeBox k) :
    (primeBoxRecords b).card = primeBoxMass b := by
  classical
  rw [primeBoxRecords, Finset.card_image_of_injective _ (primeBoxSampleRecord_injective b)]
  simp [PrimeBoxSample, primeBoxMass, Fintype.card_pi]

def dyadicPrimeIndex (p : ℕ) : ℕ := Nat.log 2 (p - 1)

lemma dyadicPrimeIndex_bounds {p : ℕ} (hp : 2 ≤ p) :
    2 ^ dyadicPrimeIndex p < p ∧ p ≤ 2 ^ (dyadicPrimeIndex p + 1) := by
  have hlow := Nat.pow_log_le_self 2 (show p - 1 ≠ 0 by omega)
  have hhigh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (p - 1)
  change 2 ^ dyadicPrimeIndex p ≤ p - 1 at hlow
  change p - 1 < 2 ^ (dyadicPrimeIndex p + 1) at hhigh
  omega

lemma mem_dyadicPrimeIndex_pool {p : ℕ} (hp : p.Prime) :
    p ∈ dyadicPrimes (2 ^ dyadicPrimeIndex p) := by
  obtain ⟨hlow, hhigh⟩ := dyadicPrimeIndex_bounds hp.two_le
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Ioc.mpr ⟨hlow, by simpa only [pow_succ'] using hhigh⟩, hp⟩

lemma dyadicPrimeIndex_monotone : Monotone dyadicPrimeIndex := by
  intro p q hpq
  exact Nat.log_mono_right (Nat.sub_le_sub_right hpq 1)

def canonicalPrimeBox (n k : ℕ) : PrimeBox k :=
  (dyadicPrimeIndex (largestPrimeFactor n),
    (fun i => dyadicPrimeIndex (topPrime (singletonCofactor n) i.val)),
    primeRemainder (singletonCofactor n) k)

lemma SingletonBad.canonicalPrimeRecord_mem_box {n k : ℕ} (hn : SingletonBad n)
    (hk : 0 < k) (hlarge : 1 < topPrime (singletonCofactor n) (k - 1)) :
    canonicalPrimeRecord n k ∈ primeBoxRecords (canonicalPrimeBox n k) := by
  apply mem_primeBoxRecords.mpr
  exact ⟨mem_dyadicPrimeIndex_pool (largestPrimeFactor_prime (by have := hn.1; omega)),
    (fun i => mem_dyadicPrimeIndex_pool (hn.canonicalPrimeRecord_prime_tuple hk hlarge i)), rfl⟩

lemma SingletonBad.canonicalPrimeBox_valid {n k : ℕ} (hn : SingletonBad n)
    (hk : 0 < k) (hlarge : 1 < topPrime (singletonCofactor n) (k - 1)) :
    ValidPrimeBox (canonicalPrimeBox n k) := by
  have hp := largestPrimeFactor_prime (by have := hn.1; omega : 1 < n)
  have hq := hn.canonicalPrimeRecord_prime_tuple hk hlarge
  refine ⟨hn.canonicalPrimeRecord_cofactor_pos k, ?_, ?_, ?_⟩
  · intro i
    exact dyadicPrimeIndex_monotone (hn.canonicalPrimeRecord_tuple_le i)
  · let i : Fin k := ⟨0, hk⟩
    have hb := (hn.canonicalPrimeRecord_cofactor_le i).trans (hn.canonicalPrimeRecord_tuple_le i)
    exact hb.trans ((dyadicPrimeIndex_bounds hp.two_le).2.trans
      (Nat.pow_le_pow_right (by norm_num) (by dsimp [canonicalPrimeBox]; omega)))
  · intro i
    exact (hn.canonicalPrimeRecord_cofactor_le i).trans (dyadicPrimeIndex_bounds (hq i).two_le).2

lemma SingletonBad.canonicalPrimeBox_base_le {n k : ℕ} (hn : SingletonBad n)
    (hk : 0 < k) (hlarge : 1 < topPrime (singletonCofactor n) (k - 1)) :
    primeBoxBaseValue (canonicalPrimeBox n k) ≤ n := by
  have hp := largestPrimeFactor_prime (by have := hn.1; omega : 1 < n)
  have hq := hn.canonicalPrimeRecord_prime_tuple hk hlarge
  calc
    primeBoxBaseValue (canonicalPrimeBox n k) ≤ primeRecordValue (canonicalPrimeRecord n k) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (dyadicPrimeIndex_bounds hp.two_le).1.le 2)
        (Nat.mul_le_mul_right _ (Finset.prod_le_prod' fun i _ =>
          (dyadicPrimeIndex_bounds (hq i).two_le).1.le))
    _ = n := hn.canonicalPrimeRecord_value k

lemma SingletonBad.canonicalPrimeBox_tuple_upper_ge {n k R : ℕ} (hn : SingletonBad n)
    (hk : 0 < k) (hprime : 1 < topPrime (singletonCofactor n) (k - 1))
    (hlarge : R ≤ topPrime (singletonCofactor n) (k - 1)) :
    ∀ i : Fin k, R ≤ 2 ^ ((canonicalPrimeBox n k).2.1 i + 1) := by
  intro i
  exact (hn.canonicalPrimeRecord_tuple_ge hlarge i).trans
    (dyadicPrimeIndex_bounds (hn.canonicalPrimeRecord_prime_tuple hk hprime i).two_le).2

end Erdos380
