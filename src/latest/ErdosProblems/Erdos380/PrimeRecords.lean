import ErdosProblems.Erdos380.TopPrimeProducts
import ErdosProblems.Erdos380.SingletonCompression

/-! # Counting a largest-prime square, a prime tuple, and a smaller cofactor -/

open scoped BigOperators

namespace Erdos380

abbrev PrimeRecord (k : ℕ) := ℕ × (Fin k → ℕ) × ℕ

def primeRecordValue {k : ℕ} (r : PrimeRecord k) : ℕ :=
  r.1 ^ 2 * ((∏ i, r.2.1 i) * r.2.2)

def ValidPrimeRecord {k : ℕ} (r : PrimeRecord k) : Prop :=
  r.1.Prime ∧ (∀ i, (r.2.1 i).Prime) ∧ 0 < r.2.2 ∧
    (∀ i, r.2.1 i ≤ r.1) ∧ largestPrimeFactor r.2.2 ≤ r.1 ∧
      ∀ i, largestPrimeFactor r.2.2 < r.2.1 i

lemma ValidPrimeRecord.largest {k : ℕ} {r : PrimeRecord k} (hr : ValidPrimeRecord r) :
    largestPrimeFactor (primeRecordValue r) = r.1 := by
  obtain ⟨hp, hf, hb, hfp, hbp, _⟩ := hr
  have hf0 : (∏ i, r.2.1 i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hf i).ne_zero
  have hfl : largestPrimeFactor (∏ i, r.2.1 i) ≤ r.1 := by
    apply largestPrimeFactor_le hp.one_le
    intro q hq hqd
    obtain ⟨i, _, hqi⟩ := (hq.prime.dvd_finsetProd_iff (fun i : Fin k => r.2.1 i)).mp hqd
    have heq : q = r.2.1 i := (Nat.prime_dvd_prime_iff_eq hq (hf i)).mp hqi
    simpa only [heq] using hfp i
  rw [primeRecordValue, largestPrimeFactor_mul (pow_ne_zero 2 hp.ne_zero) (mul_ne_zero hf0 hb.ne'),
    largestPrimeFactor_pow r.1 (by decide), largestPrimeFactor_of_prime hp,
    largestPrimeFactor_mul hf0 hb.ne', max_eq_left (max_le hfl hbp)]

lemma ValidPrimeRecord.singletonBad {k : ℕ} {r : PrimeRecord k} (hr : ValidPrimeRecord r) :
    SingletonBad (primeRecordValue r) := by
  have hp := hr.1
  have hfpos : 0 < ∏ i, r.2.1 i := Finset.prod_pos fun i _ => (hr.2.1 i).pos
  have hpos : 0 < primeRecordValue r :=
    mul_pos (pow_pos hp.pos 2) (mul_pos hfpos hr.2.2.1)
  have hle := largestPrimeFactor_le_self (Nat.succ_le_iff.mpr hpos)
  rw [hr.largest] at hle
  exact ⟨hp.two_le.trans hle, by rw [hr.largest]; exact dvd_mul_right _ _⟩

theorem validPrimeRecord_fiber_unique {k : ℕ} {r s : PrimeRecord k}
    (hr : ValidPrimeRecord r) (hs : ValidPrimeRecord s)
    (heq : primeRecordValue r = primeRecordValue s) :
    r.1 = s.1 ∧ r.2.2 = s.2.2 ∧ (List.ofFn r.2.1).Perm (List.ofFn s.2.1) := by
  have hp : r.1 = s.1 := by rw [← hr.largest, ← hs.largest, heq]
  have hprod : (∏ i, r.2.1 i) * r.2.2 = (∏ i, s.2.1 i) * s.2.2 := by
    unfold primeRecordValue at heq
    rw [hp] at heq
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hs.1.pos 2) heq
  obtain ⟨hb, hf⟩ := top_prime_product_cofactor_unique hr.2.2.1 hs.2.2.1 hr.2.1 hs.2.1
    hr.2.2.2.2.2 hs.2.2.2.2.2 hprod
  exact ⟨hp, hb, hf⟩

lemma validPrimeRecords_fiber_card_le {k : ℕ} (S : Finset (PrimeRecord k))
    (hvalid : ∀ r ∈ S, ValidPrimeRecord r) (n : ℕ) :
    (S.filter fun r => primeRecordValue r = n).card ≤ k.factorial := by
  classical
  let F := S.filter fun r => primeRecordValue r = n
  rcases F.eq_empty_or_nonempty with hF | ⟨s, hs⟩
  · change F.card ≤ k.factorial
    rw [hF]
    exact Nat.zero_le _
  have hsS := (Finset.mem_filter.mp hs).1
  have hsval := (Finset.mem_filter.mp hs).2
  calc
    F.card ≤ (List.ofFn s.2.1).permutations.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun r : PrimeRecord k => List.ofFn r.2.1)
      · intro r hr
        have heq := (Finset.mem_filter.mp hr).2.trans hsval.symm
        exact List.mem_toFinset.mpr (List.mem_permutations.mpr
          (validPrimeRecord_fiber_unique (hvalid r (Finset.mem_filter.mp hr).1) (hvalid s hsS) heq).2.2)
      · intro r hr t ht hlist
        have heq := (Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp ht).2.symm
        obtain ⟨hp, hb, _⟩ := validPrimeRecord_fiber_unique
          (hvalid r (Finset.mem_filter.mp hr).1) (hvalid t (Finset.mem_filter.mp ht).1) heq
        exact Prod.ext hp (Prod.ext (List.ofFn_injective hlist) hb)
    _ ≤ (List.ofFn s.2.1).permutations.length := List.toFinset_card_le _
    _ = k.factorial := by simp [List.length_permutations]

theorem validPrimeRecords_card_le_singletons {k N : ℕ} (S : Finset (PrimeRecord k))
    (hvalid : ∀ r ∈ S, ValidPrimeRecord r) (hsize : ∀ r ∈ S, primeRecordValue r ≤ N) :
    S.card ≤ k.factorial * (singletonBadUpTo N).card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to (f := primeRecordValue)
    (s := S) (t := singletonBadUpTo N) ?_ k.factorial ?_
  · intro r hr
    have hbad := (hvalid r hr).singletonBad
    exact mem_singletonBadUpTo.mpr ⟨by have := hbad.1; omega, hsize r hr, hbad⟩
  · intro n _
    exact validPrimeRecords_fiber_card_le S hvalid n

lemma ValidPrimeRecord.cofactor {k : ℕ} {r : PrimeRecord k} (hr : ValidPrimeRecord r) :
    singletonCofactor (primeRecordValue r) = (∏ i, r.2.1 i) * r.2.2 := by
  have h := hr.singletonBad.square_mul_cofactor
  rw [hr.largest] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hr.1.pos 2) h

lemma ValidPrimeRecord.le_cofactor_largest {k : ℕ} {r : PrimeRecord k}
    (hr : ValidPrimeRecord r) (i : Fin k) :
    r.2.1 i ≤ largestPrimeFactor (singletonCofactor (primeRecordValue r)) := by
  rw [hr.cofactor]
  apply prime_le_largestPrimeFactor
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => (hr.2.1 j).ne_zero) hr.2.2.1.ne')
    (hr.2.1 i)
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _

theorem validPrimeRecords_card_le_largeCofactorSingletons {k N R : ℕ}
    (S : Finset (PrimeRecord k)) (hvalid : ∀ r ∈ S, ValidPrimeRecord r)
    (hsize : ∀ r ∈ S, primeRecordValue r ≤ N)
    (hlarge : ∀ r ∈ S, R ≤ largestPrimeFactor (singletonCofactor (primeRecordValue r))) :
    S.card ≤ k.factorial * (largeCofactorSingletons N R).card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to (f := primeRecordValue)
    (s := S) (t := largeCofactorSingletons N R) ?_ k.factorial ?_
  · intro r hr
    have hbad := (hvalid r hr).singletonBad
    exact Finset.mem_filter.mpr ⟨mem_singletonBadUpTo.mpr
      ⟨by have := hbad.1; omega, hsize r hr, hbad⟩, hlarge r hr⟩
  · intro n _
    exact validPrimeRecords_fiber_card_le S hvalid n

end Erdos380
