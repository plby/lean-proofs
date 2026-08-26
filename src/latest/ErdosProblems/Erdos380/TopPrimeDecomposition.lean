import ErdosProblems.Erdos380.PrimeRecords

/-! # Canonical removal of the largest prime factors, with multiplicity -/

open scoped BigOperators

namespace Erdos380

def primeRemainder (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 => primeRemainder n j / largestPrimeFactor (primeRemainder n j)

def topPrime (n j : ℕ) : ℕ := largestPrimeFactor (primeRemainder n j)

lemma largestPrimeFactor_dvd_of_pos {n : ℕ} (hn : 0 < n) : largestPrimeFactor n ∣ n := by
  by_cases h : n = 1
  · simp [h]
  · exact largestPrimeFactor_dvd (by omega)

lemma primeRemainder_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < primeRemainder n j := by
  induction j with
  | zero => exact hn
  | succ j ih =>
    exact Nat.div_pos (largestPrimeFactor_le_self (Nat.succ_le_iff.mpr ih))
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_largestPrimeFactor _))

lemma topPrime_mul_remainder {n : ℕ} (hn : 0 < n) (j : ℕ) :
    topPrime n j * primeRemainder n (j + 1) = primeRemainder n j :=
  Nat.mul_div_cancel' (largestPrimeFactor_dvd_of_pos (primeRemainder_pos hn j))

lemma primeRemainder_succ_dvd {n : ℕ} (hn : 0 < n) (j : ℕ) :
    primeRemainder n (j + 1) ∣ primeRemainder n j :=
  ⟨topPrime n j, by simpa only [mul_comm] using (topPrime_mul_remainder hn j).symm⟩

lemma primeRemainder_dvd_of_le {n j l : ℕ} (hn : 0 < n) (hjl : j ≤ l) :
    primeRemainder n l ∣ primeRemainder n j := by
  induction l, hjl using Nat.le_induction with
  | base => exact dvd_rfl
  | succ l _ ih => exact (primeRemainder_succ_dvd hn l).trans ih

lemma topPrime_antitone {n : ℕ} (hn : 0 < n) : Antitone (topPrime n) := by
  intro j l hjl
  exact largestPrimeFactor_mono_dvd (primeRemainder_pos hn j).ne'
    (primeRemainder_dvd_of_le hn hjl)

lemma topPrime_prime {n j : ℕ} (hn : 0 < n) (hj : 1 < topPrime n j) :
    (topPrime n j).Prime := by
  apply largestPrimeFactor_prime
  have hle := largestPrimeFactor_le_self (Nat.succ_le_iff.mpr (primeRemainder_pos hn j))
  change topPrime n j ≤ primeRemainder n j at hle
  omega

lemma topPrime_product_mul_remainder {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (∏ i : Fin k, topPrime n i.val) * primeRemainder n k = n := by
  induction k with
  | zero => simp [primeRemainder]
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mul_assoc, topPrime_mul_remainder hn k]
    exact ih

def canonicalPrimeRecord (n k : ℕ) : PrimeRecord k :=
  (largestPrimeFactor n, (fun i => topPrime (singletonCofactor n) i.val),
    primeRemainder (singletonCofactor n) k)

lemma SingletonBad.canonicalPrimeRecord_value {n : ℕ} (hn : SingletonBad n) (k : ℕ) :
    primeRecordValue (canonicalPrimeRecord n k) = n := by
  unfold primeRecordValue canonicalPrimeRecord
  rw [topPrime_product_mul_remainder hn.cofactor_pos k]
  exact hn.square_mul_cofactor

lemma SingletonBad.canonicalPrimeRecord_cofactor_pos {n : ℕ} (hn : SingletonBad n) (k : ℕ) :
    0 < (canonicalPrimeRecord n k).2.2 := primeRemainder_pos hn.cofactor_pos k

lemma SingletonBad.canonicalPrimeRecord_tuple_le {n : ℕ} (hn : SingletonBad n)
    {k : ℕ} (i : Fin k) : (canonicalPrimeRecord n k).2.1 i ≤ largestPrimeFactor n := by
  have hdiv : primeRemainder (singletonCofactor n) i.val ∣ n :=
    (primeRemainder_dvd_of_le hn.cofactor_pos (Nat.zero_le i.val)).trans hn.cofactor_dvd
  exact largestPrimeFactor_mono_dvd (by have := hn.1; omega) hdiv

lemma SingletonBad.canonicalPrimeRecord_cofactor_le {n : ℕ} (hn : SingletonBad n)
    {k : ℕ} (i : Fin k) :
    largestPrimeFactor (canonicalPrimeRecord n k).2.2 ≤ (canonicalPrimeRecord n k).2.1 i :=
  topPrime_antitone hn.cofactor_pos (Nat.le_of_lt i.isLt)

lemma SingletonBad.canonicalPrimeRecord_prime_tuple {n k : ℕ} (hn : SingletonBad n)
    (hk : 0 < k) (hlarge : 1 < topPrime (singletonCofactor n) (k - 1)) :
    ∀ i : Fin k, ((canonicalPrimeRecord n k).2.1 i).Prime := by
  intro i
  apply topPrime_prime hn.cofactor_pos
  exact hlarge.trans_le (topPrime_antitone hn.cofactor_pos (by have := i.isLt; omega))

lemma SingletonBad.canonicalPrimeRecord_tuple_ge {n k R : ℕ} (hn : SingletonBad n)
    (hlarge : R ≤ topPrime (singletonCofactor n) (k - 1)) :
    ∀ i : Fin k, R ≤ (canonicalPrimeRecord n k).2.1 i := by
  intro i
  exact hlarge.trans (topPrime_antitone hn.cofactor_pos (by have := i.isLt; omega))

end Erdos380
