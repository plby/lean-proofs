import ErdosProblems.Erdos380.PrimeRecords
import ErdosProblems.Erdos380.PrimeCounts

/-!
# Disjoint shifted prime boxes

The largest-prime pool is shifted up by a factor four, and every tuple
pool by a factor two. The resulting primes lie above the cofactor's prime
factors. Each output prime remembers its dyadic box.
-/

open scoped BigOperators

namespace Erdos380

abbrev PrimeBox (k : ℕ) := ℕ × (Fin k → ℕ) × ℕ

def primeBoxBaseValue {k : ℕ} (b : PrimeBox k) : ℕ :=
  (2 ^ b.1) ^ 2 * ((∏ i, 2 ^ (b.2.1 i)) * b.2.2)

def ValidPrimeBox {k : ℕ} (b : PrimeBox k) : Prop :=
  0 < b.2.2 ∧ (∀ i, b.2.1 i ≤ b.1) ∧
    largestPrimeFactor b.2.2 ≤ 2 ^ (b.1 + 2) ∧
      ∀ i, largestPrimeFactor b.2.2 ≤ 2 ^ (b.2.1 i + 1)

noncomputable def shiftedPrimeBoxRecords {k : ℕ} (b : PrimeBox k) : Finset (PrimeRecord k) := by
  classical
  exact ((dyadicPrimes (2 ^ (b.1 + 2))).product
    (Fintype.piFinset fun i : Fin k => dyadicPrimes (2 ^ (b.2.1 i + 1)))).image
      fun pf => (pf.1, pf.2, b.2.2)

lemma mem_shiftedPrimeBoxRecords {k : ℕ} {b : PrimeBox k} {r : PrimeRecord k} :
    r ∈ shiftedPrimeBoxRecords b ↔
      r.1 ∈ dyadicPrimes (2 ^ (b.1 + 2)) ∧
      (∀ i, r.2.1 i ∈ dyadicPrimes (2 ^ (b.2.1 i + 1))) ∧ r.2.2 = b.2.2 := by
  classical
  rcases r with ⟨p, f, c⟩
  simp [shiftedPrimeBoxRecords, Fintype.mem_piFinset, and_assoc, eq_comm]

lemma shiftedPrimeBoxRecords_card {k : ℕ} (b : PrimeBox k) :
    (shiftedPrimeBoxRecords b).card = (dyadicPrimes (2 ^ (b.1 + 2))).card *
      ∏ i, (dyadicPrimes (2 ^ (b.2.1 i + 1))).card := by
  classical
  unfold shiftedPrimeBoxRecords
  rw [Finset.card_image_of_injective]
  · simp
  · intro pf qg h
    dsimp only at h
    exact Prod.ext (congrArg (fun r : PrimeRecord k => r.1) h)
      (congrArg (fun r : PrimeRecord k => r.2.1) h)

lemma dyadic_power_index_unique {a b p : ℕ}
    (ha : p ∈ dyadicPrimes (2 ^ a)) (hb : p ∈ dyadicPrimes (2 ^ b)) : a = b := by
  obtain ⟨hpa, hap⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1
  obtain ⟨hpb, hbp⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
  have hle : ∀ a b : ℕ, a < b → 2 * 2 ^ a ≤ 2 ^ b := by
    intro a b hab
    calc
      2 * 2 ^ a = 2 ^ (a + 1) := (pow_succ' 2 a).symm
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases lt_trichotomy a b with h | h | h
  · have := hle a b h
    omega
  · exact h
  · have := hle b a h
    omega

lemma shiftedPrimeBoxRecords_box_unique {k : ℕ} {a b : PrimeBox k} {r : PrimeRecord k}
    (ha : r ∈ shiftedPrimeBoxRecords a) (hb : r ∈ shiftedPrimeBoxRecords b) : a = b := by
  obtain ⟨ha0, hai, hac⟩ := mem_shiftedPrimeBoxRecords.mp ha
  obtain ⟨hb0, hbi, hbc⟩ := mem_shiftedPrimeBoxRecords.mp hb
  have h0 : a.1 = b.1 := by have := dyadic_power_index_unique ha0 hb0; omega
  have hi : a.2.1 = b.2.1 := by
    funext i
    have := dyadic_power_index_unique (hai i) (hbi i)
    omega
  exact Prod.ext h0 (Prod.ext hi (hac.symm.trans hbc))

lemma shiftedPrimeBoxRecords_pairwiseDisjoint {k : ℕ} (B : Finset (PrimeBox k)) :
    (B : Set (PrimeBox k)).PairwiseDisjoint shiftedPrimeBoxRecords := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro r hra hrb
  exact hab (shiftedPrimeBoxRecords_box_unique hra hrb)

lemma shiftedPrimeBoxRecords_valid {k : ℕ} {b : PrimeBox k} {r : PrimeRecord k}
    (hb : ValidPrimeBox b) (hr : r ∈ shiftedPrimeBoxRecords b) : ValidPrimeRecord r := by
  obtain ⟨hbc, hbi, hb0, hbP⟩ := hb
  obtain ⟨hr0, hri, hrc⟩ := mem_shiftedPrimeBoxRecords.mp hr
  have hp := (Finset.mem_filter.mp hr0).2
  have hplow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr0).1).1
  refine ⟨hp, (fun i => (Finset.mem_filter.mp (hri i)).2), by simpa only [hrc] using hbc,
    ?_, ?_, ?_⟩
  · intro i
    have hhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hri i)).1).2
    have hpow : 2 * 2 ^ (b.2.1 i + 1) ≤ 2 ^ (b.1 + 2) := by
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by have := hbi i; omega)
    exact (hhi.trans hpow).trans hplow.le
  · simpa only [hrc] using hb0.trans hplow.le
  · intro i
    have hlow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hri i)).1).1
    simpa only [hrc] using (hbP i).trans_lt hlow

lemma shiftedPrimeBoxRecords_value_le {k : ℕ} {b : PrimeBox k} {r : PrimeRecord k}
    (hr : r ∈ shiftedPrimeBoxRecords b) :
    primeRecordValue r ≤ (64 * 4 ^ k) * primeBoxBaseValue b := by
  obtain ⟨hr0, hri, hrc⟩ := mem_shiftedPrimeBoxRecords.mp hr
  have hp : r.1 ≤ 8 * 2 ^ b.1 := by
    have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr0).1).2
    rw [pow_add] at h
    norm_num at h
    nlinarith
  have hq (i : Fin k) : r.2.1 i ≤ 4 * 2 ^ (b.2.1 i) := by
    have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hri i)).1).2
    rw [pow_succ] at h
    nlinarith
  calc
    primeRecordValue r ≤ (8 * 2 ^ b.1) ^ 2 * ((∏ i, 4 * 2 ^ (b.2.1 i)) * b.2.2) := by
      unfold primeRecordValue
      rw [hrc]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left hp 2)
        (Nat.mul_le_mul_right _ (Finset.prod_le_prod' fun i _ => hq i))
    _ = (64 * 4 ^ k) * primeBoxBaseValue b := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, primeBoxBaseValue]
      ring

end Erdos380
