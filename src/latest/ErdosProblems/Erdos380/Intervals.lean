import ErdosProblems.Erdos380.Core
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Arithmetic structure of bad intervals

The product's prime factors, prime-power divisibility at a unique multiple,
and the elementary exclusion of intervals reaching halfway to zero.
-/

open scoped BigOperators

namespace Erdos380

lemma largestPrimeFactor_mono_dvd {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) :
    largestPrimeFactor m ≤ largestPrimeFactor n := by
  apply largestPrimeFactor_le (one_le_largestPrimeFactor n)
  intro p hp hpm
  exact prime_le_largestPrimeFactor hn hp (hpm.trans hmn)

lemma largestPrimeFactor_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    largestPrimeFactor (∏ i ∈ s, f i) =
      max 1 (s.sup fun i => largestPrimeFactor (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, largestPrimeFactor_mul hfa (Finset.prod_ne_zero_iff.mpr hfs),
      ih hfs, Finset.sup_insert]
    change max (largestPrimeFactor (f a)) (max 1 _) =
      max 1 (max (largestPrimeFactor (f a)) _)
    omega

lemma intervalPrime_eq_sup {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v) :
    intervalPrime u v = (Finset.Icc u v).sup largestPrimeFactor := by
  have hf : ∀ n ∈ Finset.Icc u v, n ≠ 0 := by
    intro n hn
    have := (Finset.mem_Icc.mp hn).1
    omega
  unfold intervalPrime intervalProduct
  rw [largestPrimeFactor_prod _ (fun n => n) hf]
  apply max_eq_right
  exact (one_le_largestPrimeFactor u).trans
    (Finset.le_sup (f := largestPrimeFactor) (Finset.mem_Icc.mpr ⟨le_rfl, huv⟩))

lemma largestPrimeFactor_le_intervalPrime {u v n : ℕ} (hu : 1 ≤ u)
    (hn : n ∈ Finset.Icc u v) : largestPrimeFactor n ≤ intervalPrime u v :=
  largestPrimeFactor_mono_dvd (intervalProduct_pos hu).ne' (dvd_intervalProduct hn)

lemma prime_dvd_intervalProduct_iff {u v p : ℕ} (hp : p.Prime) :
    p ∣ intervalProduct u v ↔ ∃ n ∈ Finset.Icc u v, p ∣ n := by
  exact hp.prime.dvd_finsetProd_iff id

lemma eq_of_dvd_of_mem_short_interval {u v p a b : ℕ}
    (ha : a ∈ Finset.Icc u v) (hb : b ∈ Finset.Icc u v)
    (hpa : p ∣ a) (hpb : p ∣ b) (hshort : v - u < p) : a = b := by
  obtain ⟨hau, hav⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hbu, hbv⟩ := Finset.mem_Icc.mp hb
  rcases le_total a b with hab | hba
  · have hd : p ∣ b - a := Nat.dvd_sub hpb hpa
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega : b - a < p)
    omega
  · have hd : p ∣ a - b := Nat.dvd_sub hpa hpb
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega : a - b < p)
    omega

lemma factorization_intervalProduct {u v p : ℕ} (hu : 1 ≤ u) :
    (intervalProduct u v).factorization p =
      ∑ n ∈ Finset.Icc u v, n.factorization p := by
  unfold intervalProduct
  rw [Nat.factorization_prod]
  · simp
  · intro n hn
    have := (Finset.mem_Icc.mp hn).1
    omega

lemma pow_dvd_intervalProduct_iff_of_unique {u v p a k : ℕ}
    (hu : 1 ≤ u) (hp : p.Prime) (ha : a ∈ Finset.Icc u v)
    (hunique : ∀ n ∈ Finset.Icc u v, p ∣ n → n = a) :
    p ^ k ∣ intervalProduct u v ↔ p ^ k ∣ a := by
  have ha0 : a ≠ 0 := by
    have := (Finset.mem_Icc.mp ha).1
    omega
  rw [hp.pow_dvd_iff_le_factorization (intervalProduct_pos hu).ne',
    hp.pow_dvd_iff_le_factorization ha0, factorization_intervalProduct hu]
  have heq : (∑ n ∈ Finset.Icc u v, n.factorization p) = a.factorization p := by
    apply Finset.sum_eq_single a
    · intro n hn hna
      exact Nat.factorization_eq_zero_of_not_dvd fun hpn => hna (hunique n hn hpn)
    · exact fun h => (h ha).elim
  rw [heq]

lemma BadInterval.exists_square_anchor_of_short {u v : ℕ} (hbad : BadInterval u v)
    (hshort : v - u < intervalPrime u v) :
    ∃ a ∈ Finset.Icc u v,
      intervalPrime u v ^ 2 ∣ a ∧ largestPrimeFactor a = intervalPrime u v := by
  have hp := largestPrimeFactor_prime hbad.2.2.1
  have hpd := largestPrimeFactor_dvd hbad.2.2.1
  obtain ⟨a, ha, hpa⟩ := (prime_dvd_intervalProduct_iff hp).mp hpd
  have hunique : ∀ n ∈ Finset.Icc u v, intervalPrime u v ∣ n → n = a := by
    intro n hn hpn
    exact eq_of_dvd_of_mem_short_interval hn ha hpn hpa hshort
  have hsquare := (pow_dvd_intervalProduct_iff_of_unique hbad.1 hp ha hunique).mp
    hbad.2.2.2
  refine ⟨a, ha, hsquare, le_antisymm (largestPrimeFactor_le_intervalPrime hbad.1 ha) ?_⟩
  have ha0 : a ≠ 0 := by
    have := (Finset.mem_Icc.mp ha).1
    have := hbad.1
    omega
  exact prime_le_largestPrimeFactor ha0 hp hpa

lemma eq_of_dvd_lt_two_mul {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (hdvd : p ∣ n) (hlt : n < 2 * p) : n = p := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    simp [this] at hn
  have hk2 : k < 2 := by nlinarith
  have : k = 1 := by omega
  simp [this]

lemma BadInterval.right_lt_two_mul_left {u v : ℕ} (hbad : BadInterval u v) :
    v + 2 ≤ 2 * u := by
  have hu := hbad.1
  have huv := hbad.2.1
  have hv2 : 2 ≤ v := by
    by_contra h
    have hv1 : v = 1 := by omega
    have hu1 : u = 1 := by omega
    have hprod := hbad.2.2.1
    simp [hu1, hv1] at hprod
  by_contra h
  obtain ⟨q, hq, hqlo, hqhi⟩ := Nat.exists_prime_lt_and_le_two_mul (v / 2) (by omega)
  have hqmem : q ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hqdiv : q ∣ intervalProduct u v := dvd_intervalProduct hqmem
  have hqp : q ≤ intervalPrime u v :=
    prime_le_largestPrimeFactor (intervalProduct_pos hu).ne' hq hqdiv
  have hp := largestPrimeFactor_prime hbad.2.2.1
  have hpd := largestPrimeFactor_dvd hbad.2.2.1
  obtain ⟨a, ha, hpa⟩ := (prime_dvd_intervalProduct_iff hp).mp hpd
  have hlarge : v < 2 * intervalPrime u v := by omega
  have haeq : a = intervalPrime u v :=
    eq_of_dvd_lt_two_mul hp.pos (by have := (Finset.mem_Icc.mp ha).1; omega)
      hpa (lt_of_le_of_lt (Finset.mem_Icc.mp ha).2 hlarge)
  have hpmem : intervalPrime u v ∈ Finset.Icc u v := haeq ▸ ha
  have hunique : ∀ n ∈ Finset.Icc u v, intervalPrime u v ∣ n → n = intervalPrime u v := by
    intro n hn hpn
    exact eq_of_dvd_lt_two_mul hp.pos (by have := (Finset.mem_Icc.mp hn).1; omega)
      hpn (lt_of_le_of_lt (Finset.mem_Icc.mp hn).2 hlarge)
  have hsq := (pow_dvd_intervalProduct_iff_of_unique hu hp hpmem hunique).mp hbad.2.2.2
  have hle := Nat.le_of_dvd hp.pos hsq
  nlinarith [hp.two_le]

lemma BadInterval.two_mul_intervalPrime_le_right {u v : ℕ} (hbad : BadInterval u v) :
    2 * intervalPrime u v ≤ v := by
  by_contra h
  have hlarge : v < 2 * intervalPrime u v := by omega
  have hp := largestPrimeFactor_prime hbad.2.2.1
  obtain ⟨a, ha, hpa⟩ := (prime_dvd_intervalProduct_iff hp).mp
    (largestPrimeFactor_dvd hbad.2.2.1)
  have heq : a = intervalPrime u v := eq_of_dvd_lt_two_mul hp.pos
    (by have := (Finset.mem_Icc.mp ha).1; have := hbad.1; omega) hpa
    ((Finset.mem_Icc.mp ha).2.trans_lt hlarge)
  have hpmem : intervalPrime u v ∈ Finset.Icc u v := heq ▸ ha
  have hunique : ∀ n ∈ Finset.Icc u v, intervalPrime u v ∣ n → n = intervalPrime u v := by
    intro n hn hpn
    exact eq_of_dvd_lt_two_mul hp.pos
      (by have := (Finset.mem_Icc.mp hn).1; have := hbad.1; omega) hpn
      ((Finset.mem_Icc.mp hn).2.trans_lt hlarge)
  have hsq := (pow_dvd_intervalProduct_iff_of_unique hbad.1 hp hpmem hunique).mp hbad.2.2.2
  have hle := Nat.le_of_dvd hp.pos hsq
  nlinarith [hp.two_le]

/-- Bad intervals contain no primes; no Sylvester--Schur input is needed here. -/
lemma BadInterval.not_prime_mem {u v n : ℕ} (hbad : BadInterval u v)
    (hn : n ∈ Finset.Icc u v) : ¬ n.Prime := by
  intro hp
  have hnp : n ≤ intervalPrime u v := by
    rw [← largestPrimeFactor_of_prime hp]
    exact largestPrimeFactor_le_intervalPrime hbad.1 hn
  have hu := (Finset.mem_Icc.mp hn).1
  have hv := hbad.right_lt_two_mul_left
  have hpv := hbad.two_mul_intervalPrime_le_right
  omega

end Erdos380
