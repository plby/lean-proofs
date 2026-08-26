import ErdosProblems.Erdos380.PrimeCompression
import ErdosProblems.Erdos380.PrimeRadical
import ErdosProblems.Erdos380.SingletonCount

/-!
# Comparing singleton counts by replacing a prime

Remove one prime from the cofactor after the largest-prime square, and
replace it by its compressed prime. The square is left intact. Recording
the compressed prime and a bounded index tag makes the operation injective.
-/

open scoped BigOperators

namespace Erdos380

def singletonCofactor (n : ℕ) : ℕ := n / largestPrimeFactor n ^ 2

lemma SingletonBad.square_mul_cofactor {n : ℕ} (hn : SingletonBad n) :
    largestPrimeFactor n ^ 2 * singletonCofactor n = n :=
  Nat.mul_div_cancel' hn.2

lemma SingletonBad.cofactor_pos {n : ℕ} (hn : SingletonBad n) :
    0 < singletonCofactor n := by
  have h := hn.square_mul_cofactor
  by_contra hnonpos
  have hz : singletonCofactor n = 0 := by omega
  rw [hz, mul_zero] at h
  have := hn.1
  omega

lemma SingletonBad.cofactor_dvd {n : ℕ} (hn : SingletonBad n) :
    singletonCofactor n ∣ n := ⟨largestPrimeFactor n ^ 2, by
      simpa only [mul_comm] using hn.square_mul_cofactor.symm⟩

noncomputable def singletonCompressedValue (K n : ℕ) : ℕ :=
  largestPrimeFactor n ^ 2 *
    (compressedPrime K (largestPrimeFactor (singletonCofactor n)) *
      (singletonCofactor n / largestPrimeFactor (singletonCofactor n)))

lemma SingletonBad.cofactor_split {n : ℕ} (hn : SingletonBad n)
    (hq : 1 < largestPrimeFactor (singletonCofactor n)) :
    largestPrimeFactor (singletonCofactor n) *
      (singletonCofactor n / largestPrimeFactor (singletonCofactor n)) =
        singletonCofactor n := by
  apply Nat.mul_div_cancel'
  apply largestPrimeFactor_dvd
  have hle := largestPrimeFactor_le_self (Nat.succ_le_iff.mpr hn.cofactor_pos)
  omega

lemma SingletonBad.cofactor_prime {n : ℕ} (hn : SingletonBad n)
    (hq : 1 < largestPrimeFactor (singletonCofactor n)) :
    (largestPrimeFactor (singletonCofactor n)).Prime := by
  apply largestPrimeFactor_prime
  have hle := largestPrimeFactor_le_self (Nat.succ_le_iff.mpr hn.cofactor_pos)
  omega

lemma SingletonBad.compressedValue_largest {K n : ℕ} (hn : SingletonBad n)
    (hq : 1 < largestPrimeFactor (singletonCofactor n)) :
    largestPrimeFactor (singletonCompressedValue K n) = largestPrimeFactor n := by
  let p := largestPrimeFactor n
  let m := singletonCofactor n
  let q := largestPrimeFactor m
  let b := m / q
  let r := compressedPrime K q
  have hp : p.Prime := largestPrimeFactor_prime (by have := hn.1; omega)
  have hqp : q.Prime := hn.cofactor_prime hq
  have hsplit : q * b = m := hn.cofactor_split hq
  have hb : 0 < b := by
    have hm := hn.cofactor_pos
    change 0 < m at hm
    by_contra h
    have hz : b = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hsplit
    omega
  have hmn : largestPrimeFactor m ≤ p :=
    largestPrimeFactor_mono_dvd (by have := hn.1; omega) hn.cofactor_dvd
  have hbq : largestPrimeFactor b ≤ q :=
    largestPrimeFactor_mono_dvd hn.cofactor_pos.ne'
      ⟨q, by simpa only [mul_comm] using hsplit.symm⟩
  have hr : r.Prime := compressedPrime_prime K q
  have hrq : r ≤ q := compressedPrime_le hqp
  change largestPrimeFactor (p ^ 2 * (r * b)) = p
  rw [largestPrimeFactor_mul (pow_ne_zero _ hp.ne_zero) (mul_ne_zero hr.ne_zero hb.ne'),
    largestPrimeFactor_pow p (by decide), largestPrimeFactor_of_prime hp,
    largestPrimeFactor_mul hr.ne_zero hb.ne', largestPrimeFactor_of_prime hr]
  exact max_eq_left (max_le (hrq.trans hmn) (hbq.trans hmn))

lemma SingletonBad.compressedValue_bad {K n : ℕ} (hn : SingletonBad n)
    (hq : 1 < largestPrimeFactor (singletonCofactor n)) :
    SingletonBad (singletonCompressedValue K n) := by
  have hl := hn.compressedValue_largest (K := K) hq
  have hp := largestPrimeFactor_prime (by have := hn.1; omega : 1 < n)
  have hsq : largestPrimeFactor (singletonCompressedValue K n) ^ 2 ∣
      singletonCompressedValue K n := by
    rw [hl]
    exact dvd_mul_right _ _
  have hpos : 1 ≤ singletonCompressedValue K n := by
    by_contra h
    have hz : singletonCompressedValue K n = 0 := by omega
    rw [hz, largestPrimeFactor_zero] at hl
    have := hp.two_le
    omega
  have hle := largestPrimeFactor_le_self hpos
  exact ⟨by rw [hl] at hle; exact hp.two_le.trans hle, hsq⟩

lemma SingletonBad.compressedValue_mul_le {C K n : ℕ} (hn : SingletonBad n)
    (hq : 1 < largestPrimeFactor (singletonCofactor n))
    (hscale : C * compressedPrime K (largestPrimeFactor (singletonCofactor n)) ≤
      largestPrimeFactor (singletonCofactor n)) :
    C * singletonCompressedValue K n ≤ n := by
  calc
    C * singletonCompressedValue K n = largestPrimeFactor n ^ 2 *
        ((C * compressedPrime K (largestPrimeFactor (singletonCofactor n))) *
          (singletonCofactor n / largestPrimeFactor (singletonCofactor n))) := by
      unfold singletonCompressedValue
      ring
    _ ≤ largestPrimeFactor n ^ 2 * singletonCofactor n := by
      exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hscale)).trans_eq
        (congrArg (fun a => largestPrimeFactor n ^ 2 * a) (hn.cofactor_split hq))
    _ = n := hn.square_mul_cofactor

lemma singletonCompressedValue_with_tag_injective {K n m : ℕ}
    (hn : SingletonBad n) (hm : SingletonBad m)
    (hqn : 1 < largestPrimeFactor (singletonCofactor n))
    (hqm : 1 < largestPrimeFactor (singletonCofactor m))
    (hv : singletonCompressedValue K n = singletonCompressedValue K m)
    (hr : compressedPrime K (largestPrimeFactor (singletonCofactor n)) =
      compressedPrime K (largestPrimeFactor (singletonCofactor m)))
    (htag : Nat.primeCounting' (largestPrimeFactor (singletonCofactor n)) % K =
      Nat.primeCounting' (largestPrimeFactor (singletonCofactor m)) % K) : n = m := by
  have hp : largestPrimeFactor n = largestPrimeFactor m := by
    rw [← hn.compressedValue_largest (K := K) hqn,
      ← hm.compressedValue_largest (K := K) hqm, hv]
  have hq := compressedPrime_with_tag_injective (hn.cofactor_prime hqn)
    (hm.cofactor_prime hqm) hr htag
  have hquot : singletonCofactor n / largestPrimeFactor (singletonCofactor n) =
      singletonCofactor m / largestPrimeFactor (singletonCofactor m) := by
    unfold singletonCompressedValue at hv
    rw [hp] at hv
    have hp0 : 0 < largestPrimeFactor m ^ 2 :=
      pow_pos (lt_of_lt_of_le Nat.zero_lt_one (one_le_largestPrimeFactor m)) 2
    have h := Nat.eq_of_mul_eq_mul_left hp0 hv
    rw [hr] at h
    exact Nat.eq_of_mul_eq_mul_left (compressedPrime_prime K _).pos h
  have hcof : singletonCofactor n = singletonCofactor m := by
    calc
      singletonCofactor n = largestPrimeFactor (singletonCofactor n) *
          (singletonCofactor n / largestPrimeFactor (singletonCofactor n)) :=
        (hn.cofactor_split hqn).symm
      _ = largestPrimeFactor (singletonCofactor m) *
          (singletonCofactor m / largestPrimeFactor (singletonCofactor m)) :=
        congrArg₂ (· * ·) hq hquot
      _ = singletonCofactor m := hm.cofactor_split hqm
  calc
    n = largestPrimeFactor n ^ 2 * singletonCofactor n := hn.square_mul_cofactor.symm
    _ = largestPrimeFactor m ^ 2 * singletonCofactor m := by rw [hp, hcof]
    _ = m := hm.square_mul_cofactor

def largePrimeFactors (n R : ℕ) : Finset ℕ := n.primeFactors.filter fun p => R ≤ p

lemma largePrimeFactors_card_log_le {n R : ℕ} (hn : 0 < n) (hR : 1 ≤ R) :
    (largePrimeFactors n R).card * Real.log (R : ℝ) ≤ Real.log (n : ℝ) := by
  calc
    (largePrimeFactors n R).card * Real.log (R : ℝ) =
        ∑ _ ∈ largePrimeFactors n R, Real.log (R : ℝ) := by simp
    _ ≤ ∑ p ∈ largePrimeFactors n R, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < R))
      exact_mod_cast (Finset.mem_filter.mp hp).2
    _ ≤ Real.log (n : ℝ) := sum_log_distinct_prime_divisors_le hn
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (fun p hp => Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

lemma largePrimeFactors_card_le_log_div {n N R : ℕ} (hn : 0 < n)
    (hnN : n ≤ N) (hR : 1 < R) :
    ((largePrimeFactors n R).card : ℝ) ≤ Real.log (N : ℝ) / Real.log (R : ℝ) := by
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast hR))).mpr
  exact (largePrimeFactors_card_log_le hn hR.le).trans
    (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnN))

noncomputable def singletonCompressionRecords (N R K : ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (singletonBadUpTo N).biUnion fun n =>
    ((largePrimeFactors n R).product (Finset.range K)).image fun rt => (n, rt)

lemma singletonCompressionRecords_card_le (N R K : ℕ) :
    (singletonCompressionRecords N R K).card ≤
      K * ∑ n ∈ singletonBadUpTo N, (largePrimeFactors n R).card := by
  classical
  calc
    (singletonCompressionRecords N R K).card ≤
        ∑ n ∈ singletonBadUpTo N,
          (((largePrimeFactors n R).product (Finset.range K)).image fun rt => (n, rt)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ n ∈ singletonBadUpTo N, (largePrimeFactors n R).card * K := by
      apply Finset.sum_le_sum
      intro n _
      calc
        _ ≤ ((largePrimeFactors n R).product (Finset.range K)).card := Finset.card_image_le
        _ = (largePrimeFactors n R).card * K := by simp
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The loss in this comparison is the number of possible large prime
divisors of the output, times the fixed size of the index tag. -/
theorem singleton_compression_card_le {C K N R : ℕ} (hC : 0 < C) (hK : 0 < K)
    (s : Finset ℕ) (hbad : ∀ n ∈ s, SingletonBad n)
    (hbound : ∀ n ∈ s, n ≤ C * N)
    (hprime : ∀ n ∈ s, 1 < largestPrimeFactor (singletonCofactor n))
    (hscale : ∀ n ∈ s,
      C * compressedPrime K (largestPrimeFactor (singletonCofactor n)) ≤
        largestPrimeFactor (singletonCofactor n))
    (hlarge : ∀ n ∈ s,
      R ≤ compressedPrime K (largestPrimeFactor (singletonCofactor n))) :
    s.card ≤ K * ∑ n ∈ singletonBadUpTo N, (largePrimeFactors n R).card := by
  classical
  apply le_trans _ (singletonCompressionRecords_card_le N R K)
  apply Finset.card_le_card_of_injOn (fun n => (singletonCompressedValue K n,
    compressedPrime K (largestPrimeFactor (singletonCofactor n)),
    Nat.primeCounting' (largestPrimeFactor (singletonCofactor n)) % K))
  · intro n hn
    have hnB := hbad n hn
    have hvB := hnB.compressedValue_bad (K := K) (hprime n hn)
    have hvN : singletonCompressedValue K n ≤ N := by
      have h := (hnB.compressedValue_mul_le (hprime n hn) (hscale n hn)).trans (hbound n hn)
      exact Nat.le_of_mul_le_mul_left h hC
    have hv0 : singletonCompressedValue K n ≠ 0 := by have := hvB.1; omega
    have hrv : compressedPrime K (largestPrimeFactor (singletonCofactor n)) ∣
        singletonCompressedValue K n :=
      dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    apply Finset.mem_biUnion.mpr
    refine ⟨singletonCompressedValue K n, mem_singletonBadUpTo.mpr
      ⟨by have := hvB.1; omega, hvN, hvB⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(_, _), Finset.mem_product.mpr ⟨?_, Finset.mem_range.mpr (Nat.mod_lt _ hK)⟩, rfl⟩
    exact Finset.mem_filter.mpr ⟨(compressedPrime_prime K _).mem_primeFactors hrv hv0,
      hlarge n hn⟩
  · intro n hn m hm h
    exact singletonCompressedValue_with_tag_injective (hbad n hn) (hbad m hm)
      (hprime n hn) (hprime m hm) (congrArg Prod.fst h)
      (congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h)
      (congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h)

theorem singleton_compression_card_le_log {C K N R : ℕ} (hC : 0 < C) (hK : 0 < K)
    (hR : 1 < R) (s : Finset ℕ) (hbad : ∀ n ∈ s, SingletonBad n)
    (hbound : ∀ n ∈ s, n ≤ C * N)
    (hprime : ∀ n ∈ s, 1 < largestPrimeFactor (singletonCofactor n))
    (hscale : ∀ n ∈ s,
      C * compressedPrime K (largestPrimeFactor (singletonCofactor n)) ≤
        largestPrimeFactor (singletonCofactor n))
    (hlarge : ∀ n ∈ s,
      R ≤ compressedPrime K (largestPrimeFactor (singletonCofactor n))) :
    (s.card : ℝ) ≤ K * (Real.log (N : ℝ) / Real.log (R : ℝ)) *
      (singletonBadUpTo N).card := by
  have h := singleton_compression_card_le hC hK s hbad hbound hprime hscale hlarge
  have hsum : (∑ n ∈ singletonBadUpTo N, ((largePrimeFactors n R).card : ℝ)) ≤
      (singletonBadUpTo N).card * (Real.log (N : ℝ) / Real.log (R : ℝ)) := by
    calc
      _ ≤ ∑ _ ∈ singletonBadUpTo N, Real.log (N : ℝ) / Real.log (R : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, hnN, _⟩ := mem_singletonBadUpTo.mp hn
        exact largePrimeFactors_card_le_log_div (by omega) hnN hR
      _ = _ := by simp
  calc
    (s.card : ℝ) ≤ (K : ℝ) * ∑ n ∈ singletonBadUpTo N, ((largePrimeFactors n R).card : ℝ) := by
      exact_mod_cast h
    _ ≤ (K : ℝ) * ((singletonBadUpTo N).card * (Real.log (N : ℝ) / Real.log (R : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg K)
    _ = _ := by ring

noncomputable def largeCofactorSingletons (N Q : ℕ) : Finset ℕ := by
  classical
  exact (singletonBadUpTo N).filter fun n => Q ≤ largestPrimeFactor (singletonCofactor n)

/-- A fixed enlargement of the cutoff costs only a logarithmic factor on
singletons having a sufficiently large prime in their cofactor. No local
smooth-number asymptotic is used. -/
theorem exists_largeCofactorSingletons_dilation_bound {C : ℕ} (hC : 1 ≤ C) :
    ∃ P₀ : ℕ, ∀ N R : ℕ, 1 < R →
      ((largeCofactorSingletons (C * N) (max P₀ (128 * C * R))).card : ℝ) ≤
        (8 * C : ℝ) * (Real.log (N : ℝ) / Real.log (R : ℝ)) *
          (singletonBadUpTo N).card := by
  classical
  obtain ⟨P₀, hscale⟩ := exists_compressedPrime_scale_bounds hC
  refine ⟨P₀, ?_⟩
  intro N R hR
  let s := largeCofactorSingletons (C * N) (max P₀ (128 * C * R))
  have hbad : ∀ n ∈ s, SingletonBad n := fun n hn =>
    (mem_singletonBadUpTo.mp (Finset.mem_filter.mp hn).1).2.2
  have hbound : ∀ n ∈ s, n ≤ C * N := fun n hn =>
    (mem_singletonBadUpTo.mp (Finset.mem_filter.mp hn).1).2.1
  have hqbound : ∀ n ∈ s, max P₀ (128 * C * R) ≤
      largestPrimeFactor (singletonCofactor n) := fun n hn => (Finset.mem_filter.mp hn).2
  have hprime : ∀ n ∈ s, 1 < largestPrimeFactor (singletonCofactor n) := by
    intro n hn
    have hlarge := (le_max_right P₀ (128 * C * R)).trans (hqbound n hn)
    have hR' : R ≤ 128 * C * R := Nat.le_mul_of_pos_left R (by omega)
    exact hR.trans_le (hR'.trans hlarge)
  have hsc : ∀ n ∈ s,
      C * compressedPrime (8 * C) (largestPrimeFactor (singletonCofactor n)) ≤
        largestPrimeFactor (singletonCofactor n) ∧
      largestPrimeFactor (singletonCofactor n) ≤
        128 * C * compressedPrime (8 * C) (largestPrimeFactor (singletonCofactor n)) := by
    intro n hn
    exact hscale _ ((le_max_left _ _).trans (hqbound n hn))
      ((hbad n hn).cofactor_prime (hprime n hn))
  have hlarge : ∀ n ∈ s,
      R ≤ compressedPrime (8 * C) (largestPrimeFactor (singletonCofactor n)) := by
    intro n hn
    have h := ((le_max_right _ _).trans (hqbound n hn)).trans (hsc n hn).2
    exact Nat.le_of_mul_le_mul_left h (by omega)
  have h := singleton_compression_card_le_log (by omega : 0 < C)
    (by omega : 0 < 8 * C) hR s hbad hbound hprime (fun n hn => (hsc n hn).1) hlarge
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

end Erdos380
