import Mathlib.Data.Nat.Squarefree

/-!
# Erdős Problem 888: the two largest prime factors

This file isolates the elementary factorization used to assign a squarefree
integer with at least two prime factors to a block.  Such an integer has a
unique expression

`a = c * p * q`

in which `p < q` are prime and every prime factor of `c` is smaller than
`p`.  The existence proof explicitly removes the largest and second-largest
members of `a.primeFactors`; the uniqueness theorem is stated independently
of that construction so downstream files can use it directly.
-/

namespace Erdos888

/-- `a = c * p * q`, with `p` and `q` the two largest prime factors of `a`.

The condition on `c.primeFactors` is phrased without a redundant primality
hypothesis: membership in `Nat.primeFactors` already implies primality. -/
def TwoLargestPrimeDecomposition (a c p q : ℕ) : Prop :=
  a = c * p * q ∧
    p.Prime ∧ q.Prime ∧ p < q ∧ Squarefree c ∧
      ∀ r ∈ c.primeFactors, r < p

/-- A squarefree positive integer with at least two distinct prime factors
has a two-largest-prime decomposition. -/
theorem exists_twoLargestPrimeDecomposition {a : ℕ}
    (_ha : 0 < a) (hsq : Squarefree a) (hcard : 2 ≤ a.primeFactors.card) :
    ∃ c p q, TwoLargestPrimeDecomposition a c p q := by
  classical
  let s := a.primeFactors
  have hs_nonempty : s.Nonempty := by
    rw [← Finset.card_pos]
    dsimp [s]
    omega
  let q := s.max' hs_nonempty
  have hq_mem : q ∈ s := by
    dsimp [q]
    exact s.max'_mem hs_nonempty
  have hs_erase_q_nonempty : (s.erase q).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hq_mem]
    change 0 < a.primeFactors.card - 1
    omega
  let p := (s.erase q).max' hs_erase_q_nonempty
  have hp_mem : p ∈ s.erase q := by
    dsimp [p]
    exact (s.erase q).max'_mem hs_erase_q_nonempty
  let t := (s.erase q).erase p
  let c := ∏ r ∈ t, r
  have hq_prime : q.Prime := by
    exact Nat.prime_of_mem_primeFactors (by simpa [s] using hq_mem)
  have hp_prime : p.Prime := by
    exact Nat.prime_of_mem_primeFactors (by
      simpa [s] using Finset.mem_of_mem_erase hp_mem)
  have hp_lt_q : p < q := by
    simpa [q] using s.lt_max'_of_mem_erase_max' hs_nonempty hp_mem
  have ht_subset : t ⊆ s := by
    intro r hr
    exact Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase (by simpa [t] using hr))
  have ht_prime : ∀ r ∈ t, r.Prime := by
    intro r hr
    exact Nat.prime_of_mem_primeFactors (by simpa [s] using ht_subset hr)
  have hprod_q : (∏ r ∈ s.erase q, r) * q = ∏ r ∈ s, r := by
    simpa using Finset.prod_erase_mul (s := s) (f := fun r : ℕ => r) hq_mem
  have hprod_p : (∏ r ∈ t, r) * p = ∏ r ∈ s.erase q, r := by
    simpa [t] using
      Finset.prod_erase_mul (s := s.erase q) (f := fun r : ℕ => r) hp_mem
  have ha_decomp : a = c * p * q := by
    calc
      a = ∏ r ∈ s, r := by
        simpa [s] using (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ = (∏ r ∈ s.erase q, r) * q := hprod_q.symm
      _ = ((∏ r ∈ t, r) * p) * q := by rw [hprod_p]
      _ = c * p * q := by rfl
  have hc_dvd_a : c ∣ a := by
    refine ⟨p * q, ?_⟩
    simpa [mul_assoc] using ha_decomp
  have hc_squarefree : Squarefree c := hsq.squarefree_of_dvd hc_dvd_a
  have hc_primeFactors : c.primeFactors = t := by
    simpa [c] using Nat.primeFactors_prod ht_prime
  have hc_small : ∀ r ∈ c.primeFactors, r < p := by
    intro r hr
    have hr_t : r ∈ t := by simpa [hc_primeFactors] using hr
    have hr_erase_p : r ∈ (s.erase q).erase p := by simpa [t] using hr_t
    simpa [p] using
      (s.erase q).lt_max'_of_mem_erase_max' hs_erase_q_nonempty hr_erase_p
  exact ⟨c, p, q, ha_decomp, hp_prime, hq_prime, hp_lt_q,
    hc_squarefree, hc_small⟩

/-- The ordered two-largest-prime decomposition is unique.

This theorem is deliberately independent of the construction in
`exists_twoLargestPrimeDecomposition`: it is the injectivity fact needed
when block encodings remember only `(c, p, q)`. -/
theorem TwoLargestPrimeDecomposition.unique
    {a c p q c' p' q' : ℕ}
    (h : TwoLargestPrimeDecomposition a c p q)
    (h' : TwoLargestPrimeDecomposition a c' p' q') :
    c = c' ∧ p = p' ∧ q = q' := by
  rcases h with ⟨ha, hp, hq, hpq, hc, hc_small⟩
  rcases h' with ⟨ha', hp', hq', hpq', hc', hc'_small⟩
  have hq_dvd_right : q ∣ c' * p' * q' := by
    rw [← ha', ha]
    exact dvd_mul_left q (c * p)
  have hq_le_q' : q ≤ q' := by
    rcases hq.dvd_mul.mp hq_dvd_right with hq_cp | hq_q'
    · rcases hq.dvd_mul.mp hq_cp with hq_c | hq_p'
      · have hq_mem : q ∈ c'.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq, hq_c, hc'.ne_zero⟩
        exact (hc'_small q hq_mem).le.trans hpq'.le
      · exact (Nat.prime_dvd_prime_iff_eq hq hp').mp hq_p' |>.le.trans hpq'.le
    · exact (Nat.prime_dvd_prime_iff_eq hq hq').mp hq_q' |>.le
  have hq'_dvd_left : q' ∣ c * p * q := by
    rw [← ha, ha']
    exact dvd_mul_left q' (c' * p')
  have hq'_le_q : q' ≤ q := by
    rcases hq'.dvd_mul.mp hq'_dvd_left with hq'_cp | hq'_q
    · rcases hq'.dvd_mul.mp hq'_cp with hq'_c | hq'_p
      · have hq'_mem : q' ∈ c.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq', hq'_c, hc.ne_zero⟩
        exact (hc_small q' hq'_mem).le.trans hpq.le
      · exact (Nat.prime_dvd_prime_iff_eq hq' hp).mp hq'_p |>.le.trans hpq.le
    · exact (Nat.prime_dvd_prime_iff_eq hq' hq).mp hq'_q |>.le
  have hqq' : q = q' := Nat.le_antisymm hq_le_q' hq'_le_q
  have hcp : c * p = c' * p' := by
    apply mul_right_cancel₀ hq.ne_zero
    simpa [hqq'] using ha.symm.trans ha'
  have hp_dvd_right : p ∣ c' * p' := by
    rw [← hcp]
    exact dvd_mul_left p c
  have hp_le_p' : p ≤ p' := by
    rcases hp.dvd_mul.mp hp_dvd_right with hp_c | hp_p'
    · have hp_mem : p ∈ c'.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hp_c, hc'.ne_zero⟩
      exact (hc'_small p hp_mem).le
    · exact (Nat.prime_dvd_prime_iff_eq hp hp').mp hp_p' |>.le
  have hp'_dvd_left : p' ∣ c * p := by
    rw [hcp]
    exact dvd_mul_left p' c'
  have hp'_le_p : p' ≤ p := by
    rcases hp'.dvd_mul.mp hp'_dvd_left with hp'_c | hp'_p
    · have hp'_mem : p' ∈ c.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp', hp'_c, hc.ne_zero⟩
      exact (hc_small p' hp'_mem).le
    · exact (Nat.prime_dvd_prime_iff_eq hp' hp).mp hp'_p |>.le
  have hpp' : p = p' := Nat.le_antisymm hp_le_p' hp'_le_p
  have hcc' : c = c' := by
    apply mul_right_cancel₀ hp.ne_zero
    simpa [hpp'] using hcp
  exact ⟨hcc', hpp', hqq'⟩

/-- Equality of the represented integers is equivalent to equality of all
three coordinates for valid ordered decompositions. -/
theorem twoLargestPrimeDecomposition_injective
    {a b c p q c' p' q' : ℕ}
    (ha : TwoLargestPrimeDecomposition a c p q)
    (hb : TwoLargestPrimeDecomposition b c' p' q') :
    a = b ↔ c = c' ∧ p = p' ∧ q = q' := by
  constructor
  · intro hab
    exact ha.unique (hab ▸ hb)
  · rintro ⟨rfl, rfl, rfl⟩
    exact ha.1.trans hb.1.symm

end Erdos888
