/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Prime-exponent profiles for finite arithmetic-frame counts.
Informal argument: unique factorization and initial segments in an arithmetic order.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameChoices

namespace Erdos1189

open Finset

def primePowerProfile (N : ℕ) (e : N.primeFactors → ℕ) : ℕ :=
  ∏ p : N.primeFactors, p.val ^ e p

lemma primePowerProfile_ne_zero (N : ℕ) (e : N.primeFactors → ℕ) :
    primePowerProfile N e ≠ 0 :=
  prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero

lemma primePowerProfile_factorization (N : ℕ) (e : N.primeFactors → ℕ)
    (p : N.primeFactors) : (primePowerProfile N e).factorization p = e p := by
  rw [primePowerProfile, Nat.factorization_prod_apply
    (fun q _ => pow_ne_zero _ (Nat.prime_of_mem_primeFactors q.2).ne_zero), sum_eq_single p]
  · exact Nat.factorization_pow_self (Nat.prime_of_mem_primeFactors p.2)
  · intro q _ hqp
    have hqp' : q.val ≠ p.val := fun h => hqp (Subtype.ext h)
    simp [Nat.factorization_pow, (Nat.prime_of_mem_primeFactors q.2).factorization, hqp']
  · simp

lemma primePowerProfile_injective (N : ℕ) : Function.Injective (primePowerProfile N) := by
  intro e f h
  funext p
  have hh := congrArg (fun d : ℕ => d.factorization p) h
  simpa only [primePowerProfile_factorization] using hh

lemma primePowerProfile_full {N : ℕ} (hN : N ≠ 0) :
    primePowerProfile N (fun p => N.factorization p) = N := by
  exact (Nat.prod_primeFactors_coe_pow_factorization hN).symm

lemma primePowerProfile_dvd {N : ℕ} (hN : N ≠ 0) {e : N.primeFactors → ℕ}
    (he : ∀ p, e p ≤ N.factorization p) : primePowerProfile N e ∣ N := by
  calc
    _ ∣ primePowerProfile N (fun p => N.factorization p) :=
      prod_dvd_prod_of_dvd _ _ (fun p _ => pow_dvd_pow p.val (he p))
    _ = N := primePowerProfile_full hN

lemma primePowerProfile_factorization_of_not_mem {N : ℕ} (hN : N ≠ 0)
    {e : N.primeFactors → ℕ} (he : ∀ p, e p ≤ N.factorization p)
    {p : ℕ} (hp : p ∉ N.primeFactors) : (primePowerProfile N e).factorization p = 0 := by
  have hle := (Nat.factorization_le_iff_dvd (primePowerProfile_ne_zero N e) hN).mpr
    (primePowerProfile_dvd hN he) p
  have hzero : N.factorization p = 0 := by
    exact Finsupp.notMem_support_iff.mp hp
  omega

lemma primePowerProfile_of_divisor {N d : ℕ} (hN : N ≠ 0) (hd : d ∣ N) :
    primePowerProfile N (fun p => d.factorization p) = d := by
  have hd0 := ne_zero_of_dvd_ne_zero hN hd
  have hle := (Nat.factorization_le_iff_dvd hd0 hN).mpr hd
  apply Nat.eq_of_factorization_eq (primePowerProfile_ne_zero _ _) hd0
  intro p
  by_cases hp : p ∈ N.primeFactors
  · exact primePowerProfile_factorization N _ ⟨p, hp⟩
  · rw [primePowerProfile_factorization_of_not_mem hN (fun p => hle p) hp]
    have hzero : N.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    have := hle p
    omega

lemma fin_lt_card_filter_iff {n r : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) (e : Fin n) :
    e.val < (univ.filter (fun j => f j < r)).card ↔ f e < r := by
  constructor
  · intro he
    by_contra hnot
    have hsub : univ.filter (fun j => f j < r) ⊆ Iio e := by
      intro j hj
      apply mem_Iio.mpr
      apply hf.lt_iff_lt.mp
      have hj' := (mem_filter.mp hj).2
      omega
    have hc := card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega
  · intro he
    have hsub : Iic e ⊆ univ.filter (fun j => f j < r) := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _, (hf.monotone (mem_Iic.mp hj)).trans_lt he⟩
    have hc := card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega

def IsArithmeticRank {N : ℕ} (rank : PrimeCoordinate N → ℕ) : Prop :=
  ∀ p : N.primeFactors, StrictMono (fun e => rank ⟨p, e⟩)

def precedingExponent {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (c : PrimeCoordinate N) (p : N.primeFactors) : ℕ :=
  (univ.filter (fun e : Fin (N.factorization p) => rank ⟨p, e⟩ < rank c)).card

lemma precedingExponent_le {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (c : PrimeCoordinate N) (p : N.primeFactors) :
    precedingExponent rank c p ≤ N.factorization p := by
  exact (card_filter_le _ _).trans (by simp)

lemma lt_precedingExponent_iff {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (hrank : IsArithmeticRank rank) (c : PrimeCoordinate N) (p : N.primeFactors)
    (e : Fin (N.factorization p)) :
    e.val < precedingExponent rank c p ↔ rank ⟨p, e⟩ < rank c :=
  fin_lt_card_filter_iff (hrank p) e

lemma precedingExponent_self {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (hrank : IsArithmeticRank rank) (c : PrimeCoordinate N) :
    precedingExponent rank c c.1 = c.2.val := by
  unfold precedingExponent
  have hs : univ.filter (fun e : Fin (N.factorization c.1) => rank ⟨c.1, e⟩ < rank c) =
      Iio c.2 := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_Iio]
    exact (hrank c.1).lt_iff_lt
  rw [hs, Fin.card_Iio]

end Erdos1189
