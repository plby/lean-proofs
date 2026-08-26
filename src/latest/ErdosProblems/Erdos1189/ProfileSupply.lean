/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Enough distinct profiles in the optimal arithmetic order.
Informal source: Section 8.3, inequality (8.3), and Bertrand's postulate.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ArithmeticProfiles
import ErdosProblems.Erdos1189.FrameOrdering
import ErdosProblems.Erdos1189.PrimeWeights

namespace Erdos1189

open Finset

lemma primeAt_le_two_pow {s : ℕ} (hs : 3 ≤ s) : primeAt s ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num [primeAt, Nat.nth_prime_three_eq_seven]
  | succ s hs ih =>
      have hn := primeAt_succ_lt_two_mul s
      rw [pow_succ]
      omega

lemma prime_sub_one_le_two_pow_count {p : ℕ} (hp : p.Prime) :
    p - 1 ≤ 2 ^ Nat.primeCounting (p - 1) := by
  obtain ⟨s, _, hs⟩ := Nat.exists_lt_card_nth_eq hp
  have hs' : primeAt s = p := hs
  have hc : Nat.primeCounting (p - 1) = s := by
    rw [← hs', Nat.primeCounting_sub_one]
    exact Nat.primeCounting'_nth_eq s
  rw [hc, ← hs']
  exact primeAt_sub_one_le_two_pow s

lemma prime_le_two_pow_count {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    p ≤ 2 ^ Nat.primeCounting (p - 1) := by
  obtain ⟨s, _, hs⟩ := Nat.exists_lt_card_nth_eq hp
  have hs' : primeAt s = p := hs
  have hs3 : 3 ≤ s := by
    have hp3 : primeAt 3 ≤ primeAt s := by
      simpa only [primeAt, Nat.nth_prime_three_eq_seven, hs] using hp7
    exact primeAt_strictMono.le_iff_le.mp hp3
  have hc : Nat.primeCounting (p - 1) = s := by
    rw [← hs', Nat.primeCounting_sub_one]
    exact Nat.primeCounting'_nth_eq s
  rw [hc, ← hs']
  exact primeAt_le_two_pow hs3

lemma profile_count_ge_two_pow {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (c : PrimeCoordinate N) (T : Finset N.primeFactors)
    (hT : ∀ p ∈ T, p ≠ c.1 ∧ 1 ≤ precedingExponent rank c p) :
    2 ^ T.card ≤ (profileModuli rank c).card := by
  let f (D : T.powerset) : ArithmeticProfile rank c := fun p =>
    ⟨if p.val ∈ D.val then 1 else 0, by
      split_ifs with hp
      · exact Nat.lt_succ_of_le (hT p.val (mem_powerset.mp D.property hp)).2
      · exact Nat.succ_pos _⟩
  have hf : Function.Injective f := by
    intro D E h
    apply Subtype.ext
    ext p
    by_cases hp : p ∈ T
    · have hpc := (hT p hp).1
      have hh := congrArg (fun F : ArithmeticProfile rank c => (F ⟨p, hpc⟩).val) h
      change (if p ∈ D.val then 1 else 0 : ℕ) = (if p ∈ E.val then 1 else 0) at hh
      split_ifs at hh with hd he <;> simp_all
    · have hpD : p ∉ D.val := fun h => hp (mem_powerset.mp D.property h)
      have hpE : p ∉ E.val := fun h => hp (mem_powerset.mp E.property h)
      simp [hpD, hpE]
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, card_powerset, Fintype.card_pi, Fintype.card_fin,
    card_profileModuli] using hc

lemma primeFactors_below_card {N p : ℕ}
    (hbelow : ∀ q : ℕ, q.Prime → q < p → q ∈ N.primeFactors) :
    (univ.filter (fun q : N.primeFactors => q.val < p)).card = Nat.primeCounting (p - 1) := by
  have himage : (univ.filter (fun q : N.primeFactors => q.val < p)).image Subtype.val =
      Nat.primesLE (p - 1) := by
    ext q
    simp only [mem_image, mem_filter, mem_univ, true_and, Nat.mem_primesLE]
    constructor
    · rintro ⟨q', hqp, rfl⟩
      exact ⟨by omega, Nat.prime_of_mem_primeFactors q'.2⟩
    · rintro ⟨hqp, hq⟩
      have hqp' : q < p := by have := hq.pos; omega
      exact ⟨⟨q, hbelow q hq hqp'⟩, hqp', rfl⟩
  have hc := congrArg Finset.card himage
  simpa only [card_image_of_injective _ Subtype.val_injective,
    Nat.primesLE_card_eq_primeCounting] using hc

theorem profile_count_ge_prime_weight {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (hrank : IsArithmeticRank rank)
    (href : ∀ c i, coordinateScore c.1 c.2 < coordinateScore i.1 i.2 → rank c < rank i)
    (c : PrimeCoordinate N)
    (hbelow : ∀ q : ℕ, q.Prime → q < c.1.val → q ∈ N.primeFactors) :
    coordinateSize c - 1 ≤ (profileModuli rank c).card := by
  let T := univ.filter (fun q : N.primeFactors => q.val < c.1.val)
  have hT : ∀ p ∈ T, p ≠ c.1 ∧ 1 ≤ precedingExponent rank c p := by
    intro p hp
    have hpc := (mem_filter.mp hp).2
    have hpne : p ≠ c.1 := by intro h; rw [h] at hpc; exact lt_irrefl _ hpc
    have hpExp : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp p.2)
    have hfirst := href ⟨p, ⟨0, hpExp⟩⟩ c
      (first_prime_score_lt (Nat.prime_of_mem_primeFactors c.1.2) hpc c.2)
    refine ⟨hpne, ?_⟩
    exact (lt_precedingExponent_iff hrank c p ⟨0, hpExp⟩).mpr hfirst
  have hcount := profile_count_ge_two_pow rank c T hT
  rw [show T.card = Nat.primeCounting (c.1.val - 1) from primeFactors_below_card hbelow] at hcount
  exact (prime_sub_one_le_two_pow_count (Nat.prime_of_mem_primeFactors c.1.2)).trans hcount

lemma primesLE_erase_top (P : ℕ) : (Nat.primesLE P).erase P = Nat.primesLE (P - 1) := by
  ext q
  simp only [mem_erase, Nat.mem_primesLE]
  constructor
  · rintro ⟨hne, hqP, hq⟩
    exact ⟨by omega, hq⟩
  · rintro ⟨hqP, hq⟩
    have := hq.pos
    exact ⟨by omega, by omega, hq⟩

theorem terminal_profile_count {N P : ℕ} (hP : P.Prime) (hP7 : 7 ≤ P)
    (hpf : N.primeFactors = Nat.primesLE P)
    {rank : PrimeCoordinate N → ℕ} (hrank : IsArithmeticRank rank)
    (c : PrimeCoordinate N) (hlast : ∀ i, i ≠ c → rank i < rank c) :
    P ≤ (profileModuli rank c).card := by
  let T := (univ : Finset N.primeFactors).erase c.1
  have hT : ∀ p ∈ T, p ≠ c.1 ∧ 1 ≤ precedingExponent rank c p := by
    intro p hp
    have hpc := (mem_erase.mp hp).1
    have hpExp : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp p.2)
    have hne : (⟨p, ⟨0, hpExp⟩⟩ : PrimeCoordinate N) ≠ c :=
      fun h => hpc (congrArg Sigma.fst h)
    refine ⟨hpc, ?_⟩
    exact (lt_precedingExponent_iff hrank c p ⟨0, hpExp⟩).mpr (hlast _ hne)
  have hcount := profile_count_ge_two_pow rank c T hT
  have hcard : T.card = Nat.primeCounting (P - 1) := by
    have hmem : P ∈ Nat.primesLE P := Nat.mem_primesLE.mpr ⟨le_rfl, hP⟩
    have hPc := card_erase_of_mem hmem
    rw [primesLE_erase_top, Nat.primesLE_card_eq_primeCounting] at hPc
    simp only [T, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_coe, hpf]
    exact hPc.symm
  rw [hcard] at hcount
  exact (prime_le_two_pow_count hP hP7).trans hcount

end Erdos1189
