/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedDivisors

/-!
# Erdős Problem 446: the exact-multiplicity prime construction

This file isolates the elementary arithmetic step in Ford's fixed-multiplicity
argument.  Let `a` be the small factor and let `P` be a finite set of large
primes.  If `a ≤ y`, every product of two different primes in `P` exceeds the
upper endpoint `z`, and each prime has exactly one divisor of `a` which moves
it into `(y,z]`, then `a * ∏ p ∈ P, p` has exactly `#P` divisors in that
interval.

The hypotheses are precisely the separation conditions used after (40a) in
the mathematical writeup.  The final corollary replaces the singleton-fiber
hypothesis by a natural, cross-multiplied form of an isolated divisor.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Divisors of the small factor `a` which, after multiplication by `p`,
land in the half-open target interval `(y,z]`. -/
def eligibleDivisorsForPrime (y z a p : ℕ) : Finset ℕ :=
  a.divisors.filter fun d ↦ y < d * p ∧ d * p ≤ z

/-- The corresponding divisors of the full modulus. -/
def liftedDivisorsForPrime (y z a p : ℕ) : Finset ℕ :=
  (eligibleDivisorsForPrime y z a p).image fun d ↦ d * p

theorem mem_eligibleDivisorsForPrime {y z a p d : ℕ} :
    d ∈ eligibleDivisorsForPrime y z a p ↔
      d ∈ a.divisors ∧ y < d * p ∧ d * p ≤ z := by
  simp [eligibleDivisorsForPrime]

theorem mem_liftedDivisorsForPrime {y z a p n : ℕ} :
    n ∈ liftedDivisorsForPrime y z a p ↔
      ∃ d ∈ a.divisors, y < d * p ∧ d * p ≤ z ∧ d * p = n := by
  simp only [liftedDivisorsForPrime, Finset.mem_image,
    mem_eligibleDivisorsForPrime]
  aesop

/-- Removing a finite set of prime factors from the right hand side of a
divisibility relation.  This is the elementary Euclid-lemma induction used
to recover the small divisor after the unique large prime is removed. -/
theorem dvd_smallFactor_of_dvd_mul_primeProd
    {a d : ℕ} {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hdvd : d ∣ a * ∏ p ∈ P, p)
    (havoid : ∀ p ∈ P, ¬p ∣ d) :
    d ∣ a := by
  induction P using Finset.induction_on generalizing a with
  | empty => simpa using hdvd
  | @insert p P hpP ih =>
      have hpPrime : p.Prime := hprime p (Finset.mem_insert_self p P)
      have hpAvoid : ¬p ∣ d := havoid p (Finset.mem_insert_self p P)
      have hcop : d.Coprime p :=
        (hpPrime.coprime_iff_not_dvd.mpr hpAvoid).symm
      have hdvdRest : d ∣ a * ∏ q ∈ P, q := by
        apply hcop.dvd_of_dvd_mul_left
        simpa [Finset.prod_insert hpP, mul_assoc, mul_left_comm, mul_comm] using hdvd
      exact ih
        (fun q hq ↦ hprime q (Finset.mem_insert_of_mem hq))
        hdvdRest
        (fun q hq ↦ havoid q (Finset.mem_insert_of_mem hq))

/-- Under the size and separation hypotheses, every divisor of
`a * ∏ p ∈ P, p` in `(y,z]` contains one and only one prime from `P`, and
the remaining factor divides `a`. -/
theorem intervalDivisors_eq_biUnion_lifted
    {y z a : ℕ} {P : Finset ℕ}
    (ha : 0 < a) (hay : a ≤ y)
    (hprime : ∀ p ∈ P, p.Prime)
    (_hlarge : ∀ p ∈ P, a < p)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → z < p * q) :
    (Finset.Ioc y z).filter (fun d ↦ d ∣ a * ∏ p ∈ P, p) =
      P.biUnion (liftedDivisorsForPrime y z a) := by
  classical
  ext n
  constructor
  · intro hn
    have hnIoc : n ∈ Finset.Ioc y z := (Finset.mem_filter.mp hn).1
    have hnDvd : n ∣ a * ∏ p ∈ P, p := (Finset.mem_filter.mp hn).2
    have hex : ∃ p ∈ P, p ∣ n := by
      by_contra hnone
      have hnone' : ∀ p ∈ P, ¬p ∣ n := by
        intro p hpP hpN
        exact hnone ⟨p, hpP, hpN⟩
      have hna : n ∣ a :=
        dvd_smallFactor_of_dvd_mul_primeProd hprime hnDvd hnone'
      have hnle : n ≤ a := Nat.le_of_dvd ha hna
      have hnBounds := Finset.mem_Ioc.mp hnIoc
      omega
    obtain ⟨p, hpP, hpN⟩ := hex
    have huniq : ∀ q ∈ P, q ∣ n → q = p := by
      intro q hqP hqN
      by_contra hqp
      have hpqCoprime : p.Coprime q :=
        (Nat.coprime_primes (hprime p hpP) (hprime q hqP)).mpr (Ne.symm hqp)
      have hpqDvd : p * q ∣ n :=
        hpqCoprime.mul_dvd_of_dvd_of_dvd hpN hqN
      have hnBounds := Finset.mem_Ioc.mp hnIoc
      have hpqLe : p * q ≤ n :=
        Nat.le_of_dvd (by omega : 0 < n) hpqDvd
      exact (not_lt_of_ge (hpqLe.trans hnBounds.2))
        (hsep p hpP q hqP (Ne.symm hqp))
    obtain ⟨e, rfl⟩ := hpN
    have hprodErase : (∏ q ∈ P, q) = p * ∏ q ∈ P.erase p, q :=
      (P.mul_prod_erase id hpP).symm
    have heDvdRest : e ∣ a * ∏ q ∈ P.erase p, q := by
      apply (Nat.mul_dvd_mul_iff_left (hprime p hpP).pos).mp
      rw [hprodErase] at hnDvd
      simpa [mul_assoc, mul_left_comm, mul_comm] using hnDvd
    have heAvoid : ∀ q ∈ P.erase p, ¬q ∣ e := by
      intro q hq hqe
      have hqP : q ∈ P := Finset.mem_of_mem_erase hq
      have hqN : q ∣ p * e := hqe.trans (Nat.dvd_mul_left e p)
      have hqp : q = p := huniq q hqP hqN
      exact (Finset.ne_of_mem_erase hq) hqp
    have heDvd : e ∣ a :=
      dvd_smallFactor_of_dvd_mul_primeProd
        (fun q hq ↦ hprime q (Finset.mem_of_mem_erase hq))
        heDvdRest heAvoid
    have heDiv : e ∈ a.divisors := Nat.mem_divisors.mpr ⟨heDvd, ha.ne'⟩
    rw [Finset.mem_biUnion]
    refine ⟨p, hpP, ?_⟩
    rw [mem_liftedDivisorsForPrime]
    refine ⟨e, heDiv, ?_⟩
    simpa [mul_comm] using hnIoc
  · intro hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨p, hpP, hpLift⟩ := hn
    rw [mem_liftedDivisorsForPrime] at hpLift
    obtain ⟨d, hdDiv, hydp, hdpz, rfl⟩ := hpLift
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hydp, hdpz⟩, ?_⟩
    have hda : d ∣ a := Nat.dvd_of_mem_divisors hdDiv
    have hpProd : p ∣ ∏ q ∈ P, q :=
      Finset.dvd_prod_of_mem id hpP
    obtain ⟨b, hb⟩ := hda
    obtain ⟨c, hc⟩ := hpProd
    refine ⟨b * c, ?_⟩
    rw [hb, hc]
    ring

/-- The lifted fibers belonging to distinct separated primes are disjoint. -/
theorem liftedDivisorsForPrime_pairwiseDisjoint
    {y z a : ℕ} {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → z < p * q) :
    (P : Set ℕ).PairwiseDisjoint (liftedDivisorsForPrime y z a) := by
  intro p hpP q hqP hpq
  change Disjoint (liftedDivisorsForPrime y z a p)
    (liftedDivisorsForPrime y z a q)
  rw [Finset.disjoint_left]
  intro n hnP hnQ
  rw [mem_liftedDivisorsForPrime] at hnP hnQ
  obtain ⟨d, hdDiv, hydp, hdpz, rfl⟩ := hnP
  obtain ⟨e, heDiv, hyeq, heqz, heq⟩ := hnQ
  have hpDvd : p ∣ d * p := Nat.dvd_mul_left p d
  have hqDvd : q ∣ d * p := by rw [← heq]; exact Nat.dvd_mul_left q e
  have hpqCoprime : p.Coprime q :=
    (Nat.coprime_primes (hprime p hpP) (hprime q hqP)).mpr hpq
  have hpqDvd : p * q ∣ d * p :=
    hpqCoprime.mul_dvd_of_dvd_of_dvd hpDvd hqDvd
  have hpqLe : p * q ≤ d * p :=
    Nat.le_of_dvd
      (Nat.mul_pos (Nat.pos_of_mem_divisors hdDiv) (hprime p hpP).pos)
      hpqDvd
  exact (not_lt_of_ge (hpqLe.trans hdpz)) (hsep p hpP q hqP hpq)

/-- Ford's separated-prime construction produces exactly one target
divisor for each selected prime. -/
theorem divisorCountIoc_mul_primeProd_eq_card
    {y z a : ℕ} {P : Finset ℕ}
    (ha : 0 < a) (hay : a ≤ y)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, a < p)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → z < p * q)
    (hone : ∀ p ∈ P, (eligibleDivisorsForPrime y z a p).card = 1) :
    divisorCountIoc y z (a * ∏ p ∈ P, p) = P.card := by
  rw [divisorCountIoc,
    intervalDivisors_eq_biUnion_lifted ha hay hprime hlarge hsep,
    Finset.card_biUnion (liftedDivisorsForPrime_pairwiseDisjoint hprime hsep)]
  calc
    (∑ p ∈ P, (liftedDivisorsForPrime y z a p).card) =
        ∑ p ∈ P, (eligibleDivisorsForPrime y z a p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [liftedDivisorsForPrime, Finset.card_image_of_injective]
      intro d e hde
      exact Nat.mul_right_cancel (hprime p hp).pos hde
    _ = ∑ _p ∈ P, 1 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hone p hp
    _ = P.card := by simp

/-- A purely arithmetic form of isolation for a target ratio `z / y`.
Cross multiplication avoids divisions and logarithms. -/
def RatioIsolatedDivisor (y z a d : ℕ) : Prop :=
  d ∈ a.divisors ∧
    ∀ e ∈ a.divisors, y * e < z * d → y * d < z * e → e = d

/-- An isolated divisor which moves `p` into the target interval is the
unique eligible divisor for that prime. -/
theorem eligibleDivisorsForPrime_eq_singleton_of_ratioIsolated
    {y z a p d : ℕ}
    (hiso : RatioIsolatedDivisor y z a d)
    (hdwin : y < d * p ∧ d * p ≤ z) :
    eligibleDivisorsForPrime y z a p = {d} := by
  ext e
  constructor
  · intro he
    have heData := mem_eligibleDivisorsForPrime.mp he
    have hyed : y * e < z * d := by
      calc
        y * e < (d * p) * e :=
          Nat.mul_lt_mul_of_pos_right hdwin.1
            (Nat.pos_of_mem_divisors heData.1)
        _ = (e * p) * d := by ring
        _ ≤ z * d := Nat.mul_le_mul_right d heData.2.2
    have hyde : y * d < z * e := by
      calc
        y * d < (e * p) * d :=
          Nat.mul_lt_mul_of_pos_right heData.2.1
            (Nat.pos_of_mem_divisors hiso.1)
        _ = (d * p) * e := by ring
        _ ≤ z * e := Nat.mul_le_mul_right e hdwin.2
    have hed : e = d := hiso.2 e heData.1 hyed hyde
    simpa only [Finset.mem_singleton] using hed
  · intro he
    have hed : e = d := by simpa using he
    subst e
    exact mem_eligibleDivisorsForPrime.mpr ⟨hiso.1, hdwin⟩

/-- The existing logarithmic notion of `log 2`-isolation implies the
cross-multiplied isolation condition for the dyadic interval `(y,2y]`.
This is the exact arithmetic bridge from Ford's `I(a; log 2)` to the
singleton prime fibers above. -/
theorem ratioIsolatedDivisor_two_mul_of_sigmaIsolated
    {y a d : ℕ} (_hy : 0 < y)
    (hiso : d ∈ sigmaIsolatedDivisors a (Real.log 2)) :
    RatioIsolatedDivisor y (2 * y) a d := by
  have hisoData := mem_sigmaIsolatedDivisors.mp hiso
  refine ⟨hisoData.1, ?_⟩
  intro e heDiv hyed hyde
  have hePos : 0 < e := Nat.pos_of_mem_divisors heDiv
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hisoData.1
  have heTwoD : e < 2 * d := by
    apply Nat.lt_of_mul_lt_mul_left (a := y)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hyed
  have hdTwoE : d < 2 * e := by
    apply Nat.lt_of_mul_lt_mul_left (a := y)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hyde
  have hlogE : Real.log (e : ℝ) ≤ Real.log 2 + Real.log (d : ℝ) := by
    calc
      Real.log (e : ℝ) ≤ Real.log ((2 * d : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hePos)
          (by exact_mod_cast heTwoD.le)
      _ = Real.log 2 + Real.log (d : ℝ) := by
        push_cast
        rw [Real.log_mul (by norm_num) (by exact_mod_cast hdPos.ne')]
  have hlogD : Real.log (d : ℝ) ≤ Real.log 2 + Real.log (e : ℝ) := by
    calc
      Real.log (d : ℝ) ≤ Real.log ((2 * e : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hdPos)
          (by exact_mod_cast hdTwoE.le)
      _ = Real.log 2 + Real.log (e : ℝ) := by
        push_cast
        rw [Real.log_mul (by norm_num) (by exact_mod_cast hePos.ne')]
  have hclose :
      |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2 := by
    rw [abs_le]
    constructor <;> linarith
  have heNeighbor : e ∈ sigmaNeighborDivisors a d (Real.log 2) :=
    mem_sigmaNeighborDivisors.mpr ⟨heDiv, hclose⟩
  rw [hisoData.2] at heNeighbor
  simpa using heNeighbor

/-- Exact multiplicity in the form used in Ford's fixed-`r` lower bound:
one isolated small divisor is assigned to each separated large prime. -/
theorem divisorCountIoc_mul_primeProd_eq_card_of_ratioIsolated
    {y z a : ℕ} {P : Finset ℕ}
    (ha : 0 < a) (hay : a ≤ y)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, a < p)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → z < p * q)
    (hiso : ∀ p ∈ P, ∃ d,
      RatioIsolatedDivisor y z a d ∧ y < d * p ∧ d * p ≤ z) :
    divisorCountIoc y z (a * ∏ p ∈ P, p) = P.card := by
  apply divisorCountIoc_mul_primeProd_eq_card ha hay hprime hlarge hsep
  intro p hp
  obtain ⟨d, hdIso, hdwin⟩ := hiso p hp
  rw [eligibleDivisorsForPrime_eq_singleton_of_ratioIsolated hdIso hdwin]
  simp

/-- The dyadic specialization stated directly with the logarithmic isolated
divisors used in Ford's moment estimate. -/
theorem divisorCountIoc_mul_primeProd_eq_card_of_sigmaIsolated
    {y a : ℕ} {P : Finset ℕ}
    (hy : 0 < y) (ha : 0 < a) (hay : a ≤ y)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, a < p)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * y < p * q)
    (hiso : ∀ p ∈ P, ∃ d,
      d ∈ sigmaIsolatedDivisors a (Real.log 2) ∧
        y < d * p ∧ d * p ≤ 2 * y) :
    divisorCountIoc y (2 * y) (a * ∏ p ∈ P, p) = P.card := by
  apply divisorCountIoc_mul_primeProd_eq_card_of_ratioIsolated
    ha hay hprime hlarge hsep
  intro p hp
  obtain ⟨d, hdIso, hdwin⟩ := hiso p hp
  exact ⟨d, ratioIsolatedDivisor_two_mul_of_sigmaIsolated hy hdIso, hdwin⟩

/-! ## Adjoining a rough cofactor -/

/-- A divisor not exceeding `z` is coprime to a number all of whose prime
divisors exceed `z`. -/
theorem coprime_roughCofactor_of_le
    {d b z : ℕ} (hd : 0 < d) (hdz : d ≤ z)
    (hrough : ∀ q : ℕ, q.Prime → q ∣ b → z < q) :
    d.Coprime b := by
  apply Nat.coprime_of_dvd'
  intro q hqPrime hqd hqb
  have hqLeD : q ≤ d := Nat.le_of_dvd hd hqd
  have hzq : z < q := hrough q hqPrime hqb
  omega

/-- Multiplication by a `z`-rough cofactor creates no new divisors at most
`z`, hence preserves every divisor count in `(y,z]`. -/
theorem divisorCountIoc_mul_roughCofactor
    {y z m b : ℕ}
    (hrough : ∀ q : ℕ, q.Prime → q ∣ b → z < q) :
    divisorCountIoc y z (m * b) = divisorCountIoc y z m := by
  unfold divisorCountIoc
  congr 1
  apply Finset.filter_congr
  intro d hdIoc
  have hdBounds := Finset.mem_Ioc.mp hdIoc
  constructor
  · intro hdMul
    have hcop : d.Coprime b :=
      coprime_roughCofactor_of_le (by omega) hdBounds.2 hrough
    exact hcop.dvd_of_dvd_mul_right hdMul
  · intro hdm
    exact hdm.trans (Nat.dvd_mul_right m b)

/-- Ford's full elementary shape: the isolated separated-prime modulus can
be multiplied by an arbitrary cofactor whose prime factors lie above the
target interval, without changing the exact multiplicity. -/
theorem divisorCountIoc_mul_primeProd_mul_rough_eq_card_of_sigmaIsolated
    {y a b : ℕ} {P : Finset ℕ}
    (hy : 0 < y) (ha : 0 < a) (hay : a ≤ y)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, a < p)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * y < p * q)
    (hiso : ∀ p ∈ P, ∃ d,
      d ∈ sigmaIsolatedDivisors a (Real.log 2) ∧
        y < d * p ∧ d * p ≤ 2 * y)
    (hrough : ∀ q : ℕ, q.Prime → q ∣ b → 2 * y < q) :
    divisorCountIoc y (2 * y)
        ((a * ∏ p ∈ P, p) * b) = P.card := by
  rw [divisorCountIoc_mul_roughCofactor hrough]
  exact divisorCountIoc_mul_primeProd_eq_card_of_sigmaIsolated
    hy ha hay hprime hlarge hsep hiso

end Erdos446
