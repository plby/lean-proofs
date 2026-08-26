/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The divisor family in part (v) of Erdős Problem 1189.
Informal result: Zhi-Wei Sun, "On covering numbers", Integers 7 (2007), A33.
Formal author: OpenAI Codex.

The proof below constructs the cover and proves its irreducibility directly
using the elementary fibre obstruction, without assuming Sun or Simpson.
-/

import ErdosProblems.Erdos1189.BinaryChain
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Finset.NatDivisors

namespace Erdos1189

open Finset
open scoped Pointwise

/-- The `p` moduli divisible by the odd prime. -/
def sunTerminal (p : ℕ) : Finset ℕ := (range p).image fun j => p * 2 ^ j

/-- The explicit modulus set of Sun's two-prime family. -/
def sunModuli (p : ℕ) : Finset ℕ := binaryChain (p - 1) ∪ sunTerminal p

lemma prime_coprime_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p.Coprime 2 := by
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact hp.ne_one h
  · exact hp2 h

lemma sunModuli_nontrivial {p d : ℕ} (hp : p.Prime) (hd : d ∈ sunModuli p) : 1 < d := by
  rcases mem_union.mp hd with hd | hd
  · exact binaryChain_nontrivial hd
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hd
    have : 0 < 2 ^ j := by positivity
    nlinarith [hp.two_le]

lemma sunModuli_dvd {p d : ℕ} (hd : d ∈ sunModuli p) :
    d ∣ p * 2 ^ (p - 1) := by
  rcases mem_union.mp hd with hd | hd
  · exact (binaryChain_dvd hd).trans (dvd_mul_left _ _)
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
    exact Nat.mul_dvd_mul_left p (pow_dvd_pow 2 (by
      have := mem_range.mp hj
      omega))

/-- Natural residues for Sun's cover. -/
def sunResidue (p : ℕ) (hcop : p.Coprime 2) (d : ℕ) : ℕ :=
  if p ∣ d then
    (Nat.chineseRemainder (hcop.pow_right (d.factorization 2)) (d.factorization 2) 0).val
  else 2 ^ (d.factorization 2 - 1)

lemma sunResidue_binary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i : ℕ) :
    sunResidue p (prime_coprime_two hp hp2) (2 ^ (i + 1)) = 2 ^ i := by
  have hnot : ¬ p ∣ 2 ^ (i + 1) := by
    intro h
    exact (hp.coprime_iff_not_dvd.mp (prime_coprime_two hp hp2)) (hp.dvd_of_dvd_pow h)
  rw [sunResidue, if_neg hnot, Nat.factorization_pow_self Nat.prime_two]
  simp

lemma sunResidue_terminal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) :
    sunResidue p (prime_coprime_two hp hp2) (p * 2 ^ j) =
      (Nat.chineseRemainder ((prime_coprime_two hp hp2).pow_right j) j 0).val := by
  have hfact : (p * 2 ^ j).factorization 2 = j := by
    rw [Nat.factorization_mul hp.ne_zero (by positivity), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two]
    simp [hp.factorization, Ne.symm hp2]
  rw [sunResidue, if_pos (dvd_mul_right p (2 ^ j))]
  exact congrArg (fun t : ℕ =>
    (Nat.chineseRemainder ((prime_coprime_two hp hp2).pow_right t) t 0).val) hfact

lemma sun_natural_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) :
    ∃ d ∈ sunModuli p, x ≡ sunResidue p (prime_coprime_two hp hp2) d [MOD d] := by
  rcases binary_cover_or_dvd (p - 1) x with ⟨i, hi, hxi⟩ | hdiv
  · refine ⟨2 ^ (i + 1), mem_union_left _ (mem_binaryChain.mpr ⟨i, hi, rfl⟩), ?_⟩
    rw [sunResidue_binary hp hp2]
    exact hxi
  · let j := x % p
    have hj : j < p := Nat.mod_lt x hp.pos
    refine ⟨p * 2 ^ j, mem_union_right _ (mem_image.mpr ⟨j, mem_range.mpr hj, rfl⟩), ?_⟩
    rw [sunResidue_terminal hp hp2]
    apply (Nat.modEq_and_modEq_iff_modEq_mul ((prime_coprime_two hp hp2).pow_right j)).mp
    constructor
    · exact (Nat.mod_modEq x p).symm.trans (Nat.chineseRemainder _ j 0).property.1.symm
    · have hjdiv : 2 ^ j ∣ x := (pow_dvd_pow 2 (by omega : j ≤ p - 1)).trans hdiv
      have hxzero : x ≡ 0 [MOD 2 ^ j] := Nat.modEq_zero_iff_dvd.mpr hjdiv
      exact hxzero.trans (Nat.chineseRemainder _ j 0).property.2.symm

lemma sun_covering {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : IsCoveringSet (sunModuli p) := by
  refine ⟨fun d hd => sunModuli_nontrivial hp hd,
    fun d => sunResidue p (prime_coprime_two hp hp2) d, ?_⟩
  apply (covers_iff_finite_period (N := p * 2 ^ (p - 1))
    (Nat.mul_pos hp.pos (by positivity)) (fun d hd => sunModuli_dvd hd)).mpr
  intro x
  obtain ⟨d, hd, hxd⟩ := sun_natural_cover hp hp2 x
  exact ⟨d, hd, Int.natCast_modEq_iff.mpr hxd⟩

lemma sunTerminal_card {p : ℕ} (hp : 0 < p) : (sunTerminal p).card = p := by
  rw [sunTerminal, card_image_of_injective, card_range]
  intro i j h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (Nat.eq_of_mul_eq_mul_left hp h)

lemma sun_irreducible {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsIrreducibleCoveringSet (sunModuli p) := by
  refine ⟨sun_covering hp hp2, ?_⟩
  intro E hE hcover
  obtain ⟨a, ha⟩ := hcover.2
  have hnat : ∀ z : ℕ, ∃ d ∈ E, z ≡ canonicalResidue a d [MOD d] := by
    intro z
    obtain ⟨d, hd, hzd⟩ := ha z
    exact ⟨d, hd, (nat_modEq_canonicalResidue_iff a (by
      have := hcover.1 d hd
      omega) z).mpr hzd⟩
  have heq := subset_eq_of_fibre_cover (D := binaryChain (p - 1)) (B := sunTerminal p)
    (N := 2 ^ (p - 1)) (p := p) (by positivity) hp.pos
    ((prime_coprime_two hp hp2).symm.pow_left (p - 1))
    (fun d hd => binaryChain_pos hd) (fun d hd => binaryChain_dvd hd)
    (binaryChain_weight (p - 1)) (sunTerminal_card hp.pos)
    (by
      intro d hd
      obtain ⟨j, _, rfl⟩ := mem_image.mp hd
      exact dvd_mul_right _ _)
    (mem_image.mpr ⟨p - 1, mem_range.mpr (by have := hp.pos; omega), rfl⟩) hE.subset hnat
  exact hE.ne heq

lemma nontrivialDivisors_sun {p : ℕ} (hp : p.Prime) :
    nontrivialDivisors (2 ^ (p - 1) * p) = sunModuli p := by
  ext d
  constructor
  · intro hd
    obtain ⟨hd, hdgt⟩ := mem_filter.mp hd
    rw [Nat.divisors_mul, hp.divisors] at hd
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_mul.mp hd
    obtain ⟨i, hi, rfl⟩ := (Nat.mem_divisors_prime_pow Nat.prime_two (p - 1)).mp hb
    rcases mem_insert.mp hc with rfl | hc
    · rw [mul_one] at hdgt ⊢
      have hipos : 0 < i := by
        by_contra h
        have : i = 0 := by omega
        simp [this] at hdgt
      exact mem_union_left _ (mem_binaryChain.mpr ⟨i - 1, by omega, by congr 1; omega⟩)
    · have : c = p := mem_singleton.mp hc
      subst c
      exact mem_union_right _ (mem_image.mpr
        ⟨i, mem_range.mpr (by have := hp.pos; omega), Nat.mul_comm _ _⟩)
  · intro hd
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨by simpa only [mul_comm] using sunModuli_dvd hd,
        Nat.mul_ne_zero (by positivity) hp.ne_zero⟩,
      sunModuli_nontrivial hp hd⟩

/-- Part (v), with no imported covering theorem: every odd prime yields an
irreducible set of all nontrivial divisors, including the number itself. -/
theorem irreducible_sun_divisors {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsIrreducibleCoveringSet (nontrivialDivisors (2 ^ (p - 1) * p)) := by
  rw [nontrivialDivisors_sun hp]
  exact sun_irreducible hp hp2

lemma sun_number_strictMono : StrictMono (fun p : ℕ => 2 ^ (p - 1) * p) := by
  apply strictMono_nat_of_lt_succ
  intro p
  cases p with
  | zero => norm_num
  | succ p =>
      simp only [Nat.add_sub_cancel, pow_succ]
      have : 0 < 2 ^ p := by positivity
      nlinarith

/-- Infinitely many integers have an irreducible set of nontrivial divisors. -/
theorem infinite_irreducible_divisor_sets :
    {n : ℕ | IsIrreducibleCoveringSet (nontrivialDivisors n)}.Infinite := by
  have hprimes : ({p : ℕ | p.Prime} \ {2}).Infinite :=
    Nat.infinite_setOfPred_prime.sdiff (Set.finite_singleton 2)
  have himage := hprimes.image sun_number_strictMono.injective.injOn
  apply himage.mono
  rintro n ⟨p, hp, rfl⟩
  exact irreducible_sun_divisors hp.1 (by simpa using hp.2)

end Erdos1189
