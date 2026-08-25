/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.AffineBoundingSieve

/-!
# Removing slope primes from the affine sieve

In a collision application the constants are large primes, so no sieving
prime divides them.  A prime dividing both slopes has no local root and is
simply omitted from the sieve product.  At every remaining prime at least
one slope is invertible, giving a legitimate local density.
-/

namespace Erdos822

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction

/-- Sieving primes in the usual interval which do not divide both affine
slopes. -/
def slopeAwareSievePrimes (a b z Y : ℕ) : Finset ℕ :=
  (Erdos387.sievePrimes z Y).filter fun p ↦ ¬ p ∣ a ∨ ¬ p ∣ b

/-- Product of the slope-aware sieving primes. -/
def slopeAwareSievePrimeProduct (a b z Y : ℕ) : ℕ :=
  ∏ p ∈ slopeAwareSievePrimes a b z Y, p

@[simp]
theorem mem_slopeAwareSievePrimes_iff {a b z Y p : ℕ} :
    p ∈ slopeAwareSievePrimes a b z Y ↔
      p.Prime ∧ z < p ∧ p < Y ∧ (¬ p ∣ a ∨ ¬ p ∣ b) := by
  simp [slopeAwareSievePrimes, Erdos387.mem_sievePrimes, and_assoc]

theorem slopeAwareSievePrimeProduct_squarefree (a b z Y : ℕ) :
    Squarefree (slopeAwareSievePrimeProduct a b z Y) := by
  unfold slopeAwareSievePrimeProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (coprime_primes
      (mem_slopeAwareSievePrimes_iff.mp hp).1
      (mem_slopeAwareSievePrimes_iff.mp hq).1).mpr hpq
  · intro p hp
    exact (mem_slopeAwareSievePrimes_iff.mp hp).1.squarefree

theorem slopeAwareSievePrimeProduct_pos (a b z Y : ℕ) :
    0 < slopeAwareSievePrimeProduct a b z Y := by
  unfold slopeAwareSievePrimeProduct
  exact Finset.prod_pos fun p hp =>
    (mem_slopeAwareSievePrimes_iff.mp hp).1.pos

theorem prime_mem_slopeAwareSievePrimes_of_dvd_product
    {a b z Y p : ℕ} (hp : p.Prime)
    (hdiv : p ∣ slopeAwareSievePrimeProduct a b z Y) :
    p ∈ slopeAwareSievePrimes a b z Y := by
  unfold slopeAwareSievePrimeProduct at hdiv
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
  have hqPrime := (mem_slopeAwareSievePrimes_iff.mp hq).1
  have hpEq : p = q := ((hqPrime.dvd_iff_eq hp.ne_one).mp hpq).symm
  simpa [hpEq] using hq

theorem pos_of_dvd_slopeAwareSievePrimeProduct
    {a b z Y d : ℕ}
    (hd : d ∣ slopeAwareSievePrimeProduct a b z Y) : 0 < d :=
  Nat.pos_of_dvd_of_pos hd (slopeAwareSievePrimeProduct_pos a b z Y)

/-- Parameters surviving the slope-aware sieve. -/
def slopeAwareSiftedTwoAffineCandidates
    (a s b t X z Y : ℕ) : Finset ℕ :=
  (Finset.range X).filter fun n ↦
    Nat.Coprime (slopeAwareSievePrimeProduct a b z Y)
      (twoAffineProduct a s b t n)

/-- Bounding sieve whose prime product omits primes dividing both slopes. -/
noncomputable def slopeAwareTwoAffineBoundingSieve
    (a s b t X z Y : ℕ) (hz : 2 ≤ z)
    (hconstants : ∀ p ∈ slopeAwareSievePrimes a b z Y,
      ¬ p ∣ s ∧ ¬ p ∣ t) : BoundingSieve := by
  classical
  let I := Finset.range X
  exact
    { support := I.image (twoAffineProduct a s b t)
      prodPrimes := slopeAwareSievePrimeProduct a b z Y
      prodPrimes_squarefree := slopeAwareSievePrimeProduct_squarefree a b z Y
      weights := fun q ↦
        ((I.filter fun n ↦ twoAffineProduct a s b t n = q).card : ℝ)
      weights_nonneg := fun _ ↦ by positivity
      totalMass := X
      nu := twoAffineNu a s b t
      nu_mult := twoAffineNu_mult a s b t
      nu_pos_of_prime := by
        intro p hp hpDiv
        have hpMem :=
          prime_mem_slopeAwareSievePrimes_of_dvd_product hp hpDiv
        have hdata := mem_slopeAwareSievePrimes_iff.mp hpMem
        exact (twoAffineNu_pos_lt_one_of_not_dvd_constants_one_slope
          hp (hz.trans_lt hdata.2.1)
          (hconstants p hpMem).1 (hconstants p hpMem).2 hdata.2.2.2).1
      nu_lt_one_of_prime := by
        intro p hp hpDiv
        have hpMem :=
          prime_mem_slopeAwareSievePrimes_of_dvd_product hp hpDiv
        have hdata := mem_slopeAwareSievePrimes_iff.mp hpMem
        exact (twoAffineNu_pos_lt_one_of_not_dvd_constants_one_slope
          hp (hz.trans_lt hdata.2.1)
          (hconstants p hpMem).1 (hconstants p hpMem).2 hdata.2.2.2).2 }

theorem slopeAwareTwoAffineBoundingSieve_totalMass
    {a s b t X z Y : ℕ} {hz : 2 ≤ z}
    {hconstants : ∀ p ∈ slopeAwareSievePrimes a b z Y,
      ¬ p ∣ s ∧ ¬ p ∣ t} :
    (slopeAwareTwoAffineBoundingSieve a s b t X z Y hz hconstants).totalMass = X :=
  rfl

theorem slopeAwareTwoAffineBoundingSieve_multSum
    {a s b t X z Y d : ℕ} {hz : 2 ≤ z}
    {hconstants : ∀ p ∈ slopeAwareSievePrimes a b z Y,
      ¬ p ∣ s ∧ ¬ p ∣ t} :
    (slopeAwareTwoAffineBoundingSieve a s b t X z Y hz hconstants).multSum d =
      ((divisibleTwoAffineCandidates a s b t X d).card : ℝ) := by
  classical
  let I := Finset.range X
  let f := twoAffineProduct a s b t
  rw [BoundingSieve.multSum]
  change (∑ q ∈ I.image f,
      if d ∣ q then ((I.filter fun n ↦ f n = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦ d ∣ q,
          (I.filter fun n ↦ f n = q).card) =
        (I.filter fun n ↦ d ∣ f n).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

theorem slopeAwareTwoAffineBoundingSieve_siftedSum
    {a s b t X z Y : ℕ} {hz : 2 ≤ z}
    {hconstants : ∀ p ∈ slopeAwareSievePrimes a b z Y,
      ¬ p ∣ s ∧ ¬ p ∣ t} :
    (slopeAwareTwoAffineBoundingSieve a s b t X z Y hz hconstants).siftedSum =
      ((slopeAwareSiftedTwoAffineCandidates a s b t X z Y).card : ℝ) := by
  classical
  let I := Finset.range X
  let f := twoAffineProduct a s b t
  rw [BoundingSieve.siftedSum]
  change (∑ q ∈ I.image f,
      if Nat.Coprime (slopeAwareSievePrimeProduct a b z Y) q then
        ((I.filter fun n ↦ f n = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦
          Nat.Coprime (slopeAwareSievePrimeProduct a b z Y) q,
          (I.filter fun n ↦ f n = q).card) =
        (I.filter fun n ↦
          Nat.Coprime (slopeAwareSievePrimeProduct a b z Y) (f n)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

theorem slopeAwareTwoAffineBoundingSieve_abs_rem_le_nuClasses
    {a s b t X z Y d : ℕ} {hz : 2 ≤ z}
    {hconstants : ∀ p ∈ slopeAwareSievePrimes a b z Y,
      ¬ p ∣ s ∧ ¬ p ∣ t}
    (hd : d ∣ slopeAwareSievePrimeProduct a b z Y) :
    |(slopeAwareTwoAffineBoundingSieve a s b t X z Y hz hconstants).rem d| ≤
      twoAffineNuClasses a s b t d := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (slopeAwareSievePrimeProduct_squarefree a b z Y)
  rw [BoundingSieve.rem, slopeAwareTwoAffineBoundingSieve_multSum,
    slopeAwareTwoAffineBoundingSieve_totalMass]
  change
    |↑(divisibleTwoAffineCandidates a s b t X d).card -
        twoAffineNu a s b t d * (X : ℝ)| ≤
      (twoAffineNuClasses a s b t d : ℝ)
  rw [twoAffineNu_squarefree hsq]
  simpa [mul_div_assoc, mul_comm, mul_left_comm] using
    abs_card_divisibleTwoAffineCandidates_sub_density_of_squarefree
      (a := a) (s := s) (b := b) (t := t) (X := X)
      hsq (pos_of_dvd_slopeAwareSievePrimeProduct hd)

end Erdos822
