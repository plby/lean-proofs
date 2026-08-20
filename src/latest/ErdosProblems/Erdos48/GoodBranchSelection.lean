/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PrimeChains

/-!
# Finite selection for the FLP good branch

This file contains the exact finite bookkeeping which removes the
prime-chain closure of the bad moduli from the shifted-smooth primes.  The
only estimate used here is the elementary count of multiples of two distinct
primes; all analytic lower bounds remain explicit hypotheses.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- A finite, decidable formulation of `u`-smoothness. -/
def SmoothAtMost (u n : ℕ) : Prop :=
  ∀ q ∈ n.primeFactors, q ≤ u

theorem smoothAtMost_iff_prime_dvd {u n : ℕ} (hn : n ≠ 0) :
    SmoothAtMost u n ↔ ∀ q : ℕ, q.Prime → q ∣ n → q ≤ u := by
  constructor
  · intro h q hq hqn
    exact h q ((Nat.mem_primeFactors).2 ⟨hq, hqn, hn⟩)
  · intro h q hq
    have hqData := Nat.mem_primeFactors.mp hq
    exact h q hqData.1 hqData.2.1

/-- Primes `p ≤ x` whose shift `p+1` is `u`-smooth. -/
def smoothShiftedPrimes (x u : ℕ) : Finset ℕ :=
  by
    classical
    exact (Nat.primesLE x).filter fun p ↦ SmoothAtMost u (p + 1)

@[simp] theorem mem_smoothShiftedPrimes {x u p : ℕ} :
    p ∈ smoothShiftedPrimes x u ↔
      p ≤ x ∧ p.Prime ∧ SmoothAtMost u (p + 1) := by
  classical
  rw [smoothShiftedPrimes, Finset.mem_filter, Nat.mem_primesLE]
  tauto

/-- Retain only shifts divisible by none of the forbidden primes. -/
def avoidingShiftedDivisors (A T : Finset ℕ) : Finset ℕ :=
  A.filter fun p ↦ ∀ t ∈ T, ¬t ∣ p + 1

@[simp] theorem mem_avoidingShiftedDivisors {A T : Finset ℕ} {p : ℕ} :
    p ∈ avoidingShiftedDivisors A T ↔
      p ∈ A ∧ ∀ t ∈ T, ¬t ∣ p + 1 := by
  simp [avoidingShiftedDivisors]

/-- There are exactly `U/d` positive multiples of `d` at most `U`. -/
theorem card_positiveMultiples_le (U d : ℕ) :
    ((Finset.range (U + 1)).filter fun n ↦ n ≠ 0 ∧ d ∣ n).card = U / d := by
  simpa only [Nat.succ_eq_add_one] using Nat.card_multiples' U d

/-- Inside any finite set bounded by `x`, shifts divisible by two distinct
primes have cardinality at most `(x+1)/(q*t)`. -/
theorem card_filter_two_prime_dvd_shift_le
    {A : Finset ℕ} {x q t : ℕ}
    (hA : ∀ p ∈ A, p ≤ x) (hq : q.Prime) (ht : t.Prime) (hqt : q ≠ t) :
    (A.filter fun p ↦ q ∣ p + 1 ∧ t ∣ p + 1).card ≤
      (x + 1) / (q * t) := by
  classical
  let M := (Finset.range (x + 2)).filter fun n ↦
    n ≠ 0 ∧ q * t ∣ n
  let S := A.filter fun p ↦ q ∣ p + 1 ∧ t ∣ p + 1
  have hinj : Set.InjOn (fun p : ℕ ↦ p + 1) S := by
    intro a ha b hb hab
    exact Nat.add_right_cancel hab
  have hsub : S.image (fun p ↦ p + 1) ⊆ M := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have hpData := Finset.mem_filter.mp hp
    have hpBound : p ≤ x := hA p hpData.1
    have hcop : q.Coprime t := (Nat.coprime_primes hq ht).2 hqt
    have hprod : q * t ∣ p + 1 :=
      hcop.mul_dvd_of_dvd_of_dvd hpData.2.1 hpData.2.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega : p + 1 < x + 2),
        ⟨by omega, hprod⟩⟩
  calc
    (A.filter fun p ↦ q ∣ p + 1 ∧ t ∣ p + 1).card = S.card := rfl
    _ = (S.image fun p ↦ p + 1).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ M.card := Finset.card_le_card hsub
    _ = (x + 1) / (q * t) := by
      exact card_positiveMultiples_le (x + 1) (q * t)

/-- Removing every shift divisible by a forbidden prime costs at most the
sum of the pairwise divisibility counts. -/
theorem card_filter_dvd_le_avoiding_add_loss
    {A T : Finset ℕ} {x q : ℕ}
    (hA : ∀ p ∈ A, p ≤ x) (hq : q.Prime)
    (hT : ∀ t ∈ T, t.Prime) (hqT : q ∉ T) :
    (A.filter fun p ↦ q ∣ p + 1).card ≤
      ((avoidingShiftedDivisors A T).filter fun p ↦ q ∣ p + 1).card +
        ∑ t ∈ T, (x + 1) / (q * t) := by
  classical
  let raw := A.filter fun p ↦ q ∣ p + 1
  let kept := (avoidingShiftedDivisors A T).filter fun p ↦ q ∣ p + 1
  let collisions := T.biUnion fun t ↦
    A.filter fun p ↦ q ∣ p + 1 ∧ t ∣ p + 1
  have hcover : raw ⊆ kept ∪ collisions := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    by_cases hav : ∀ t ∈ T, ¬t ∣ p + 1
    · exact Finset.mem_union_left _ <| Finset.mem_filter.mpr
        ⟨mem_avoidingShiftedDivisors.mpr ⟨hpData.1, hav⟩, hpData.2⟩
    · push_neg at hav
      obtain ⟨t, htT, htp⟩ := hav
      exact Finset.mem_union_right _ <| Finset.mem_biUnion.mpr
        ⟨t, htT, Finset.mem_filter.mpr ⟨hpData.1, hpData.2, htp⟩⟩
  have hcollisionCard : collisions.card ≤
      ∑ t ∈ T, (A.filter fun p ↦ q ∣ p + 1 ∧ t ∣ p + 1).card := by
    exact Finset.card_biUnion_le
  have hpair :
      (∑ t ∈ T,
          (A.filter fun p ↦ q ∣ p + 1 ∧ t ∣ p + 1).card) ≤
        ∑ t ∈ T, (x + 1) / (q * t) := by
    apply Finset.sum_le_sum
    intro t htT
    exact card_filter_two_prime_dvd_shift_le hA hq (hT t htT)
      (fun hqt ↦ hqT (hqt ▸ htT))
  calc
    (A.filter fun p ↦ q ∣ p + 1).card = raw.card := rfl
    _ ≤ (kept ∪ collisions).card := Finset.card_le_card hcover
    _ ≤ kept.card + collisions.card := Finset.card_union_le kept collisions
    _ ≤ kept.card +
        ∑ t ∈ T,
          (A.filter fun p ↦ q ∣ p + 1 ∧ t ∣ p + 1).card :=
      Nat.add_le_add_left hcollisionCard _
    _ ≤ kept.card + ∑ t ∈ T, (x + 1) / (q * t) :=
      Nat.add_le_add_left hpair _
    _ = ((avoidingShiftedDivisors A T).filter
          fun p ↦ q ∣ p + 1).card +
        ∑ t ∈ T, (x + 1) / (q * t) := rfl

/-- Convenient lower-bound form: if the raw count covers both the desired
survivors and the explicit collision loss, the avoiding set has the desired
count. -/
theorem le_card_avoiding_filter_of_add_loss_le
    {A T : Finset ℕ} {x q N : ℕ}
    (hA : ∀ p ∈ A, p ≤ x) (hq : q.Prime)
    (hT : ∀ t ∈ T, t.Prime) (hqT : q ∉ T)
    (hraw : N + ∑ t ∈ T, (x + 1) / (q * t) ≤
      (A.filter fun p ↦ q ∣ p + 1).card) :
    N ≤ ((avoidingShiftedDivisors A T).filter
      fun p ↦ q ∣ p + 1).card := by
  have hupper := card_filter_dvd_le_avoiding_add_loss hA hq hT hqT
  omega

/-- The integral collision loss is dominated by the reciprocal mass of the
forbidden primes.  This is the cast bridge between the elementary finite
union bound above and the weighted prime-chain theorem. -/
theorem cast_collisionLoss_le_harmonic
    {T : Finset ℕ} {x q : ℕ} :
    (((∑ t ∈ T, (x + 1) / (q * t) : ℕ) : ℕ) : ℝ) ≤
      ((x + 1 : ℕ) : ℝ) / (q : ℝ) *
        ∑ t ∈ T, (t : ℝ)⁻¹ := by
  classical
  push_cast
  calc
    (∑ t ∈ T, (((x + 1) / (q * t) : ℕ) : ℝ)) ≤
        ∑ t ∈ T, ((x : ℝ) + 1) / ((q : ℝ) * (t : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using
        (Nat.cast_div_le (α := ℝ) (m := x + 1) (n := q * t))
    _ = ((x : ℝ) + 1) / (q : ℝ) *
        ∑ t ∈ T, (t : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

/-- Real-valued form of the usable-count lower bound.  It is tailored to
consume a prime-chain reciprocal-mass estimate without first rounding that
estimate back to a natural number. -/
theorem le_card_avoiding_filter_of_real_harmonic_loss_le
    {A T : Finset ℕ} {x q N : ℕ}
    (hA : ∀ p ∈ A, p ≤ x) (hq : q.Prime)
    (hT : ∀ t ∈ T, t.Prime) (hqT : q ∉ T)
    (hraw : (N : ℝ) + ((x + 1 : ℕ) : ℝ) / (q : ℝ) *
        ∑ t ∈ T, (t : ℝ)⁻¹ ≤
      (((A.filter fun p ↦ q ∣ p + 1).card : ℕ) : ℝ)) :
    N ≤ ((avoidingShiftedDivisors A T).filter
      fun p ↦ q ∣ p + 1).card := by
  have hloss := cast_collisionLoss_le_harmonic (T := T) (x := x) (q := q)
  have hrawNat : N + ∑ t ∈ T, (x + 1) / (q * t) ≤
      (A.filter fun p ↦ q ∣ p + 1).card := by
    exact_mod_cast (show
      (N : ℝ) + (((∑ t ∈ T, (x + 1) / (q * t) : ℕ) : ℕ) : ℝ) ≤
        (((A.filter fun p ↦ q ∣ p + 1).card : ℕ) : ℝ) from
      (by linarith only [hloss, hraw]))
  exact le_card_avoiding_filter_of_add_loss_le hA hq hT hqT hrawNat

end

end Erdos48
